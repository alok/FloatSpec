#!/usr/bin/env python3
"""Replayable finite differential execution of actual Lean and pinned Rocq definitions.

Run with uv run scripts/flocq_bridge.py --flocq-dir PATH. The reference must be
built with its configured compiler. No algorithm is reimplemented in an adapter:
the adapters only construct inputs and serialize integer/location/Boolean results.
Lean runs both compiled code and kernel reduction; Rocq uses vm_compute.
Agreement is finite testing, not a proof of equivalence.
"""

from __future__ import annotations

import argparse
import ast
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass
import hashlib
import json
import os
from pathlib import Path
import random
import re
import signal
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
LEAN_LOC = [".loc_Exact", ".loc_Inexact .lt", ".loc_Inexact .eq", ".loc_Inexact .gt"]
COQ_LOC = ["loc_Exact", "loc_Inexact Lt", "loc_Inexact Eq", "loc_Inexact Gt"]
OPS = ("power", "div_eucl", "location", "round", "truncate", "div", "plus", "sqrt",
       "formats", "digits", "operations", "format_calc", "overflow", "bits32", "bits64",
       "bit_fields", "order32", "order64", "validity", "nearby", "neighbors", "comparison", "small_ieee",
       "ieee_round", "single_helpers", "single_frexp")
ARITIES = dict(zip(OPS, (2, 2, 3, 3, 5, 6, 6, 4, 3, 2, 5, 8, 4, 1, 1, 6, 2, 2, 5, 6, 6, 10, 15, 8, 9, 6), strict=True))
WIDTHS = dict(zip(OPS, (1, 2, 3, 6, 3, 2, 2, 2, 4, 1, 13, 12, 21, 9, 9, 8, 14, 14, 15, 7, 17, 14, 87, 16, 46, 11), strict=True))
RADIX_OPS = {"truncate", "div", "plus", "sqrt", "digits", "operations", "format_calc"}


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.op not in ARITIES or len(self.args) != ARITIES[self.op]:
            raise ValueError(f"unknown operation or wrong arity: {self.op}")
        if not all(type(n) is int for n in self.args):
            raise ValueError("case arguments must be integers, not source text or Booleans")
        if self.op in RADIX_OPS and self.args[0] < 2:
            raise ValueError("Flocq radix requires beta >= 2")
        loc_index = {"location": 2, "round": 1, "truncate": 3}.get(self.op)
        if loc_index is not None and self.args[loc_index] not in range(4):
            raise ValueError("location encoding must be 0, 1, 2, or 3")
        if self.op == "round" and self.args[0] not in (0, 1):
            raise ValueError("rounding sign must be 0 or 1")
        if self.op == "format_calc" and self.args[7] not in range(4):
            raise ValueError("format selector must be FIX=0, FLX=1, FLT=2, or FTZ=3")
        if self.op == "overflow":
            _, _, mode, sign = self.args
            if mode not in range(5) or sign not in (0, 1):
                raise ValueError("overflow requires mode 0..4 and sign 0..1")
        if self.op == "bit_fields" and self.args[2] not in (0, 1):
            raise ValueError("bit-field sign must be 0 or 1")
        if self.op == "validity" and (self.args[2] not in (0, 1) or self.args[3] <= 0):
            raise ValueError("validity requires sign 0/1 and a positive source mantissa")
        if self.op == "nearby" and (self.args[2] not in range(5) or
                                     self.args[3] not in (0, 1) or self.args[4] <= 0):
            raise ValueError("nearby requires mode 0..4, sign 0/1, and a positive source mantissa")
        if self.op == "neighbors":
            prec, emax, kind, sign, mantissa, _ = self.args
            if not 0 < prec < emax or kind not in range(4) or sign not in (0, 1) or mantissa <= 0:
                raise ValueError("neighbors requires 0 < prec < emax, kind 0..3, sign 0/1, positive mantissa")
        if self.op == "comparison":
            for offset in (2, 6):
                kind, sign, mantissa, _ = self.args[offset:offset+4]
                if kind not in range(4) or sign not in (0, 1) or mantissa <= 0:
                    raise ValueError("comparison requires kind 0..3, sign 0/1, positive source mantissa")
        if self.op == "small_ieee":
            prec, emax, mode = self.args[:3]
            if not 1 < prec < emax or mode not in range(5):
                raise ValueError("small_ieee requires 1 < prec < emax and mode 0..4")
            for offset in (3, 7, 11):
                kind, sign, mantissa, _ = self.args[offset:offset+4]
                if kind not in range(4) or sign not in (0, 1) or mantissa <= 0:
                    raise ValueError("small_ieee requires kind 0..3, sign 0/1, positive source mantissa")
        if self.op == "ieee_round":
            _, _, mode, sign, _, _, location, positive = self.args
            if mode not in range(5) or sign not in (0, 1) or location not in range(4) or positive <= 0:
                raise ValueError("ieee_round requires mode 0..4, sign 0/1, location 0..3, positive round mantissa")
        if self.op == "single_helpers":
            prec, emax, mode, kind, sign, mantissa, _, _, _ = self.args
            if not 0 < prec < emax or mode not in range(5) or kind not in range(4) or sign not in (0, 1) or mantissa <= 0:
                raise ValueError("single_helpers requires 0 < prec < emax, mode 0..4, kind 0..3, sign 0/1, positive source mantissa")
        if self.op == "single_frexp":
            prec, _, kind, sign, mantissa, _ = self.args
            if prec <= 0 or kind not in range(4) or sign not in (0, 1) or mantissa <= 0:
                raise ValueError("single_frexp requires positive precision, kind 0..3, sign 0/1, positive source mantissa")


def small_ieee_raw(value, coq=False):
    kind, sign, mantissa, exponent = value
    s = 'true' if sign else 'false'
    prefix = 'SpecFloat.' if coq else '.'
    return (f'{prefix}S754_zero {s}', f'{prefix}S754_infinity {s}',
            f'{prefix}S754_nan',
            f'{prefix}S754_finite {s} ({mantissa})' + ('%positive' if coq else '') +
            f' ({exponent})')[kind]


def single_frexp_expressions(case: Case) -> tuple[str, str]:
    """The source frexp type has no precision/maximum-exponent separation premise."""
    prec, emax, *raw = case.args
    lean = (f'letI : Prec_gt_0 {prec} := ⟨by decide⟩; '
            f'let raw : StandardFloat := {small_ieee_raw(raw)}; '
            f'let x := BinarySingleNaN.SF2B\' (prec := {prec}) (emax := ({emax})) raw; '
            'let f := BinarySingleNaN.Bfrexp x; '
            'let fraction := binarySingleNaNFloatToStandardFloat f.1; '
            f'[boolean (validBinarySingleNaNStandardFloat (prec := {prec}) (emax := ({emax})) raw)] ++ '
            'standard (binarySingleNaNFloatToStandardFloat x) ++ standard fraction ++ '
            f'[f.2, boolean (validBinarySingleNaNStandardFloat (prec := {prec}) (emax := ({emax})) fraction)]')
    coq = (f'let raw := {small_ieee_raw(raw, True)} in '
           f'let x := @BinarySingleNaN.SF2B\' {prec} ({emax}) raw in '
           f'let f := @BinarySingleNaN.Bfrexp {prec} ({emax}) eq_refl x in '
           f'let fraction := @BinarySingleNaN.B2SF {prec} ({emax}) (fst f) in '
           f'[boolean (SpecFloat.valid_binary {prec} ({emax}) raw)] ++ '
           f'standard (@BinarySingleNaN.B2SF {prec} ({emax}) x) ++ standard fraction ++ '
           f'[snd f; boolean (SpecFloat.valid_binary {prec} ({emax}) fraction)]')
    return lean, coq


def single_frexp_corpus(seed: int, samples: int) -> list[Case]:
    rng, cases = random.Random(seed), []
    for prec in (1, 2, 3, 8, 24, 53):
        for emax in sorted({-3, 0, 1, 2, 3, prec - 1, prec, prec + 1}):
            emin = 3 - emax - prec
            raw = [(kind, sign, 1, 0) for kind in (0, 1) for sign in (0, 1)] + [(2, 0, 1, 0)]
            raw += [(3, sign, m, e) for sign in (0, 1)
                    for m in sorted({1, 1 << (prec - 1), (1 << prec) - 1, 1 << prec})
                    for e in sorted({emin - 1, emin, emin + 1, -prec, 0, emax - prec, emax - prec + 1})]
            raw += [(rng.randrange(4), rng.randrange(2), rng.randint(1, 1 << (prec + 1)),
                     rng.randint(min(emin - 2, -prec - 2), max(emax + 2, 2))) for _ in range(samples)]
            cases.extend(Case('single_frexp', (prec, emax, *value)) for value in raw)
    return list(dict.fromkeys(cases))


def single_helpers_expressions(case: Case) -> tuple[str, str]:
    prec, emax, mode, kind, sign, mantissa, exponent, shift, norm = case.args
    lm = ('.RNE', '.RTZ', '.RTN', '.RTP', '.RNA')[mode]
    cm = ('mode_NE', 'mode_ZR', 'mode_DN', 'mode_UP', 'mode_NA')[mode]
    s = 'true' if sign else 'false'
    lean = (f'letI : Prec_gt_0 {prec} := ⟨by decide⟩; '
            f'letI : Prec_lt_emax {prec} {emax} := ⟨by decide⟩; '
            f'let raw : StandardFloat := {small_ieee_raw((kind, sign, mantissa, exponent))}; '
            f'let x := BinarySingleNaN.SF2B\' (prec := {prec}) (emax := {emax}) raw; '
            'let f := BinarySingleNaN.Bfrexp x; '
            f'[boolean (validBinarySingleNaNStandardFloat (prec := {prec}) (emax := {emax}) raw)]')
    coq = (f'let raw := {small_ieee_raw((kind, sign, mantissa, exponent), True)} in '
           f'let x := @BinarySingleNaN.SF2B\' {prec} {emax} raw in '
           f'let f := @BinarySingleNaN.Bfrexp {prec} {emax} eq_refl x in '
           f'[boolean (SpecFloat.valid_binary {prec} {emax} raw)]')
    lv = ['x', f'BinarySingleNaN.binary_normalize (prec := {prec}) (emax := {emax}) {lm} ({norm}) ({exponent}) {s}',
          f'BinarySingleNaN.Bone (prec := {prec}) (emax := {emax})',
          f'Binary.B2BSN (Binary.Bone (prec := {prec}) (emax := {emax}))',
          f'BinarySingleNaN.Bldexp {lm} x ({shift})', 'f.1',
          "BinarySingleNaN.Bulp' x", "BinarySingleNaN.Bpred_pos' x", "BinarySingleNaN.Bsucc' x"]
    head = f'{prec} {emax} eq_refl eq_refl'
    cv = ['x', f'@BinarySingleNaN.binary_normalize {head} {cm} ({norm}) ({exponent}) {s}',
          f'@BinarySingleNaN.Bone {head}',
          f'@Binary.B2BSN {prec} {emax} (@Binary.Bone {head})',
          f'@BinarySingleNaN.Bldexp {head} {cm} x ({shift})', 'fst f',
          f"@BinarySingleNaN.Bulp' {head} x", f"@BinarySingleNaN.Bpred_pos' {head} x",
          f"@BinarySingleNaN.Bsucc' {head} x"]
    for left, right in zip(lv, cv, strict=True):
        lean += f' ++ standard (binarySingleNaNFloatToStandardFloat ({left}))'
        coq += f' ++ standard (@BinarySingleNaN.B2SF {prec} {emax} ({right}))'
    lean += ' ++ [f.2]'
    coq += ' ++ [snd f]'
    for namespace in ('Binary', 'BinarySingleNaN'):
        lean += (f' ++ (let r := {namespace}.shr_fexp (prec := {prec}) (emax := {emax}) '
                 f'({norm}) ({exponent}) .loc_Exact; '
                 '[r.1.shr_m, boolean r.1.shr_r, boolean r.1.shr_s, r.2])')
        coq += (f' ++ (let r := SpecFloat.shr_fexp {prec} {emax} ({norm}) ({exponent}) '
                'SpecFloat.loc_Exact in [SpecFloat.shr_m (fst r); boolean (SpecFloat.shr_r (fst r)); '
                'boolean (SpecFloat.shr_s (fst r)); snd r])')
    return lean, coq


def single_helpers_corpus(seed: int, samples: int) -> list[Case]:
    rng, cases = random.Random(seed), []
    for prec, emax in ((1, 2), (1, 3), (2, 3), (3, 4), (4, 8), (8, 16), (24, 128), (53, 1024)):
        emin = 3 - emax - prec
        raw = [(kind, sign, 1, 0) for kind in (0, 1, 2) for sign in (0, 1)]
        raw += [(3, sign, m, e) for sign in (0, 1) for m, e in
                ((1, emin), ((1 << prec) - 1, emin), (1, -prec), (1 << (prec - 1), -prec),
                 ((1 << prec) - 1, emax - prec), (1, emin - 1), (1 << prec, 0),
                 ((1 << prec) - 1, emax - prec + 1))]
        shifts = (-2 * emax, -1, 0, 1, 2 * emax)
        for mode in range(5):
            for index, (kind, sign, m, e) in enumerate(raw):
                norm = 0 if kind == 0 else -m if sign else m
                cases.append(Case('single_helpers', (prec, emax, mode, kind, sign, m, e,
                                                     shifts[index % len(shifts)], norm)))
            for sign in (0, 1):
                for shift in shifts:
                    cases.append(Case('single_helpers', (prec, emax, mode, 3, sign,
                        1 << (prec - 1), 1 - prec, shift, -1 if sign else 1)))
        for _ in range(samples):
            cases.append(Case('single_helpers', (prec, emax, rng.randrange(5), rng.randrange(4),
                rng.randrange(2), rng.randint(1, 1 << (prec + 1)), rng.randint(emin - 2, emax + 2),
                rng.randint(-2 * emax, 2 * emax), rng.randint(-(1 << prec), 1 << prec))))
    return list(dict.fromkeys(cases))


def small_ieee_expressions(case: Case) -> tuple[str, str]:
    p, emax, mode, *words = case.args
    if not 1 < p < emax or mode not in range(5):
        raise ValueError('small full-payload formats require 1 < precision < emax')
    operands = [words[offset:offset+4] for offset in (0, 4, 8)]
    if any(k not in range(4) or s not in (0, 1) or m <= 0 for k, s, m, e in operands):
        raise ValueError('invalid raw constructor')
    lm = ('.RNE', '.RTZ', '.RTN', '.RTP', '.RNA')[mode]
    cm = ('mode_NE', 'mode_ZR', 'mode_DN', 'mode_UP', 'mode_NA')[mode]
    lean = (f'letI : Prec_gt_0 {p} := ⟨by decide⟩; '
            f'letI : Prec_lt_emax {p} {emax} := ⟨by decide⟩; '
            f'let nan : {{ x : binary_float {p} {emax} // Binary.is_nan x = true }} := '
            '⟨.B754_nan false .xH (by norm_num [nan_pl, Zaux.Zlt_bool, '
            'Digits.digits2_pos, Digits.digits2_Pnat, Digits.digits2_Pnat_bitlength_payload, '
            'Zaux.positiveToNat]), rfl⟩; ')
    coq = ''
    for name, operand in zip(('x', 'y', 'z'), operands, strict=True):
        lean += (f'let raw_{name} : StandardFloat := {small_ieee_raw(operand)}; '
                 f'let single_{name} := BinarySingleNaN.SF2B\' '
                 f'(prec := {p}) (emax := {emax}) raw_{name}; '
                 f'let {name} := Binary.BSN2B nan single_{name}; ')
        coq += (f'let raw_{name} := {small_ieee_raw(operand, True)} in '
                f'let {name} := @BinarySingleNaN.SF2B\' {p} {emax} raw_{name} in ')
    lean += '[' + ', '.join(f'boolean (validBinarySingleNaNStandardFloat '
                            f'(prec := {p}) (emax := {emax}) raw_{n})' for n in ('x','y','z')) + ']'
    coq += '[' + '; '.join(f'boolean (SpecFloat.valid_binary {p} {emax} raw_{n})'
                           for n in ('x','y','z')) + ']'
    values_l, values_c = ['x', 'y', 'z'], ['x', 'y', 'z']
    for name in ('Bplus', 'Bminus', 'Bmult', 'Bdiv', 'Bsqrt', 'Bfma'):
        arity = 1 if name == 'Bsqrt' else 3 if name == 'Bfma' else 2
        args = ' '.join(('x','y','z')[:arity])
        handler = '(fun ' + ' '.join('_' for _ in range(arity)) + ' => nan)'
        values_l.append(f'Binary.{name} {handler} {lm} {args}')
        values_c.append(f'@BinarySingleNaN.{name} {p} {emax} '
                        f'(ltac:(compute; reflexivity)) (ltac:(compute; reflexivity)) {cm} {args}')
    for lvalue, cvalue in zip(values_l, values_c, strict=True):
        lean += f' ++ standard (binarySingleNaNFloatToStandardFloat (Binary.B2BSN ({lvalue})))'
        coq += f' ++ standard (@BinarySingleNaN.B2SF {p} {emax} ({cvalue}))'
    # Observe each public SingleNaN entry point itself, not only the full-payload
    # implementation. The source-mode facade has a distinct rounding-mode type.
    for namespace, lean_mode in (('BinarySingleNaN', lm),
                                 ('FloatSpec.IEEE754.BinarySingleNaN.Source', f'.{cm}')):
        for name, cvalue in zip(('Bplus', 'Bminus', 'Bmult', 'Bdiv', 'Bsqrt', 'Bfma'),
                                values_c[3:], strict=True):
            arity = 1 if name == 'Bsqrt' else 3 if name == 'Bfma' else 2
            args = ' '.join(f'single_{n}' for n in ('x', 'y', 'z')[:arity])
            lean += (f' ++ standard (binarySingleNaNFloatToStandardFloat '
                     f'({namespace}.{name} {lean_mode} {args}))')
            coq += f' ++ standard (@BinarySingleNaN.B2SF {p} {emax} ({cvalue}))'
    return lean, coq


def small_ieee_corpus(seed: int, samples: int) -> list[Case]:
    rng, cases = random.Random(seed), []
    for p in (2, 3, 4, 8):
        for emax in (p + 1, 2*p + 1):
            emin = 3-emax-p
            poszero, negzero = (0, 0, 1, 0), (0, 1, 1, 0)
            posinf, neginf, nan = (1, 0, 1, 0), (1, 1, 1, 0), (2, 0, 1, 0)
            tiny = (3, 0, 1, emin)
            one = (3, 0, 1 << (p-1), 1-p)
            negone = (3, 1, 1 << (p-1), 1-p)
            maximum = (3, 0, (1 << p)-1, emax-p)
            normal = (3, 0, 1 << (p-1), emin)
            subnormal = (3, 0, (1 << (p-1))-1, emin)
            invalid = (3, 0, 1, emax+1)
            values = [poszero, negzero, posinf, neginf, nan, tiny, one, negone,
                      maximum, normal, subnormal, invalid]
            # Every pair of exceptional/normal/subnormal/boundary operands;
            # FMA's addend rotates over the same independently defined pool.
            triples = [(x, y, values[(row*7 + col*3) % len(values)])
                       for row, x in enumerate(values) for col, y in enumerate(values)]
            for mode in range(5):
                for x, y, z in triples:
                    cases.append(Case('small_ieee', (p, emax, mode, *x, *y, *z)))
                for _ in range(samples):
                    operands = []
                    for _ in range(3):
                        kind = rng.choice((0, 1, 2, 3, 3, 3, 3))
                        operands.extend((kind, rng.randrange(2), rng.randint(1, (1 << p)-1),
                                         rng.randint(emin, emax-p)))
                    cases.append(Case('small_ieee', (p, emax, mode, *operands)))
    return list(dict.fromkeys(cases))


def comparison_corpus(seed: int, samples: int) -> list[Case]:
    """Canonical comparison includes degenerate formats, without extra premises."""
    cases: list[Case] = []
    rng = random.Random(seed)
    for p, emax in ((-1, 1), (0, 1), (1, 1), (1, 2), (2, 3), (3, 4), (4, 9), (8, 9), (24, 128), (53, 1024)):
        emin = 3 - emax - p
        values = [(0, 0, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (1, 1, 1, 0), (2, 0, 1, 0)]
        for s in (0, 1):
            values.extend([(3, s, 1, emin), (3, s, 1, 0),
                           (3, s, 1 << max(0, p-1), emin),
                           (3, s, (1 << max(1, p))-1, emax-p)])
        for x in values:
            for y in values:
                cases.append(Case('comparison', (p, emax, *x, *y)))
        for _ in range(samples):
            operands = []
            for _ in range(2):
                operands.extend((rng.randrange(4), rng.randrange(2), rng.randint(1, 1 << max(1, p)),
                                 rng.randint(emin-1, emax+1)))
            cases.append(Case('comparison', (p, emax, *operands)))
    return list(dict.fromkeys(cases))



def ieee_round_corpus(seed: int, samples: int) -> list[Case]:
    """Total raw rounding functions, including inputs outside value-theorem premises."""
    cases: list[Case] = []
    rng = random.Random(seed)
    for p, emax in ((-1, 1), (0, 1), (1, 1), (1, 2), (3, 3), (3, 4), (4, 9), (24, 128), (53, 1024)):
        emin = 3 - emax - p
        cut = 1 << max(1, p)
        boundary = [(-2, emin-1), (-1, 0), (0, emin), (0, 0),
                    (1, emin-1), (1, emin), (1, 0),
                    (cut-1, emin), (cut, emin), (cut+1, emin),
                    (cut-1, -p), (cut, -p), (cut+1, -p),
                    (cut-1, emax-p), (cut, emax-p), (cut+1, emax-p+1)]
        for mode in range(5):
            for sign in range(2):
                for loc in range(4):
                    for mantissa, exponent in boundary:
                        cases.append(Case("ieee_round", (p, emax, mode, sign, mantissa,
                                                         exponent, loc, max(1, abs(mantissa)))))
        for _ in range(samples):
            cases.append(Case("ieee_round", (p, emax, rng.randrange(5), rng.randrange(2),
                                             rng.randint(-2*cut, 2*cut),
                                             rng.randint(min(emin, emax)-2, max(emin, emax)+2),
                                             rng.randrange(4), rng.randint(1, 2*cut))))
    return list(dict.fromkeys(cases))


def corpus(seed: int, samples: int) -> list[Case]:
    """Small exhaustive boundary grids plus independent seeded samples per API."""
    cases: list[Case] = []
    for base in (-3, -2, -1, 0, 1, 2, 3, 10):
        for exponent in range(-3, 7):
            cases.append(Case("power", (base, exponent)))
    for numerator in range(-16, 17):
        for denominator in range(-8, 9):
            cases.append(Case("div_eucl", (numerator, denominator)))
    for steps in range(-2, 11):
        for index in range(-2, 13):
            for loc in range(4):
                cases.append(Case("location", (steps, index, loc)))
    for sign in range(2):
        for loc in range(4):
            for mantissa in (-2, -1, 0, 1, 2):
                cases.append(Case("round", (sign, loc, mantissa)))
    # Deliberately include zero, negative mantissas/divisors, negative shifts,
    # and exponent boundaries. These are total-function comparisons, not a
    # claim that the corresponding real-number correctness preconditions hold.
    for base in (2, 3, 10):
        for mantissa in (-9, -1, 0, 1, 2, 3, 4, 8, 9, 16, 17):
            for shift in (-2, -1, 0, 1, 2):
                cases.append(Case("sqrt", (base, mantissa, shift, 0)))
                for loc in range(4):
                    cases.append(Case("truncate", (base, mantissa, -1, loc, shift)))
            for divisor in (-3, -1, 0, 1, 2, 3):
                for exponent in (-1, 0, 1):
                    cases.append(Case("div", (base, mantissa, 0, divisor, 0, exponent)))
                    cases.append(Case("plus", (base, mantissa, 0, divisor, 0, exponent)))
    for emin in (-4, -1, 0, 2):
        for prec in (-1, 0, 1, 2, 5):
            for exponent in range(-6, 8):
                cases.append(Case("formats", (emin, prec, exponent)))
    for base in (2, 3, 10, 16):
        for mantissa in (-257, -16, -1, 0, 1, 2, 3, 9, 10, 15, 16, 17, 255, 256, 257):
            cases.append(Case("digits", (base, mantissa)))
        for left in (-16, -1, 0, 1, 16):
            for right in (-3, -1, 0, 1, 3):
                for exponent in (-1, 0, 1):
                    cases.append(Case("operations", (base, left, exponent, right, -exponent)))
                    for fmt in range(4):
                        cases.append(Case("format_calc", (base, left, exponent, right,
                                                          -exponent, -2, 3, fmt)))
    for mw in (-3, -1, 0, 1, 2, 8, 23, 52):
        for ew in (-2, -1, 0, 1, 2, 8, 11):
            for sign in (0, 1):
                for mantissa, exponent, word in ((0, 0, 0), (-3, -2, -1), (7, 5, 257)):
                    cases.append(Case("bit_fields", (mw, ew, sign, mantissa, exponent, word)))
    rng = random.Random(seed)
    # Raw validation and total conversion exist even when precision/exponent
    # parameters violate the hypotheses of subsequent arithmetic theorems.
    for prec in (-1, 0, 1, 3, 5):
        for emax in (1, 4, 8):
            for sign in (0, 1):
                for mantissa in (1, 3, 4, 7, 8, 16):
                    for exponent in (-5, -4, -2, 0, 1, 4):
                        cases.append(Case("validity", (prec, emax, sign, mantissa, exponent)))
    for width, fraction_width, exponent_width in ((32, 23, 8), (64, 52, 11)):
        inf = ((1 << exponent_width) - 1) << fraction_width
        one = ((1 << (exponent_width - 1)) - 1) << fraction_width
        order_words = [sign | word for sign in (0, 1 << (width - 1)) for word in
                       (0, 1, (1 << fraction_width) - 1, 1 << fraction_width,
                        one - 1, one, one + 1, inf - 1, inf, inf + 1,
                        inf + (1 << (fraction_width - 1)))]
        cases.extend(Case(f"order{width}", (left, right))
                     for left in order_words for right in order_words)
        cases.extend(Case(f"order{width}", pair) for pair in
                     ((-1, 0), (1 << width, 1 << (width - 1)), (-(1 << width), 0)))
        for sign in (0, 1 << (width - 1)):
            for exponent in (0, 1, (1 << (exponent_width - 1)) - 1,
                             (1 << exponent_width) - 2, (1 << exponent_width) - 1):
                for fraction in (0, 1, 2, (1 << (fraction_width - 1)) - 1,
                                 1 << (fraction_width - 1), (1 << fraction_width) - 1):
                    word = sign | (exponent << fraction_width) | fraction
                    cases.append(Case(f"bits{width}", (word,)))
        # The source takes unbounded Z, not a machine word. Its sign test is
        # a threshold comparison, so outside-domain behavior is not wrapping.
        for word in (-(1 << (width + 2)), -(1 << width), -2, -1,
                     1 << width, (1 << width) + 1, (1 << (width + 2)) - 1):
            cases.append(Case(f"bits{width}", (word,)))
    for prec in (-3, -1, 0, 1, 2, 3, 24, 53):
        for emax in sorted({-4, 0, 1, prec, prec + 1, 2 * prec, 128, 1024}):
            for mode in range(5):
                for sign in range(2):
                    cases.append(Case("overflow", (prec, emax, mode, sign)))
    # Raw source helpers have no precision premise; include values outside
    # later arithmetic theorem domains and observe actual input/output validity.
    for prec in (-1, 0, 1, 3, 24, 53):
        for mode in range(5):
            for sign in (0, 1):
                for mantissa in sorted({1, 2, 3, 4, 5, 7, 8, 15, (1 << max(1, prec)) - 1}):
                    for exponent in sorted({-prec - 2, -prec - 1, -prec, -1, 0, 1, 2}):
                        cases.append(Case("nearby", (prec, max(4, prec + 1), mode, sign,
                                                     mantissa, exponent)))
    # Observe validity before total conversion so rejected finite inputs do
    # not silently disappear into the NaN control cases.
    for prec in (1, 2, 3, 4, 24, 53):
        for emax in sorted({prec + 1, 2 * prec + 1}):
            for sign in (0, 1):
                cases.extend(Case("neighbors", (prec, emax, kind, sign, 1, 0)) for kind in (0, 1, 2))
                for mantissa in sorted({1, 2, 3, 1 << (prec - 1), (1 << prec) - 1, 1 << prec}):
                    for exponent in sorted({2-emax-prec, 3-emax-prec, 4-emax-prec, -prec, 0,
                                            emax-prec-1, emax-prec, emax-prec+1}):
                        cases.append(Case("neighbors", (prec, emax, 3, sign, mantissa, exponent)))
    cases.extend(comparison_corpus(seed, samples))
    cases.extend(small_ieee_corpus(seed, samples))
    cases.extend(ieee_round_corpus(seed, samples))
    cases.extend(single_helpers_corpus(seed, samples))
    cases.extend(single_frexp_corpus(seed, samples))
    for op in OPS:
        if op in ("comparison", "small_ieee", "ieee_round", "single_helpers", "single_frexp"):
            continue
        for _ in range(samples):
            base = rng.choice((2, 3, 10, 16))
            m1, m2 = (rng.randint(-1024, 1024) for _ in range(2))
            e1, e2, target = (rng.randint(-3, 3) for _ in range(3))
            loc = rng.randrange(4)
            if op == "power":
                args = (rng.randint(-16, 16), rng.randint(-4, 8))
            elif op == "div_eucl":
                args = (m1, m2)
            elif op == "location":
                args = (rng.randint(-16, 128), rng.randint(-16, 128), loc)
            elif op == "round":
                args = (rng.randrange(2), loc, m1)
            elif op == "truncate":
                args = (base, m1, e1, loc, target)
            elif op in ("div", "plus"):
                args = (base, m1, e1, m2, e2, target)
            elif op == "sqrt":
                args = (base, m1, e1, target)
            elif op == "formats":
                args = (e1, rng.randint(-1, 8), e2)
            elif op == "digits":
                args = (base, m1)
            elif op == "operations":
                args = (base, m1, e1, m2, e2)
            elif op == "overflow":
                args = (rng.randint(-16, 64), rng.randint(-32, 2048), rng.randrange(5), rng.randrange(2))
            elif op in ("bits32", "bits64"):
                width = int(op[4:])
                args = (rng.randrange(-(1 << width), 1 << (width + 1)),)
            elif op == "bit_fields":
                args = (rng.randint(-8, 64), rng.randint(-8, 16), rng.randrange(2),
                        m1, m2, rng.randrange(-(1 << 65), 1 << 65))
            elif op in ("order32", "order64"):
                width = int(op[5:])
                left = rng.getrandbits(width)
                right = rng.choice((rng.getrandbits(width), left,
                                    (left + 1) % (1 << width), left ^ (1 << (width - 1))))
                args = (left, right)
            elif op == "validity":
                args = (rng.randint(-2, 12), rng.randint(-2, 16), rng.randrange(2),
                        rng.randint(1, 1 << 14), rng.randint(-32, 20))
            elif op == "nearby":
                args = (rng.randint(-2, 64), rng.randint(-2, 128), rng.randrange(5),
                        rng.randrange(2), rng.randint(1, 1 << 54), rng.randint(-120, 120))
            elif op == "neighbors":
                prec = rng.choice((1, 2, 3, 4, 8, 24, 53))
                emax = rng.choice((prec + 1, 2 * prec + 1, 128, 1024))
                exponent = rng.choice((2-emax-prec, 3-emax-prec, 4-emax-prec, -prec, 0,
                                       emax-prec, emax-prec+1))
                mantissa = rng.randint(1, (1 << (prec + 1)) - 1)
                args = (prec, emax, rng.choice((0, 1, 2, 3, 3, 3)), rng.randrange(2), mantissa, exponent)
            else:
                args = (base, m1, e1, m2, e2, target, rng.randint(1, 5), rng.randrange(4))
            cases.append(Case(op, args))
    return list(dict.fromkeys(cases))


def expressions(case: Case) -> tuple[str, str]:
    """Translate inputs only; all arithmetic is performed by imported APIs."""
    a = [f"({n})" for n in case.args]
    op = case.op
    if op == "ieee_round":
        p, emax, mode, sign, mantissa, exponent, loc, positive = case.args
        lm = ('.RNE', '.RTZ', '.RTN', '.RTP', '.RNA')[mode]
        cm = ('mode_NE', 'mode_ZR', 'mode_DN', 'mode_UP', 'mode_NA')[mode]
        s = 'true' if sign else 'false'
        lean, rocq = [], []
        for name, serialize in (("BinarySingleNaN", "standard"), ("Binary", "full")):
            lean.append(f'{serialize} ({name}.binary_round_aux (prec := ({p})) (emax := ({emax})) '
                        f'{lm} {s} ({mantissa}) ({exponent}) ({LEAN_LOC[loc]}))')
            rocq.append(f'{serialize} (@{name}.binary_round_aux ({p}) ({emax}) '
                        f'{cm} {s} ({mantissa}) ({exponent}) ({COQ_LOC[loc]}))')
        for name, serialize in (("BinarySingleNaN", "standard"), ("Binary", "full")):
            lean.append(f'{serialize} ({name}.binary_round (prec := ({p})) (emax := ({emax})) '
                        f'{lm} {s} (binaryPositiveOfNat {positive} (by decide)) ({exponent}))')
            rocq.append(f'{serialize} (@{name}.binary_round ({p}) ({emax}) '
                        f'{cm} {s} ({positive})%positive ({exponent}))')
        return ' ++ '.join(lean), ' ++ '.join(rocq)
    if op == "small_ieee":
        return small_ieee_expressions(case)
    if op == "single_helpers":
        return single_helpers_expressions(case)
    if op == "single_frexp":
        return single_frexp_expressions(case)
    if op == "comparison":
        p, emax, *words = case.args
        operands = [words[:4], words[4:]]
        if any(k not in range(4) or s not in (0, 1) or m <= 0 for k, s, m, e in operands):
            raise ValueError('invalid raw constructor')
        lean, rocq = '', ''
        for name, (kind, sign, mantissa, exponent) in zip(('x', 'y'), operands, strict=True):
            s = 'true' if sign else 'false'
            lr = (f'.S754_zero {s}', f'.S754_infinity {s}', '.S754_nan',
                  f'.S754_finite {s} ({mantissa}) ({exponent})')[kind]
            cr = (f'SpecFloat.S754_zero {s}', f'SpecFloat.S754_infinity {s}', 'SpecFloat.S754_nan',
                  f'SpecFloat.S754_finite {s} ({mantissa})%positive ({exponent})')[kind]
            lean += (f'let raw_{name} : StandardFloat := {lr}; '
                     f"let {name} := BinarySingleNaN.SF2B' (prec := ({p})) (emax := ({emax})) raw_{name}; ")
            rocq += (f'let raw_{name} := {cr} in '
                     f"let {name} := @BinarySingleNaN.SF2B' ({p}) ({emax}) raw_{name} in ")
        lean += '[' + ', '.join(f'boolean (validBinarySingleNaNStandardFloat '
                                f'(prec := ({p})) (emax := ({emax})) raw_{name})' for name in ('x', 'y')) + ']'
        rocq += '[' + '; '.join(f'boolean (SpecFloat.valid_binary ({p}) ({emax}) raw_{name})'
                               for name in ('x', 'y')) + ']'
        for name in ('x', 'y'):
            lean += f' ++ standard (BinarySingleNaN.B2SF {name})'
            rocq += f' ++ standard (@BinarySingleNaN.B2SF ({p}) ({emax}) {name})'
        lean += ' ++ [((BinarySingleNaN.Bcompare x y).map comparisonCode).getD 2]'
        rocq += f' ++ [comparison_code (@BinarySingleNaN.Bcompare ({p}) ({emax}) x y)]'
        for name in ('Beqb', 'Bltb', 'Bleb'):
            lean += f' ++ [boolean (BinarySingleNaN.{name} x y)]'
            rocq += f' ++ [boolean (@BinarySingleNaN.{name} ({p}) ({emax}) x y)]'
        return lean, rocq
    if op == "neighbors":
        prec, emax, kind, sign, mantissa, exponent = case.args
        p, e, n = f"({prec})", f"({exponent})", f"({mantissa})"
        s = "true" if sign else "false"
        lean_input = (f".S754_zero {s}", f".S754_infinity {s}", ".S754_nan",
                      f".S754_finite {s} {n} {e}")[kind]
        coq_input = (f"SpecFloat.S754_zero {s}", f"SpecFloat.S754_infinity {s}", "SpecFloat.S754_nan",
                     f"SpecFloat.S754_finite {s} {n}%positive {e}")[kind]
        lean = (f"letI : Prec_gt_0 {p} := ⟨by decide⟩; "
                f"letI : Prec_lt_emax {p} {emax} := ⟨by decide⟩; "
                f"let raw : StandardFloat := {lean_input}; "
                f"let x := BinarySingleNaN.SF2B' (prec := {p}) (emax := {emax}) raw; "
                f"[boolean (validBinarySingleNaNStandardFloat (prec := {p}) (emax := {emax}) raw)] ++ "
                "standard (BinarySingleNaN.B2SF x)")
        rocq = (f"let raw := {coq_input} in let x := @BinarySingleNaN.SF2B' {p} {emax} raw in "
                f"[boolean (SpecFloat.valid_binary {p} {emax} raw)] ++ "
                f"standard (@BinarySingleNaN.B2SF {p} {emax} x)")
        for name in ("Bsucc", "Bpred", "Bulp"):
            lean += f" ++ standard (BinarySingleNaN.B2SF (BinarySingleNaN.{name} x))"
            rocq += (f" ++ standard (@BinarySingleNaN.B2SF {p} {emax} "
                     f"(@BinarySingleNaN.{name} {p} {emax} "
                     "(ltac:(compute; reflexivity)) (ltac:(compute; reflexivity)) x))")
        return lean, rocq
    if op == "nearby":
        prec, emax, mode, sign, mantissa, exponent = case.args
        lm = (".RNE", ".RTZ", ".RTN", ".RTP", ".RNA")[mode]
        cm = ("mode_NE", "mode_ZR", "mode_DN", "mode_UP", "mode_NA")[mode]
        s = "true" if sign else "false"
        p, e, n = f"({prec})", f"({exponent})", f"({mantissa})"
        emax = f"({emax})"
        lean = (f"let x := StandardFloat.S754_finite {s} {n} {e}; "
                f"let y := SFnearbyint_binary (prec := {p}) (emax := {emax}) {lm} {s} {n} {e}; "
                f"[SFnearbyint_binary_aux (prec := {p}) {lm} {s} {n} {e}] ++ standard y ++ "
                f"[boolean (validBinarySingleNaNStandardFloat (prec := {p}) (emax := {emax}) x), "
                f"boolean (validBinarySingleNaNStandardFloat (prec := {p}) (emax := {emax}) y)]")
        rocq = (f"let x := SpecFloat.S754_finite {s} {n}%positive {e} in "
                f"let y := BinarySingleNaN.SFnearbyint_binary {p} {emax} {cm} {s} {n}%positive {e} in "
                f"[BinarySingleNaN.SFnearbyint_binary_aux {p} {cm} {s} {n}%positive {e}] ++ standard y ++ "
                f"[boolean (SpecFloat.valid_binary {p} {emax} x); "
                f"boolean (SpecFloat.valid_binary {p} {emax} y)]")
        return lean, rocq
    if op == "validity":
        prec, emax, _, mantissa, exponent = a
        sign = "true" if case.args[2] else "false"
        lean = f"let x := StandardFloat.S754_finite {sign} {mantissa} {exponent}; "
        lean += (f"[boolean (validBinarySingleNaNStandardFloat (prec := {prec}) (emax := {emax}) x), "
                 f"boolean (rawValidity {prec} {emax} {sign} {mantissa} {exponent})] ++ "
                 f"standard (B2SF_BSN (_root_.SF2B' (prec := {prec}) (emax := {emax}) x)) ++ "
                 f"standard (BinarySingleNaN.B2SF (BinarySingleNaN.SF2B' "
                 f"(prec := {prec}) (emax := {emax}) x)) ++ "
                 f"standard (B2SF_BSN (SF2BSpec' (prec := {prec}) (emax := {emax}) x)) ++ "
                 f"[boolean (valid_binary_SF (prec := {prec}) (emax := {emax}) x)]")
        rocq = f"let x := SpecFloat.S754_finite {sign} {mantissa}%positive {exponent} in "
        rocq += (f"let valid := boolean (SpecFloat.valid_binary {prec} {emax} x) in "
                 f"let converted := standard (@BinarySingleNaN.B2SF {prec} {emax} "
                 f"(@BinarySingleNaN.SF2B' {prec} {emax} x)) in "
                 "[valid; valid] ++ converted ++ converted ++ converted ++ [valid]")
        return lean, rocq
    if op in ("bits32", "bits64"):
        width = op[4:]
        return (f"FloatSpec.Test.BitsExecution.observation{width} {a[0]}",
                f"observation{width} {a[0]}")
    if op == "bit_fields":
        mw, ew, _, mantissa, exponent, word = a
        sign = "true" if case.args[2] else "false"
        args = f"{mw} {ew} {sign} {mantissa} {exponent} {word}"
        return f"bitFields {args}", f"bit_fields {args}"
    if op in ("order32", "order64"):
        width = op[5:]
        lean = f"let x := b{width}_of_bits {a[0]}; let y := b{width}_of_bits {a[1]}; "
        rocq = f"let x := Bits.b{width}_of_bits {a[0]} in let y := Bits.b{width}_of_bits {a[1]} in "
        lean_columns = [f"bits_of_b{width} x", f"bits_of_b{width} y",
                        f"((b{width}_compare x y).map comparisonCode).getD 2",
                        f"((b{width}_compare y x).map comparisonCode).getD 2"]
        coq_columns = [f"Bits.bits_of_b{width} x", f"Bits.bits_of_b{width} y",
                       f"comparison_code (Bits.b{width}_compare x y)",
                       f"comparison_code (Bits.b{width}_compare y x)"]
        for name in ("opp", "abs", "erase", "pred", "succ"):
            lean_columns.append(f"bits_of_b{width} (b{width}_{name} x)")
            coq_columns.append(f"Bits.bits_of_b{width} (Bits.b{width}_{name} x)")
        prec, emax = (24, 128) if width == "32" else (53, 1024)
        lean = (f"letI : Prec_gt_0 {prec} := ⟨by decide⟩; "
                f"letI : Prec_lt_emax {prec} {emax} := ⟨by decide⟩; " + lean)
        for name in ("Bpred", "Bsucc", "Bulp"):
            lean_columns.append(f"bits_of_b{width} (Binary.{name} x)")
            coq_columns.append(f"Bits.bits_of_b{width} (@Binary.{name} {prec} {emax} "
                               "(ltac:(compute; reflexivity)) (ltac:(compute; reflexivity)) x)")
        lean_columns.extend(["((Binary.Bcompare x y).map comparisonCode).getD 2",
                             "((BinarySingleNaN.Bcompare (Binary.B2BSN x) (Binary.B2BSN y)).map comparisonCode).getD 2"])
        coq_columns.extend([f"comparison_code (@Binary.Bcompare {prec} {emax} x y)",
                            f"comparison_code (@BinarySingleNaN.Bcompare {prec} {emax} "
                            f"(@Binary.B2BSN {prec} {emax} x) (@Binary.B2BSN {prec} {emax} y))"])
        return lean + "[" + ", ".join(lean_columns) + "]", rocq + "[" + "; ".join(coq_columns) + "]"
    if op == "power":
        return (f"[Zaux.Zpower {a[0]} {a[1]}]", f"[Zpower {a[0]} {a[1]}]")
    if op == "div_eucl":
        return (f"pair (Zaux.Z_div_eucl {a[0]} {a[1]})",
                f"pair (Z.div_eucl {a[0]} {a[1]})")
    if op == "overflow":
        prec, emax, mode, sign = case.args
        lean_mode = (".RNE", ".RTZ", ".RTN", ".RTP", ".RNA")[mode]
        coq_mode = ("mode_NE", "mode_ZR", "mode_DN", "mode_UP", "mode_NA")[mode]
        s = "true" if sign else "false"
        p, top = f"({prec})", f"({emax})"
        lean = f"BinarySingleNaN.binary_overflow (prec := {p}) (emax := {top}) {lean_mode} {s}"
        coq = f"BinarySingleNaN.binary_overflow {p} {top} {coq_mode} {s}"
        coq_full = f"@Binary.binary_overflow {p} {top} {coq_mode} {s}"
        return (f"let x := {lean}; standard x ++ "
                f"[boolean (validBinarySingleNaNStandardFloat (prec := {p}) (emax := {top}) x)] ++ "
                f"standard (standard_binary_overflow {p} {top} {lean_mode} {s}) ++ "
                f"standard (FF2SF (Binary.binary_overflow (prec := {p}) (emax := {top}) {lean_mode} {s})) ++ "
                f"full (Binary.binary_overflow_exact (prec := {p}) (emax := {top}) {lean_mode} {s}) ++ "
                f"standard (FF2SF (_root_.binary_overflow {p} {top} {lean_mode} {s}))",
                f"let x := {coq} in standard x ++ [boolean (SpecFloat.valid_binary {p} {top} x)] ++ "
                f"standard x ++ standard (Binary.FF2SF ({coq_full})) ++ full ({coq_full}) ++ "
                f"standard (Binary.FF2SF ({coq_full}))")
    if op == "formats":
        emin, prec, exponent = a
        return (f"[FIX.FIX_exp {emin} {exponent}, FLX.FLX_exp {prec} {exponent}, "
                f"FLT.FLT_exp {prec} {emin} {exponent}, FTZ.FTZ_exp {prec} {emin} {exponent}]",
                f"[FIX_exp {emin} {exponent}; FLX_exp {prec} {exponent}; "
                f"FLT_exp {emin} {prec} {exponent}; FTZ_exp {emin} {prec} {exponent}]")
    if op == "digits":
        return (f"[Digits.Zdigits {a[0]} {a[1]}]",
                f"[Zdigits (Build_radix {a[0]} eq_refl) {a[1]}]")
    if op == "location":
        loc_l, loc_c = LEAN_LOC[case.args[2]], COQ_LOC[case.args[2]]
        names = ("new_location_even", "new_location_odd", "new_location")
        return ("[" + ", ".join(f"location ({n} {a[0]} {a[1]} ({loc_l}))" for n in names) + "]",
                "[" + "; ".join(f"location ({n} {a[0]} {a[1]} ({loc_c}))" for n in names) + "]")
    if op == "round":
        sign = "true" if case.args[0] else "false"
        loc_l, loc_c = LEAN_LOC[case.args[1]], COQ_LOC[case.args[1]]
        calls = ("round_UP {loc}", f"round_sign_DN {sign} {{loc}}",
                 f"round_sign_UP {sign} {{loc}}", f"round_ZR {sign} {{loc}}",
                 f"round_N {sign} {{loc}}")
        lean = [f"boolean (Round.{call.format(loc=f'({loc_l})')})" for call in calls]
        coq = [f"boolean (Round.{call.format(loc=f'({loc_c})')})" for call in calls]
        lean.append(f"Round.cond_incr {sign} {a[2]}")
        coq.append(f"Round.cond_incr {sign} {a[2]}")
        return "[" + ", ".join(lean) + "]", "[" + "; ".join(coq) + "]"
    base_l, base_c = a[0], f"(Build_radix {a[0]} eq_refl)"
    if op in ("operations", "format_calc"):
        x_l, y_l = f"⟨{a[1]}, {a[2]}⟩", f"⟨{a[3]}, {a[4]}⟩"
        x_c, y_c = f"(Float {base_c} {a[1]} {a[2]})", f"(Float {base_c} {a[3]} {a[4]})"
        if op == "operations":
            lean = [f"alignment (Operations.Falign {base_l} {x_l} {y_l})"]
            coq = [f"alignment (Operations.Falign {x_c} {y_c})"]
            for name in ("Fopp", "Fabs", "Fplus", "Fminus", "Fmult"):
                lean.append(f"floating (Operations.{name} {base_l} {x_l}" +
                            (f" {y_l})" if name in ("Fplus", "Fminus", "Fmult") else ")"))
                coq.append(f"floating (Operations.{name} {x_c}" +
                           (f" {y_c})" if name in ("Fplus", "Fminus", "Fmult") else ")"))
            return " ++ ".join(lean), " ++ ".join(coq)
        emin, prec, fmt = a[5], a[6], case.args[7]
        f_l = (f"FIX.FIX_exp {emin}", f"FLX.FLX_exp {prec}",
               f"FLT.FLT_exp {prec} {emin}", f"FTZ.FTZ_exp {prec} {emin}")[fmt]
        f_c = (f"FIX_exp {emin}", f"FLX_exp {prec}",
               f"FLT_exp {emin} {prec}", f"FTZ_exp {emin} {prec}")[fmt]
        lean = [f"triple (Plus.Fplus {base_l} ({f_l}) {x_l} {y_l})",
                f"triple (Div.Fdiv {base_l} ({f_l}) {x_l} {y_l})",
                f"triple (Sqrt.Fsqrt {base_l} ({f_l}) {x_l})",
                f"triple (Round.truncate {base_l} ({f_l}) ({a[1]}, {a[2]}, .loc_Exact))"]
        coq = [f"triple (Plus.Fplus {base_c} ({f_c}) {x_c} {y_c})",
               f"triple (Div.Fdiv ({f_c}) {x_c} {y_c})",
               f"triple (Sqrt.Fsqrt ({f_c}) {x_c})",
               f"triple (Round.truncate {base_c} ({f_c}) ({a[1]}, {a[2]}, loc_Exact))"]
        return " ++ ".join(lean), " ++ ".join(coq)
    if op == "truncate":
        loc_l, loc_c = LEAN_LOC[case.args[3]], COQ_LOC[case.args[3]]
        return (f"triple (Round.truncate_aux {base_l} ({a[1]}, {a[2]}, {loc_l}) {a[4]})",
                f"triple (Round.truncate_aux {base_c} ({a[1]}, {a[2]}, {loc_c}) {a[4]})")
    name = {"div": "Div.Fdiv_core", "plus": "Plus.Fplus_core", "sqrt": "Sqrt.Fsqrt_core"}[op]
    args = " ".join(a[1:])
    return f"located ({name} {base_l} {args})", f"located ({name} {base_c} {args})"


LEAN_HEADER = """import FloatSpec.src.Calc.Plus
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Sqrt
import FloatSpec.src.Core.FTZ
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
import FloatSpec.src.IEEE754.BitsSourceFacade
import FloatSpec.Test.BitsExecution
open FloatSpec.Core FloatSpec.Calc FloatSpec.Calc.Bracket
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 5000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
namespace Bridge
private def comparisonCode : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1
private def location : Location → Int
  | .loc_Exact => 0
  | .loc_Inexact .lt => 1
  | .loc_Inexact .eq => 2
  | .loc_Inexact .gt => 3
private def boolean (b : Bool) : Int := if b then 1 else 0
private def rawValidity (prec emax : Int) (s : Bool) (m : Nat) (e : Int) : Bool :=
  @decide (validB754 prec emax (.B754_finite s m e)) (by unfold validB754; infer_instance)
private def pair (p : Int × Int) : List Int := [p.1, p.2]
private def located (p : Int × Location) : List Int := [p.1, location p.2]
private def triple (p : Int × Int × Location) : List Int := [p.1, p.2.1, location p.2.2]
private def alignment (p : Int × Int × Int) : List Int := [p.1, p.2.1, p.2.2]
private def floating {beta : Int} [ValidRadix beta]
    (x : Defs.FlocqFloat beta) : List Int := [x.Fnum, x.Fexp]
private def standard : StandardFloat → List Int
  | .S754_zero s => [0, boolean s, 0, 0]
  | .S754_infinity s => [1, boolean s, 0, 0]
  | .S754_nan => [2, 0, 0, 0]
  | .S754_finite s m e => [3, boolean s, m, e]
private def full : full_float → List Int
  | .F754_zero s => [0, boolean s, 0, 0]
  | .F754_infinity s => [1, boolean s, 0, 0]
  | .F754_nan s payload => [2, boolean s, Zaux.positiveToNat payload, 0]
  | .F754_finite s m e => [3, boolean s, Zaux.positiveToNat m, e]
private def fields (p : Bool × Int × Int) : List Int := [boolean p.1, p.2.1, p.2.2]
private def bitFields (mw ew : Int) (s : Bool) (m e word : Int) : List Int :=
  let joined := FloatSpec.IEEE754.Bits.Source.join_bits mw ew s m e
  let split := FloatSpec.IEEE754.Bits.Source.split_bits mw ew word
  [joined] ++ fields split ++
    fields (FloatSpec.IEEE754.Bits.Source.split_bits mw ew joined) ++
    [FloatSpec.IEEE754.Bits.Source.join_bits mw ew split.1 split.2.1 split.2.2]
"""

COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import Core.Zaux Core.Defs Core.Digits Core.FIX Core.FLX Core.FLT Core.FTZ
  Calc.Bracket Calc.Operations Calc.Round Calc.Plus Calc.Div Calc.Sqrt IEEE754.BinarySingleNaN
  IEEE754.Bits.
Import ListNotations.
Open Scope Z_scope.
Definition location (l : SpecFloat.location) : Z :=
  match l with
  | SpecFloat.loc_Exact => 0
  | SpecFloat.loc_Inexact Lt => 1
  | SpecFloat.loc_Inexact Eq => 2
  | SpecFloat.loc_Inexact Gt => 3
  end.
Definition boolean (b : bool) : Z := if b then 1 else 0.
Definition comparison_code (c : option comparison) : Z :=
  match c with None => 2 | Some Lt => -1 | Some Eq => 0 | Some Gt => 1 end.
Definition pair (p : Z * Z) : list Z := [fst p; snd p].
Definition located (p : Z * SpecFloat.location) : list Z := [fst p; location (snd p)].
Definition triple (p : Z * Z * SpecFloat.location) : list Z :=
  let '(m, e, l) := p in [m; e; location l].
Definition alignment (p : Z * Z * Z) : list Z := let '(m, n, e) := p in [m; n; e].
Definition floating {beta : radix} (x : float beta) : list Z := [Fnum x; Fexp x].
Definition standard (x : SpecFloat.spec_float) : list Z :=
  match x with
  | SpecFloat.S754_zero s => [0; boolean s; 0; 0]
  | SpecFloat.S754_infinity s => [1; boolean s; 0; 0]
  | SpecFloat.S754_nan => [2; 0; 0; 0]
  | SpecFloat.S754_finite s m e => [3; boolean s; Zpos m; e]
  end.
Definition full (x : Binary.full_float) : list Z :=
  match x with
  | Binary.F754_zero s => [0; boolean s; 0; 0]
  | Binary.F754_infinity s => [1; boolean s; 0; 0]
  | Binary.F754_nan s payload => [2; boolean s; Zpos payload; 0]
  | Binary.F754_finite s m e => [3; boolean s; Zpos m; e]
  end.
Definition observation32 (bits : Z) : list Z :=
  let x := Bits.b32_of_bits bits in
  let '(s, m, e) := Bits.split_bits 23 8 bits in
  let raw := Binary.B2FF 24 128 x in
  full raw ++ [Bits.bits_of_b32 x; boolean s; m; e; boolean (Binary.valid_binary 24 128 raw)].
Definition observation64 (bits : Z) : list Z :=
  let x := Bits.b64_of_bits bits in
  let '(s, m, e) := Bits.split_bits 52 11 bits in
  let raw := Binary.B2FF 53 1024 x in
  full raw ++ [Bits.bits_of_b64 x; boolean s; m; e; boolean (Binary.valid_binary 53 1024 raw)].
Definition fields (p : bool * Z * Z) : list Z :=
  let '(s, m, e) := p in [boolean s; m; e].
Definition bit_fields (mw ew : Z) (s : bool) (m e word : Z) : list Z :=
  let joined := Bits.join_bits mw ew s m e in
  let '(ss, mm, ee) := Bits.split_bits mw ew word in
  [joined] ++ fields (ss, mm, ee) ++ fields (Bits.split_bits mw ew joined) ++
    [Bits.join_bits mw ew ss mm ee].
"""


def parse_result(output: str, language: str, expected_count: int) -> list[list[int]]:
    """Reject malformed/partial output; never accept an empty comparison."""
    if language == "rocq":
        match = re.fullmatch(r"\s*=\s*(.*?)\s*:\s*list\s*\(list Z\)\s*", output, re.S)
        if not match:
            raise ValueError(f"unexpected Rocq output: {output[:500]}")
        output = match[1].replace(";", ",")
    else:
        output = re.sub(r"Int\.ofNat\s+(\d+)", r"\1", output)
        output = re.sub(r"Int\.negSucc\s+(\d+)", lambda m: str(-int(m[1]) - 1), output)
    if not re.fullmatch(r"[\s\[\],\-0-9]+", output):
        raise ValueError(f"unexpected {language} output: {output[:500]}")
    result = ast.literal_eval(output.strip())
    if (not isinstance(result, list) or len(result) != expected_count or
            not all(isinstance(row, list) and row and
                    all(type(n) is int for n in row) for row in result)):
        raise ValueError(f"invalid {language} result shape/count")
    return result


def run(command: list[str], timeout: int = 120) -> str:
    if command[0] == "lake" and os.environ.get("LEAN_TOOLCHAIN_OVERRIDE"):
        command = ["elan", "run", os.environ["LEAN_TOOLCHAIN_OVERRIDE"], *command]
    with subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, start_new_session=(os.name == "posix")) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except BaseException:
            # Lake and its Lean child must stop together. Terminating only the
            # immediate process can leave a prover running after a timeout.
            try:
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
            except ProcessLookupError:
                pass
            process.communicate()
            raise
        if process.returncode:
            raise RuntimeError(f"command failed ({process.returncode}): {command}\n"
                               f"{stdout[:8000]}\n{stderr[:8000]}")
        if stderr.strip():
            raise RuntimeError(f"unexpected stderr from {command}: {stderr[:8000]}")
        return stdout


def configured_coqc(flocq: Path) -> str:
    status = (flocq / "config.status").read_text()
    match = re.search(r'^S\["COQC"\]="([^"]+)"$', status, re.M)
    if not match or not Path(match[1]).is_file():
        raise ValueError("Build Flocq first; its configured COQC is unavailable")
    return match[1]


def lean_source_fingerprint(root: Path = ROOT) -> str:
    """Bind a run to stable project Lean sources and dependency configuration.

    This is a concurrent-edit guard, not attestation of compiler binaries or
    external build artifacts. A normal Lake build still precedes execution.
    """
    digest = hashlib.sha256()
    paths = sorted((root / "FloatSpec").rglob("*.lean"))
    paths.extend(root / name for name in
                 ("FloatSpec.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json"))
    for path in paths:
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def require_lean_source_snapshot(expected: str) -> None:
    if lean_source_fingerprint() != expected:
        raise RuntimeError("Lean sources/configuration changed during verification; rebuild and rerun")


def verify_reference(flocq: Path) -> str:
    """Reject a different or modified reference, even if its build succeeds."""
    pin = run(["git", "rev-parse", "HEAD:Deps/flocq"]).strip()
    if run(["git", "-C", str(flocq), "rev-parse", "HEAD"]).strip() != pin:
        raise ValueError("reference checkout does not match the parent repository's gitlink")
    run(["git", "-C", str(flocq), "diff", "--exit-code", "HEAD", "--", "src"])
    untracked = run(["git", "-C", str(flocq), "ls-files", "--others", "--exclude-standard", "src"])
    if any(path.endswith(".v") for path in untracked.splitlines()):
        raise ValueError("reference contains untracked Rocq source files")
    return pin


def compiled_source(rows: list[tuple[str, str]], instances: str) -> str:
    return (LEAN_HEADER + instances + "def main : IO Unit := IO.println ([\n" +
            ",\n".join(row[0] for row in rows) +
            "\n] : List (List Int))\nend Bridge\ndef main := Bridge.main\n")


def execute(cases: list[Case], flocq: Path, coqc: str, folder: Path) -> dict[str, list]:
    rows = [expressions(case) for case in cases]
    lean_path, coq_path = folder / "Bridge.lean", folder / "Bridge.v"
    radices = sorted({case.args[0] for case in cases if case.op in RADIX_OPS})
    instances = "".join(f"private instance : ValidRadix {base} := ⟨by decide⟩\n"
                        for base in radices if base != 2)
    lean_path.write_text(LEAN_HEADER + instances + "#reduce ([\n" +
                         ",\n".join(row[0] for row in rows) +
                         "\n] : List (List Int))\nend Bridge\n")
    coq_path.write_text(COQ_HEADER + "Eval vm_compute in [\n" +
                        ";\n".join(row[1] for row in rows) + "\n].\n")
    compiled_path = folder / "Compiled.lean"
    compiled_path.write_text(compiled_source(rows, instances))
    commands = {"lean": ["lake", "env", "lean", str(lean_path)],
                "compiled": ["lake", "env", "lean", "--run", str(compiled_path)],
                "rocq": [coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(coq_path)]}

    def observe(name: str) -> list:
        output = run(commands[name])
        (folder / f"{name}.out").write_text(output)
        return parse_result(output, "rocq" if name == "rocq" else "lean", len(cases))

    with ThreadPoolExecutor(max_workers=3) as pool:
        futures = {name: pool.submit(observe, name) for name in commands}
        return {name: future.result() for name, future in futures.items()}


def compare(cases: list[Case], observations: dict[str, list]) -> list[dict]:
    if set(observations) != {"lean", "compiled", "rocq"}:
        raise ValueError("all three execution paths are required")
    for name, rows in observations.items():
        if len(rows) != len(cases) or any(len(row) != WIDTHS[case.op]
                                         for case, row in zip(cases, rows, strict=True)):
            raise ValueError(f"{name}: incomplete observation columns")
    mismatches = []
    for index, case in enumerate(cases):
        paths = [name for name in ("lean", "compiled")
                 if observations[name][index] != observations["rocq"][index]]
        if paths:
            mismatches.append({"index": index, "case": asdict(case), "paths": paths,
                               **{name: rows[index] for name, rows in observations.items()}})
    return mismatches


def bootstrap_lean(cases: list[Case], expected: list[list[int]], folder: Path) -> None:
    """Turn Rocq observations into actual kernel-checked Lean regression proofs."""
    rows = [expressions(case)[0] for case in cases]
    radices = sorted({case.args[0] for case in cases if case.op in RADIX_OPS})
    instances = "".join(f"private instance : ValidRadix {base} := ⟨by decide⟩\n"
                        for base in radices if base != 2)
    path = folder / "OracleRegressions.lean"
    statements = [f"example : ({row} : List Int) = {json.dumps(value)} := by decide +kernel"
                  for row, value in zip(rows, expected, strict=True)]
    path.write_text(LEAN_HEADER + instances + "\n".join(statements) + "\nend Bridge\n")
    output = run(["lake", "env", "lean", str(path)])
    (folder / "oracle_regressions.out").write_text(output)
    if output.strip():
        raise ValueError(f"unexpected Lean regression diagnostics: {output[:500]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flocq-dir", type=Path, required=True)
    parser.add_argument("--coqc", help="override the compiler recorded by the reference build")
    parser.add_argument("--seed", type=int, default=20260919)
    parser.add_argument("--samples", type=int, default=100, help="random cases per API after boundary grids")
    parser.add_argument("--batch-size", type=int, default=100)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--replay", type=Path, help="JSON list of {op, args} inputs")
    parser.add_argument("--operations", help="comma-separated test families; default is all")
    parser.add_argument("--skip-build", action="store_true",
                        help="reuse an explicitly prebuilt stable Lean snapshot; default builds first")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    flocq = args.flocq_dir.resolve()
    pin = verify_reference(flocq)
    coqc = args.coqc or configured_coqc(flocq)
    cases = ([Case(row["op"], tuple(row["args"])) for row in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if args.operations:
        selected = set(args.operations.split(","))
        if not selected <= set(OPS):
            parser.error(f"unknown test families: {selected - set(OPS)}")
        cases = [case for case in cases if case.op in selected]
    if not cases:
        parser.error("empty corpus is not a successful test")
    output = (args.output or Path(tempfile.mkdtemp(prefix="floatspec-bridge-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty; previous evidence is not overwritten")
    (output / "cases.json").write_text(json.dumps([asdict(case) for case in cases], indent=2) + "\n")
    report = {"seed": args.seed, "reference": pin, "lean_head": run(["git", "rev-parse", "HEAD"]).strip(),
              "lean_source_sha256": lean_source_fingerprint(),
              "worktree_status": run(["git", "status", "--porcelain"]).strip(),
              "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
              "rocq_version": run([coqc, "--version"]).strip(), "cases": len(cases),
              "operations": dict(Counter(case.op for case in cases)), "status": "running",
              "fresh_build": not args.skip_build,
              "method": "Lean compiled execution and kernel reduction versus Rocq vm_compute; finite tests only",
              "compared_cases": 0, "compiled_cases": 0, "bootstrapped_lean_cases": 0, "mismatches": []}
    report_path = output / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Executing {len(cases)} cases; seed={args.seed}; artifacts={output}", flush=True)
    started = time.monotonic()
    mismatches = []
    try:
        if not args.skip_build:
            build = run(["lake", "build", "FloatSpec.src.Calc.Plus", "FloatSpec.src.Calc.Div",
                         "FloatSpec.src.Calc.Sqrt", "FloatSpec.src.Core.FTZ",
                         "FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade",
                         "FloatSpec.src.IEEE754.BitsSourceFacade",
                         "FloatSpec.Test.BitsExecution"], timeout=600)
            (output / "lean_build.out").write_text(build)
        require_lean_source_snapshot(report["lean_source_sha256"])
        for offset in range(0, len(cases), args.batch_size):
            batch = cases[offset:offset + args.batch_size]
            folder = output / f"batch_{offset:06d}"
            folder.mkdir()
            observations = execute(batch, flocq, coqc, folder)
            for mismatch in compare(batch, observations):
                mismatch["index"] += offset
                mismatches.append(mismatch)
            report["compared_cases"] += len(batch)
            report["compiled_cases"] += len(batch)
            report["mismatches"] = mismatches
            if mismatches:
                (output / "replay.json").write_text(
                    json.dumps([m["case"] for m in mismatches], indent=2) + "\n")
            report_path.write_text(json.dumps(report, indent=2) + "\n")
            if observations["lean"] == observations["rocq"]:
                bootstrap_lean(batch, observations["rocq"], folder)
                report["bootstrapped_lean_cases"] += len(batch)
                report_path.write_text(json.dumps(report, indent=2) + "\n")
            print(f"{min(offset + args.batch_size, len(cases))}/{len(cases)}; "
                  f"mismatches={len(mismatches)}", flush=True)
            require_lean_source_snapshot(report["lean_source_sha256"])
        report["mismatches"] = mismatches
        report["status"] = "mismatch" if mismatches else "passed"
    except BaseException as error:
        report["status"] = "error"
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report_path.write_text(json.dumps(report, indent=2) + "\n")
    if mismatches:
        (output / "replay.json").write_text(json.dumps([m["case"] for m in mismatches], indent=2) + "\n")
        raise SystemExit(f"{len(mismatches)} mismatches; see {report_path}")
    print(f"PASS: {len(cases)} finite differential cases; see {report_path}")


if __name__ == "__main__":
    main()
