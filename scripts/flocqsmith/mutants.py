"""Positive controls: planted defects and encoder/renderer mutations (§10).

"0 mismatches" means nothing until the same pipeline has detected planted
defects. Each control is a :class:`~flocqsmith.render.LeanVariant`: for the
ops it names, the Lean side calls a wrapper defined in the generated file's
preamble (never under ``FloatSpec/``) around the real FloatSpec function, or
uses a mutated observation encoder, or permutes the rounding modes. Rocq is
never mutated. A control is *exposed* by a program that uses one of its ops
and *detected* when at least one Lean path reports ``observation-mismatch``.
A control must never produce an infrastructure or harness verdict.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .ir import Program, iter_bindings
from .render import LeanVariant

BF = "BinarySingleNaN.binary_float prec emax"
INST = "{prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]"

PREAMBLE = f"""namespace FlocqsmithMutant
def rneAsRna : RoundingMode → RoundingMode
  | .RNE => .RNA
  | m => m
def rnaAsRne : RoundingMode → RoundingMode
  | .RNA => .RNE
  | m => m
def swapDirected : RoundingMode → RoundingMode
  | .RTP => .RTN
  | .RTN => .RTP
  | m => m
def isRTN : RoundingMode → Bool
  | .RTN => true
  | _ => false
def isRTZ : RoundingMode → Bool
  | .RTZ => true
  | _ => false
def isZero {{prec emax : Int}} (r : {BF}) : Bool :=
  match BinarySingleNaN.B2SF r with
  | .S754_zero _ => true
  | _ => false
def isMaxMag {INST} (r : {BF}) : Bool :=
  BinarySingleNaN.Beqb (BinarySingleNaN.Babs r) (BinarySingleNaN.Bmax_float (prec := prec) (emax := emax))
-- tie_rne_as_rna: nearest-even answered as nearest-away.
def tie_Bplus {INST} (m : RoundingMode) (x y : {BF}) : {BF} := BinarySingleNaN.Bplus (rneAsRna m) x y
def tie_Bminus {INST} (m : RoundingMode) (x y : {BF}) : {BF} := BinarySingleNaN.Bminus (rneAsRna m) x y
def tie_Bmult {INST} (m : RoundingMode) (x y : {BF}) : {BF} := BinarySingleNaN.Bmult (rneAsRna m) x y
def tie_Bfma {INST} (m : RoundingMode) (x y z : {BF}) : {BF} := BinarySingleNaN.Bfma (rneAsRna m) x y z
-- dn_zero_sign: an exact zero result under DN gets the wrong sign.
def dnz_Bplus {INST} (m : RoundingMode) (x y : {BF}) : {BF} :=
  let r := BinarySingleNaN.Bplus m x y
  if isRTN m && isZero r then BinarySingleNaN.Bopp r else r
def dnz_Bminus {INST} (m : RoundingMode) (x y : {BF}) : {BF} :=
  let r := BinarySingleNaN.Bminus m x y
  if isRTN m && isZero r then BinarySingleNaN.Bopp r else r
-- updn_swap_negative: UP and DN dispatched the wrong way for negative results.
def updn_Bmult {INST} (m : RoundingMode) (x y : {BF}) : {BF} :=
  let r := BinarySingleNaN.Bmult m x y
  if BinarySingleNaN.Bsign r then BinarySingleNaN.Bmult (swapDirected m) x y else r
def updn_Bdiv {INST} (m : RoundingMode) (x y : {BF}) : {BF} :=
  let r := BinarySingleNaN.Bdiv m x y
  if BinarySingleNaN.Bsign r then BinarySingleNaN.Bdiv (swapDirected m) x y else r
-- zr_overflow_to_inf: overflow under ZR returns an infinity instead of the largest float.
def zro_Bmult {INST} (m : RoundingMode) (x y : {BF}) : {BF} :=
  let r := BinarySingleNaN.Bmult m x y
  if isRTZ m && isMaxMag r then
    BinarySingleNaN.Bmult (if BinarySingleNaN.Bsign r then .RTN else .RTP) x y else r
def zro_Bplus {INST} (m : RoundingMode) (x y : {BF}) : {BF} :=
  let r := BinarySingleNaN.Bplus m x y
  if isRTZ m && isMaxMag r then
    BinarySingleNaN.Bplus (if BinarySingleNaN.Bsign r then .RTN else .RTP) x y else r
-- subnormal_exp_off_by_one: a subnormal result lands one binade low.
def subShift {INST} (r : {BF}) : {BF} :=
  match BinarySingleNaN.B2SF r with
  | .S754_finite s m e =>
      if (m : Int) < 2 ^ (prec - 1).toNat then
        BinarySingleNaN.binary_normalize (prec := prec) (emax := emax) .RNE
          (if s then -(m : Int) else (m : Int)) (e - 1) s
      else r
  | _ => r
def sub_Bmult {INST} (m : RoundingMode) (x y : {BF}) : {BF} := subShift (BinarySingleNaN.Bmult m x y)
def sub_Bdiv {INST} (m : RoundingMode) (x y : {BF}) : {BF} := subShift (BinarySingleNaN.Bdiv m x y)
-- fma_double_rounding: fma computed as a rounded product followed by a rounded sum.
def dbl_Bfma {INST} (m : RoundingMode) (x y z : {BF}) : {BF} :=
  BinarySingleNaN.Bplus m (BinarySingleNaN.Bmult m x y) z
-- succ_max_saturates: the successor of the largest float stays finite.
def sat_Bsucc {INST} (x : {BF}) : {BF} :=
  if isMaxMag x && !BinarySingleNaN.Bsign x then x else BinarySingleNaN.Bsucc x
def sat_Bsucc' {INST} (x : {BF}) : {BF} :=
  if isMaxMag x && !BinarySingleNaN.Bsign x then x else BinarySingleNaN.Bsucc' x
-- ltb_as_leb: strict comparison answered as non-strict.
def lt_Bltb {{prec emax : Int}} (x y : {BF}) : Bool := BinarySingleNaN.Bleb x y
-- trunc_floor: truncation of a negative non-integer rounds down instead of toward zero.
def floor_Btrunc {{prec emax : Int}} [Prec_lt_emax prec emax] (x : {BF}) : Int :=
  let t := BinarySingleNaN.Btrunc x
  if BinarySingleNaN.Bsign x && BinarySingleNaN.is_finite x &&
      !(BinarySingleNaN.Beqb (BinarySingleNaN.Bnearbyint .RTZ x) x) then t - 1 else t
-- nearbyint_na_as_ne: nearest-away rounding to an integer answered as nearest-even.
def na_Bnearbyint {{prec emax : Int}} [Prec_lt_emax prec emax] (m : RoundingMode) (x : {BF}) : {BF} :=
  BinarySingleNaN.Bnearbyint (rnaAsRne m) x
-- enc_sign_flip: the finite-value encoder reports the opposite sign.
def standardSignFlip : StandardFloat → List Int
  | .S754_finite s m e => [3, boolean (!s), m, e]
  | x => standard x
end FlocqsmithMutant
"""

M = "FlocqsmithMutant"


@dataclass(frozen=True)
class Control:
    """``ops`` expose the control; ``corners`` are the relational corners a
    control-focused corpus forces into a program to reach the defect."""

    name: str
    family: str
    variant: LeanVariant
    ops: tuple[str, ...]
    description: str
    corners: tuple[str, ...] = ()


def _planted(name: str, description: str, ops: dict[str, str], corners: tuple[str, ...]) -> Control:
    variant = LeanVariant(name=name, ops={op: f"{M}.{template}" for op, template in ops.items()},
                          description=description)
    return Control(name, "planted", variant, tuple(ops), description, corners)


CONTROLS: tuple[Control, ...] = (
    _planted("tie_rne_as_rna", "ties under NE rounded away from zero",
             {"Bplus": "tie_Bplus {m} {a0} {a1}", "Bminus": "tie_Bminus {m} {a0} {a1}",
              "Bmult": "tie_Bmult {m} {a0} {a1}", "Bfma": "tie_Bfma {m} {a0} {a1} {a2}"},
             ("tie_plus", "tie_mult")),
    _planted("dn_zero_sign", "exact zero sum under DN has the wrong sign",
             {"Bplus": "dnz_Bplus {m} {a0} {a1}", "Bminus": "dnz_Bminus {m} {a0} {a1}"}, ("cancel",)),
    _planted("updn_swap_negative", "UP/DN swapped for negative products and quotients",
             {"Bmult": "updn_Bmult {m} {a0} {a1}", "Bdiv": "updn_Bdiv {m} {a0} {a1}"}, ("tiny",)),
    _planted("zr_overflow_to_inf", "overflow under ZR yields infinity instead of the largest float",
             {"Bmult": "zro_Bmult {m} {a0} {a1}", "Bplus": "zro_Bplus {m} {a0} {a1}"}, ("overflow_edge",)),
    _planted("subnormal_exp_off_by_one", "subnormal results one binade low (FLT emin clamp)",
             {"Bmult": "sub_Bmult {m} {a0} {a1}", "Bdiv": "sub_Bdiv {m} {a0} {a1}"}, ("tiny",)),
    _planted("fma_double_rounding", "fma rounds the product before the sum",
             {"Bfma": "dbl_Bfma {m} {a0} {a1} {a2}"}, ("fma_error",)),
    _planted("succ_max_saturates", "successor of the largest float stays finite",
             {"Bsucc": "sat_Bsucc {a0}", "Bsucc'": "sat_Bsucc' {a0}"}, ("max_succ",)),
    _planted("ltb_as_leb", "strict less-than answered as less-or-equal", {"Bltb": "lt_Bltb {a0} {a1}"},
             ("equal_pair",)),
    _planted("trunc_floor", "truncation of negative non-integers rounds down", {"Btrunc": "floor_Btrunc {a0}"},
             ("half_int",)),
    _planted("nearbyint_na_as_ne", "nearbyint under NA uses ties-to-even",
             {"Bnearbyint": "na_Bnearbyint {m} {a0}"}, ("half_int",)),
    Control("enc_sign_flip", "encoder",
            LeanVariant(name="enc_sign_flip",
                        observers={"BSN": f"{M}.standardSignFlip (BinarySingleNaN.B2SF {{v}})"},
                        description="BSN encoder flips the sign of finite values"),
            (), "BSN encoder flips the sign of finite values"),
    Control("enc_bool_negate", "encoder",
            LeanVariant(name="enc_bool_negate", observers={"Bool": "[boolean (!{v})]"},
                        description="Boolean encoder negated"),
            (), "Boolean encoder negated"),
    Control("mode_swap_up_dn", "renderer",
            LeanVariant(name="mode_swap_up_dn", mode_map=(0, 1, 3, 2, 4),
                        description="Lean renderer swaps UP and DN"),
            (), "Lean renderer swaps UP and DN"),
)

CONTROL_BY_NAME: dict[str, Control] = {c.name: c for c in CONTROLS}


def exposed(control: Control, program: Program) -> bool:
    """Whether a program can observe the control at all (computed from the IR)."""
    stmts = list(iter_bindings(program.stmts))
    if control.name == "enc_sign_flip":
        return any(s.type == "BSN" for s in stmts)
    if control.name == "enc_bool_negate":
        return any(s.type == "Bool" for s in stmts)
    if control.name == "mode_swap_up_dn":
        return any(s.mode in (2, 3) for s in stmts)
    return any(s.op in control.ops for s in stmts if s.kind in ("op", "fold"))


def preamble_for(variants: Iterable[LeanVariant]) -> str:
    """Mutant definitions are emitted only into files that use a variant."""
    return PREAMBLE if any(v.name != "baseline" for v in variants) else ""
