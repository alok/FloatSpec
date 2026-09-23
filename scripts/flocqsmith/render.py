"""Lean and Rocq renderings of one IR program (FLOCQSMITH.md §3.3, §3.7, §6).

Rocq never varies: it is the reference. The Lean rendering can be a
*variant*: a positive control that redirects chosen ops to a planted-defect
wrapper, replaces an observation encoder, or permutes the rounding modes. The
baseline variant uses the signature table unchanged. A variant never edits
``FloatSpec/``; its Lean definitions live in the generated file's preamble.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib

import flocq_bridge as fb

from .ir import Arg, Program, Stmt
from .table import (FOLD_SHAPES, LEAN_MODES, LEAN_SOURCE_MODES, OBSERVERS, OP_BY_NAME, ROCQ_MODES, BSN)


@dataclass(frozen=True)
class LeanVariant:
    """A Lean-side rendering policy; ``baseline`` is the unmutated table."""

    name: str = "baseline"
    ops: dict[str, str] = field(default_factory=dict)
    observers: dict[str, str] = field(default_factory=dict)
    mode_map: tuple[int, ...] | None = None
    description: str = ""

    def mode(self, index: int) -> int:
        return self.mode_map[index] if self.mode_map is not None else index


BASELINE = LeanVariant()


def _lean_arg(arg: Arg) -> str:
    if arg.kind == "ref":
        return str(arg.value)
    if arg.kind == "int":
        return f"({arg.value} : Int)"
    if arg.kind == "bool":
        return "true" if arg.value else "false"
    if arg.kind == "pos":
        return f"(binaryPositiveOfNat {arg.value} (by decide))"
    if arg.kind == "sf":
        return f"({fb.small_ieee_raw(arg.value)} : StandardFloat)"
    raise ValueError(f"unknown argument kind {arg.kind}")


def _rocq_arg(arg: Arg) -> str:
    if arg.kind == "ref":
        return str(arg.value)
    if arg.kind == "int":
        return f"({arg.value})"
    if arg.kind == "bool":
        return "true" if arg.value else "false"
    if arg.kind == "pos":
        return f"({arg.value})%positive"
    if arg.kind == "sf":
        return f"({fb.small_ieee_raw(arg.value, True)})"
    raise ValueError(f"unknown argument kind {arg.kind}")


class _Renderer:
    def __init__(self, program: Program, variant: LeanVariant | None, lean: bool) -> None:
        self.program = program
        self.variant = variant or BASELINE
        self.lean = lean
        self.fmt = {"p": program.fmt.p, "e": program.fmt.emax}

    def arg(self, arg: Arg) -> str:
        return _lean_arg(arg) if self.lean else _rocq_arg(arg)

    def call(self, op: str, mode: int | None, spelling: str, args: list[Arg]) -> str:
        row = OP_BY_NAME[op]
        values = {f"a{k}": self.arg(a) for k, a in enumerate(args)}
        if not self.lean:
            return row.rocq.format(**self.fmt, m=ROCQ_MODES[mode] if mode is not None else "", **values)
        lean_mode = self.variant.mode(mode) if mode is not None else 0
        override = self.variant.ops.get(op)
        if override is not None:
            template = override
        elif spelling == "source" and row.lean_source is not None:
            template = row.lean_source
        else:
            template = row.lean
        return template.format(**self.fmt, m=LEAN_MODES[lean_mode], sm=LEAN_SOURCE_MODES[lean_mode], **values)

    def observe(self, name: str, type_: str) -> str:
        lean, rocq, _ = OBSERVERS[type_]
        if self.lean:
            lean = self.variant.observers.get(type_, lean)
        return (lean if self.lean else rocq).format(v=name, **self.fmt)

    def bind(self, name: str, expr: str) -> str:
        return f"let {name} := {expr}; " if self.lean else f"let {name} := {expr} in "

    def block(self, stmts: tuple[Stmt, ...]) -> tuple[str, list[str]]:
        text, observed = "", []
        for s in stmts:
            if s.kind == "op":
                text += self.bind(s.id, self.call(s.op or "", s.mode, s.spelling, list(s.args)))
                observed.append(self.observe(s.id, s.type))
            elif s.kind == "select":
                c, a, b = (self.arg(x) for x in s.args)
                expr = f"bif {c} then {a} else {b}" if self.lean else f"if {c} then {a} else {b}"
                text += self.bind(s.id, expr)
                observed.append(self.observe(s.id, s.type))
            elif s.kind == "case4":
                compare = self.call("Bcompare", None, "core", list(s.args[:2]))
                lt, eq, gt, none = (self.arg(x) for x in s.args[2:])
                if self.lean:
                    expr = (f"(match {compare} with | some .lt => {lt} | some .eq => {eq} "
                            f"| some .gt => {gt} | none => {none})")
                else:
                    expr = (f"match {compare} with Some Lt => {lt} | Some Eq => {eq} "
                            f"| Some Gt => {gt} | None => {none} end")
                text += self.bind(s.id, expr)
                observed.append(self.observe(s.id, s.type))
            elif s.kind == "fold":
                acc_position, _ = FOLD_SHAPES[s.op or ""]
                acc = s.args[0]
                for name, step in zip(s.fold_ids(), s.steps):
                    args = list(step)
                    args.insert(acc_position, acc)
                    text += self.bind(name, self.call(s.op or "", s.mode, "core", args))
                    observed.append(self.observe(name, "BSN"))
                    acc = Arg.ref(name)
            elif s.kind == "branch":
                arms = []
                for tag, arm in enumerate(s.arms):
                    inner, inner_observed = self.block(arm)
                    arms.append(f"({inner}[{tag}] ++ " + " ++ ".join(inner_observed) + ")")
                c = self.arg(s.args[0])
                if self.lean:
                    text += f"let {s.id} : List Int := bif {c} then {arms[0]} else {arms[1]}; "
                else:
                    text += f"let {s.id} := if {c} then {arms[0]} else {arms[1]} in "
                observed.append(s.id)
            else:
                raise ValueError(f"unknown statement kind {s.kind}")
        return text, observed

    def term(self) -> str:
        body, observed = self.block(self.program.stmts)
        p, e = self.program.fmt.p, self.program.fmt.emax
        prefix = (f"letI : Prec_gt_0 {p} := ⟨by decide⟩; letI : Prec_lt_emax {p} {e} := ⟨by decide⟩; "
                  if self.lean else "")
        return prefix + body + " ++ ".join(observed)


def lean_term(program: Program, variant: LeanVariant | None = None) -> str:
    """A closed Lean term of type ``List Int`` (the whole observation)."""
    return _Renderer(program, variant, lean=True).term()


def rocq_term(program: Program) -> str:
    """A closed Rocq term of type ``list Z`` (the whole observation)."""
    return _Renderer(program, None, lean=False).term()


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


# -- whole files -------------------------------------------------------------

LEAN_EXTRA = """set_option linter.unusedVariables false
"""

ROCQ_EXTRA = """Set Warnings "-deprecated".
Ltac run_case t := first [ timeout {timeout} (let v := eval vm_compute in t in idtac "OK" v)
                          | (let _ := constr:(t) in idtac "TIMEOUT") ].
"""


@dataclass(frozen=True)
class Rendered:
    """One case's rendered text (Lean term per variant, one Rocq term)."""

    case_id: str
    lean: str
    rocq: str


def lean_file(preamble: str, commands: list[str], ir_main: list[str] | None = None) -> str:
    """Bridge header, flocqsmith options, variant preamble, then commands."""
    text = fb.LEAN_HEADER + LEAN_EXTRA
    if ir_main is not None:
        text += "set_option compiler.extract_closed false\n"
    text += preamble
    text += "".join(commands)
    if ir_main is not None:
        text += ("def fsEmit (label : String) (f : Unit → List Int) : IO Unit := do\n"
                 "  IO.eprintln s!\"FSBEGIN {label}\"\n"
                 "  (← IO.getStderr).flush\n"
                 "  let v := f ()\n"
                 "  IO.println s!\"FSOUT {label} {v}\"\n"
                 "  (← IO.getStdout).flush\n"
                 "def main : IO Unit := do\n"
                 "  pure ()\n" + "".join(ir_main))
    text += "end Bridge\n"
    if ir_main is not None:
        text += "def main := Bridge.main\n"
    return text


def rocq_file(cases: list[tuple[str, str]], timeout_seconds: int) -> str:
    text = fb.COQ_HEADER + ROCQ_EXTRA.format(timeout=timeout_seconds) + "Goal True.\n"
    for label, term in cases:
        text += f"idtac \"FSCASE {label}\"; run_case (({term}) : list Z).\n"
    return text + "Abort.\n"


def lean_bsn_type(program: Program) -> str:
    return f"{BSN}.binary_float {program.fmt.p} {program.fmt.emax}"
