"""Verdict-preserving shrinking (FLOCQSMITH.md §9).

The target is "same verdict class on the same path, and the first divergent
binding is produced by the same op". A candidate that turns the case into a
different mismatch is rejected, so the shrinker cannot drift from one bug to
another. Every candidate is re-executed; nothing is assumed.

Passes, in order (each round renders all its candidates as one batch):

1. **flatten**: unroll folds into plain ops and replace a branch by the arm
   the reference took;
2. **cut** every binding after the first divergence;
3. **pin**: replace each input of the divergent binding by a literal mint of
   its *reference* value (every binding is observed, so this is known) and
   delete everything else, which usually leaves one op on literal arguments;
4. **simplify operands** toward catalogue values (0, 1, the minimum
   subnormal) and small integer literals;
5. **canonicalize** the mode toward NE and the spelling toward the core name.

Format descent (§9 pass 5) is not implemented.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Callable

from .ir import Arg, IRError, Program, Stmt, check_program
from .observe import Observed, values_by_id
from .table import FOLD_SHAPES, OP_BY_NAME
from .verdict import Verdict


@dataclass(frozen=True)
class Target:
    path: str
    verdict: str
    op: str

    def holds(self, verdict: Verdict | None) -> bool:
        return (verdict is not None and verdict.path == self.path and verdict.verdict == self.verdict
                and (verdict.divergence or {}).get("op") == self.op)

    def to_json(self) -> dict[str, str]:
        return {"path": self.path, "verdict": self.verdict, "op": self.op}


# Runs candidate programs; returns (target-path verdict, reference values) per candidate.
Runner = Callable[[list[Program]], list[tuple[Verdict | None, tuple[Observed, ...] | None]]]


@dataclass
class ShrinkResult:
    program: Program
    verdict: Verdict | None
    reference: tuple[Observed, ...] | None
    steps: list[dict[str, object]] = field(default_factory=list)
    rounds: int = 0


def _stmt_defining(program: Program, name: str) -> int:
    for index, s in enumerate(program.stmts):
        ids = s.fold_ids() if s.kind == "fold" else [s.id]
        if name in ids:
            return index
    raise KeyError(name)


def flatten(program: Program, reference: tuple[Observed, ...]) -> Program:
    """Folds become plain ops; a branch becomes the arm the reference took."""
    values = values_by_id(reference)
    out: list[Stmt] = []
    for s in program.stmts:
        if s.kind == "fold":
            acc_position, _ = FOLD_SHAPES[s.op or ""]
            acc = s.args[0]
            for name, step in zip(s.fold_ids(), s.steps):
                args = list(step)
                args.insert(acc_position, acc)
                out.append(Stmt(name, "op", "BSN", op=s.op, mode=s.mode, args=tuple(args)))
                acc = Arg.ref(name)
        elif s.kind == "branch":
            taken = values.get(s.id)
            if taken is None:
                raise IRError(f"branch {s.id} was not observed by the reference")
            out.extend(s.arms[taken.value[0]])
        else:
            out.append(s)
    return program.with_stmts(out)


def cut_after(program: Program, divergent: str) -> Program:
    return program.with_stmts(program.stmts[:_stmt_defining(program, divergent) + 1])


def literal_for(observed: Observed) -> Arg | None:
    if observed.type in ("Z", "E"):
        return Arg.int_(observed.value[0])
    if observed.type == "Bool":
        return Arg.bool_(bool(observed.value[0]))
    if observed.type in ("SF", "BSN"):
        kind, sign, m, e = observed.value
        return Arg.sf(3, sign, m, e) if kind == 3 else Arg.sf(kind, sign if kind != 2 else 0, 1, 0)
    return None


def pin(program: Program, divergent: str, reference: tuple[Observed, ...]) -> Program:
    """Keep only the divergent statement, with its inputs pinned to reference values."""
    values = values_by_id(reference)
    target = program.stmts[_stmt_defining(program, divergent)]
    if target.kind not in ("op", "select", "case4"):
        raise IRError(f"cannot pin inputs of a {target.kind}")
    pinned: list[Stmt] = []
    new_args: list[Arg] = []
    for arg in target.args:
        if arg.kind != "ref":
            new_args.append(arg)
            continue
        observed = values[str(arg.value)]
        literal = literal_for(observed)
        if literal is None:
            raise IRError(f"no literal for {observed.type}")
        if observed.type == "BSN":
            if not any(p.id == observed.id for p in pinned):
                pinned.append(Stmt(observed.id, "op", "BSN", op="SF2B'", args=(literal,)))
            new_args.append(arg)
        else:
            new_args.append(literal)
    return program.with_stmts(pinned + [replace(target, args=tuple(new_args), corner=None)])


def _simpler_literals(program: Program, stmt: Stmt) -> list[Arg]:
    """Catalogue replacements for a pinned SF2B' literal, simplest first."""
    kind, sign, m, e = stmt.args[0].value  # type: ignore[misc]
    f = program.fmt
    options = [Arg.sf(0, sign, 1, 0), Arg.sf(3, sign, 1 << (f.p - 1), 1 - f.p), Arg.sf(3, sign, 1, f.emin),
               Arg.sf(3, 0, 1 << (f.p - 1), 1 - f.p)]
    if kind == 3:
        canonical = f.canonical(1 << (f.p - 1), e)
        if canonical is not None:
            options.append(Arg.sf(3, sign, *canonical))
    return [o for o in options if o != stmt.args[0]]


def simplify_candidates(program: Program) -> list[tuple[str, Program]]:
    out: list[tuple[str, Program]] = []
    last = program.stmts[-1]
    for index, s in enumerate(program.stmts[:-1]):
        if s.kind == "op" and s.op == "SF2B'" and s.args[0].kind == "sf":
            for option in _simpler_literals(program, s):
                stmts = list(program.stmts)
                stmts[index] = replace(s, args=(option,))
                out.append((f"simplify {s.id} -> {option.value}", program.with_stmts(stmts)))
    row = OP_BY_NAME.get(last.op or "") if last.kind == "op" else None
    for position, arg in enumerate(last.args):
        if arg.kind in ("int", "pos") and abs(int(arg.value)) > 1:  # type: ignore[call-overload]
            for smaller in (1, 0, -1) if arg.kind == "int" else (1,):
                args = list(last.args)
                args[position] = Arg(arg.kind, smaller)
                out.append((f"simplify {last.id}.arg{position} -> {smaller}",
                            program.with_stmts(list(program.stmts[:-1]) + [replace(last, args=tuple(args))])))
    if row is not None and last.mode not in (None, 0):
        out.append(("mode -> NE", program.with_stmts(list(program.stmts[:-1]) + [replace(last, mode=0)])))
    if last.spelling != "core":
        out.append(("spelling -> core",
                    program.with_stmts(list(program.stmts[:-1]) + [replace(last, spelling="core")])))
    valid = []
    for label, candidate in out:
        try:
            check_program(candidate)
        except IRError:
            continue
        valid.append((label, candidate))
    return valid


def _complexity(program: Program) -> tuple[int, int]:
    literal_bits = 0
    for s in program.stmts:
        for a in s.args:
            if a.kind in ("int", "pos"):
                literal_bits += abs(int(a.value)).bit_length()  # type: ignore[call-overload]
            elif a.kind == "sf":
                literal_bits += int(a.value[2]).bit_length() + abs(int(a.value[3])).bit_length()  # type: ignore[index]
        literal_bits += 0 if s.mode in (None, 0) else 1
        literal_bits += 0 if s.spelling == "core" else 1
    return len(program.stmts), literal_bits


def shrink(program: Program, reference: tuple[Observed, ...], divergent: str, target: Target, run: Runner,
           max_rounds: int = 6) -> ShrinkResult:
    """Shrink ``program`` while ``target`` keeps holding; every step is re-executed."""
    current, current_ref, current_verdict = program, reference, None
    result = ShrinkResult(program, None, reference)

    def attempt(label: str, candidates: list[tuple[str, Program]]) -> bool:
        nonlocal current, current_ref, current_verdict
        if not candidates:
            return False
        result.rounds += 1
        outcomes = run([c for _, c in candidates])
        for (name, candidate), (verdict, ref) in zip(candidates, outcomes):
            accepted = target.holds(verdict)
            result.steps.append({"pass": label, "candidate": name, "statements": len(candidate.stmts),
                                 "accepted": accepted,
                                 "verdict": verdict.to_json() if verdict is not None else None})
            if accepted and ref is not None:
                current, current_ref, current_verdict = candidate, ref, verdict
                return True
        return False

    divergent_id = divergent
    try:
        attempt("flatten", [("flatten", flatten(current, current_ref))])
    except IRError as error:
        result.steps.append({"pass": "flatten", "skipped": str(error)})
    try:
        attempt("cut", [("cut", cut_after(current, divergent_id))])
    except (IRError, KeyError) as error:
        result.steps.append({"pass": "cut", "skipped": str(error)})
    try:
        if current_verdict is not None:
            divergent_id = str((current_verdict.divergence or {}).get("id", divergent_id))
        attempt("pin", [("pin", pin(current, divergent_id, current_ref))])
    except (IRError, KeyError) as error:
        result.steps.append({"pass": "pin", "skipped": str(error)})
    for _ in range(max_rounds):
        candidates = [(label, c) for label, c in simplify_candidates(current)
                      if _complexity(c) < _complexity(current)]
        if not attempt("simplify", candidates):
            break
    result.program, result.reference = current, current_ref
    result.verdict = current_verdict
    return result
