"""flocqsmith regressions; set FLOCQ_AUDIT_DIR to include the live prover tests.

Offline tests cover the draw tape (deterministic replay and the mutated-tape
sweep), IR typing, renderers, decoding, the verdict taxonomy, stream parsers,
the cost model, numeric tags and the shrinker's mechanics. Live tests run
generated programs through Rocq ``vm_compute`` and all three Lean paths:
generator validity (every table op, form and corner type-checks in both
provers), replay from a record, verdict-preserving shrinking, detection of
every positive control, and offline re-judgement of a published campaign.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import json
import os
from pathlib import Path
import random
import sys
import tempfile
import unittest

import flocq_bridge as fb
from flocqsmith import harness, observe, verdict
from flocqsmith.campaign import (Options, case_from_program, load_case, new_case, replay, run_campaign,
                                 shrink_case, verify)
from flocqsmith.choose import Chooser, Draw, GeneratorBug, ReplayError
from flocqsmith.cost import pack
from flocqsmith.descriptor import (FAMILIES, FAMILY_OF, _root_signature, _signature_key, check_families,
                                   load_descriptor)
from flocqsmith.formats import FORMATS, Format
from flocqsmith.generate import CORNERS, GenConfig, generate, program_seed
from flocqsmith.harness import (DECIDE_REJECTION_PREFIXES, REJECTED, Message, Subject, Toolchain,
                                combine_kernel, execute_batch, parse_ir, parse_kernel, parse_meta, parse_rocq)
from flocqsmith.ir import Arg, IRError, Program, Stmt, check_program, signature
from flocqsmith.mutants import CONTROLS, CONTROL_BY_NAME, exposed
from flocqsmith.numeric import classify, numeric_tags, structural_tags
from flocqsmith.observe import DecodeError, decode
from flocqsmith.process import ProcResult
from flocqsmith.render import BASELINE, lean_term, rocq_term
from flocqsmith.shrink import Target, cut_after, flatten, pin, shrink
from flocqsmith.table import LEAN_ALLOWED_PREFIXES, LEAN_FORBIDDEN, OPS, check_table
from flocqsmith.verdict import CLONE_PATHS, Outcome, Verdict, judge

LIVE = os.environ.get("FLOCQ_AUDIT_DIR")


def programs(seed: int, count: int, config: GenConfig | None = None) -> list[tuple[Chooser, Program]]:
    out = []
    for index in range(count):
        chooser = Chooser(seed=program_seed(seed, index))
        out.append((chooser, generate(chooser, config or GenConfig()).program))
    return out


def one_value(fmt: Format) -> tuple[int, ...]:
    return (3, 0, 1 << (fmt.p - 1), 1 - fmt.p)


def mint_value(fmt: Format, mint: Stmt) -> tuple[int, int, int, int]:
    """The exact finite value a generator mint statement denotes."""
    if mint.op == "SF2B'":
        kind, sign, m, e = mint.args[0].value  # type: ignore[misc]
    elif mint.op == "binary_normalize":
        mm, e = int(mint.args[0].value), int(mint.args[1].value)  # type: ignore[call-overload]
        kind, sign, m = 3, int(mm < 0), abs(mm)
    elif mint.op == "Bone":
        kind, sign, m, e = 3, 0, 1 << (fmt.p - 1), 1 - fmt.p
    elif mint.op == "Bmax_float":
        kind, sign, m, e = 3, 0, (1 << fmt.p) - 1, fmt.emax_field
    else:
        raise AssertionError(f"not a mint: {mint}")
    canonical = fmt.canonical(m, e)
    assert canonical is not None
    return kind, sign, canonical[0], canonical[1]


# -- offline -------------------------------------------------------------------

class TableTests(unittest.TestCase):
    def test_table_shape_and_name_allowlist(self):
        check_table()
        for row in OPS:
            for template in (row.lean, row.lean_source or row.lean):
                self.assertTrue(template.lstrip("(").startswith(LEAN_ALLOWED_PREFIXES), row.name)
                self.assertFalse(any(bad in template for bad in LEAN_FORBIDDEN), row.name)
            self.assertTrue(row.rocq.lstrip("sndft (").startswith("@BinarySingleNaN."), row.name)

    def test_every_op_form_and_corner_is_generated(self):
        for row in OPS:
            program = generate(Chooser(seed=f"op:{row.name}"), GenConfig(force_ops=(row.name,))).program
            self.assertIn(f"op:{row.name}", structural_tags(program))
        for form in ("select", "case4", "fold", "branch", *(f"corner:{c}" for c in CORNERS)):
            # tie_mult needs p >= 3; in smaller formats it falls back to another corner.
            weights = (("b16", 1),) if form == "corner:tie_mult" else GenConfig().format_weights
            program = generate(Chooser(seed=f"form:{form}"),
                               GenConfig(format_weights=weights, force_forms=(form,))).program
            tags = structural_tags(program)
            expected = "form:fold_" if form == "fold" else form if form.startswith("corner:") else f"form:{form}"
            self.assertTrue(any(t.startswith(expected) for t in tags), (form, tags))


class FormatTests(unittest.TestCase):
    def test_canonical_matches_brute_force(self):
        for fmt in (FORMATS[n] for n in ("t1_2", "t2_3", "t3_4", "t4_8", "t5_7")):
            grid = {}
            for e in range(fmt.emin, fmt.emax_field + 1):
                for m in range(1, 1 << fmt.p):
                    if fmt.is_canonical(m, e):
                        grid[Fraction(m) * Fraction(2) ** e] = (m, e)
            for e in range(fmt.emin - 3, fmt.emax + 3):
                for m in range(1, 1 << (fmt.p + 2)):
                    value = Fraction(m) * Fraction(2) ** e
                    self.assertEqual(fmt.canonical(m, e), grid.get(value), (fmt.name, m, e))


class ChooserTests(unittest.TestCase):
    def test_generation_is_deterministic_and_tape_replay_is_exact(self):
        configs = [GenConfig(), GenConfig(swarm_include=("Bfma", "Btrunc")), GenConfig(min_size=1, max_size=3),
                   GenConfig(force_forms=("branch", "fold", "select", "case4"))]
        for k, config in enumerate(configs):
            for chooser, program in programs(100 + k, 150, config):
                replayed = Chooser(tape=chooser.draws)
                result = generate(replayed, config)
                self.assertEqual(result.program, program)
                self.assertEqual(lean_term(result.program), lean_term(program))
                self.assertEqual(rocq_term(result.program), rocq_term(program))
        first = [p.sha256() for _, p in programs(7, 40)]
        self.assertEqual(first, [p.sha256() for _, p in programs(7, 40)])
        self.assertNotEqual(first, [p.sha256() for _, p in programs(8, 40)])

    def test_typed_replay_errors(self):
        chooser, _ = programs(3, 1)[0]
        tape = list(chooser.draws)
        cases = {
            "exhausted": tape[:-1],
            "leftover": tape + [Draw("extra", 2, 0)],
            "site": [Draw("elsewhere", tape[0].bound, tape[0].value)] + tape[1:],
            "bound": [Draw(tape[0].site, tape[0].bound + 1, tape[0].value)] + tape[1:],
            "range": [Draw(tape[0].site, tape[0].bound, tape[0].bound)] + tape[1:],
        }
        for kind, bad in cases.items():
            with self.subTest(kind=kind), self.assertRaises(ReplayError) as caught:
                generate(Chooser(tape=bad), GenConfig())
            self.assertEqual(caught.exception.kind, kind)
        masked = Chooser(tape=[Draw("s", 2, 1)])
        with self.assertRaises(ReplayError) as caught:
            masked.choose("s", [("a", 1), ("b", 0)])
        self.assertEqual(caught.exception.kind, "illegal")

    def test_generator_bugs_raise(self):
        chooser = Chooser(seed="x")
        with self.assertRaises(GeneratorBug):
            chooser.choose("empty", [("a", 0)])
        with self.assertRaises(GeneratorBug):
            chooser.randint("bad", 3, 2)
        with self.assertRaises(ValueError):
            Chooser(seed="x", tape=[])

    def test_mutated_tape_sweep_has_no_third_outcome(self):
        rng = random.Random(11)
        outcomes: Counter[str] = Counter()
        for chooser, _ in programs(21, 40):
            tape = chooser.draws
            for _ in range(15):
                bad = list(tape)
                index = rng.randrange(len(bad))
                draw = bad[index]
                bad[index] = Draw(draw.site, draw.bound, rng.randrange(draw.bound))
                try:
                    program = generate(Chooser(tape=bad), GenConfig()).program
                    check_program(program)
                    lean_term(program), rocq_term(program)
                    outcomes["valid"] += 1
                except ReplayError as error:
                    outcomes[f"replay:{error.kind}"] += 1
        self.assertGreater(outcomes["valid"], 0)
        self.assertTrue(any(k.startswith("replay:") for k in outcomes), outcomes)


class IRTests(unittest.TestCase):
    def test_json_round_trip_and_rejection(self):
        for _, program in programs(4, 60, GenConfig(force_forms=("branch", "fold", "case4"))):
            text = json.dumps(program.to_json())
            self.assertEqual(Program.from_json(json.loads(text)), program)
        fmt = FORMATS["b16"]
        good = Stmt("v0", "op", "BSN", op="Bone")
        bad_programs = [
            [Stmt("v0", "op", "BSN", op="Bopp", args=(Arg.ref("nope"),))],
            [good, Stmt("v1", "op", "Bool", op="Bltb", args=(Arg.ref("v0"), Arg.int_(1)))],
            [good, Stmt("v1", "op", "BSN", op="Bplus", args=(Arg.ref("v0"), Arg.ref("v0")))],
            [good, Stmt("v1", "op", "BSN", op="Bplus", mode=5, args=(Arg.ref("v0"), Arg.ref("v0")))],
            [good, Stmt("v1", "op", "BSN", op="Bldexp", mode=0, args=(Arg.ref("v0"), Arg.int_(10 ** 6)))],
            [good, good],
            [good, Stmt("v1", "op", "BSN", op="Bopp", spelling="source", args=(Arg.ref("v0"),))],
            [Stmt("v0", "op", "BSN", op="SF2B'", args=(Arg.sf(3, 2, 1, 0),))],
        ]
        for stmts in bad_programs:
            with self.subTest(stmts=stmts), self.assertRaises(IRError):
                check_program(Program(fmt, tuple(stmts)))

    def test_signature_matches_rendered_observers(self):
        for _, program in programs(5, 80):
            sig = signature(program)
            flat = [row for row in sig["bindings"]]  # type: ignore[union-attr]
            self.assertEqual(len(flat), sum(1 for s in program.stmts
                                            for _ in (s.fold_ids() if s.kind == "fold" else [s.id])))
            lean, rocq = lean_term(program), rocq_term(program)
            for name in (row["id"] for row in flat):
                self.assertIn(name, lean)
                self.assertIn(name, rocq)


class RenderTests(unittest.TestCase):
    def test_variants_change_only_lean(self):
        program = programs(6, 1, GenConfig(force_ops=("Bplus", "Bltb")))[0][1]
        for control in CONTROLS:
            mutated = lean_term(program, control.variant)
            if exposed(control, program):
                self.assertNotEqual(mutated, lean_term(program), control.name)
            self.assertEqual(rocq_term(program), rocq_term(program))
        swap = CONTROL_BY_NAME["mode_swap_up_dn"].variant
        stmt = Stmt("v1", "op", "BSN", op="Bplus", mode=3, args=(Arg.ref("v0"), Arg.ref("v0")))
        tiny = Program(FORMATS["t3_4"], (Stmt("v0", "op", "BSN", op="Bone"), stmt))
        self.assertIn("Bplus .RTN", lean_term(tiny, swap))
        self.assertIn("mode_UP", rocq_term(tiny))

    def test_line_ranges_point_at_case_markers(self):
        subjects = [Subject(f"c{k}", p, BASELINE) for k, (_, p) in enumerate(programs(9, 5))]
        for lean in (harness.meta_file(subjects, 1000, ""), harness.ir_file(subjects, "PRE\n"),
                     harness.kernel_file(subjects, {s.case_id: (1,) for s in subjects}, 1000, "")):
            lines = lean.text.splitlines()
            for label, (start, end) in lean.ranges.items():
                self.assertEqual(lines[start - 1], f"-- FSCASE {label}")
                self.assertTrue(end >= start + 1)


class DecodeTests(unittest.TestCase):
    def setUp(self):
        self.sig = {"p": 3, "emax": 4, "bindings": [
            {"id": "v0", "type": "BSN", "op": "Bone"}, {"id": "v1", "type": "Bool", "op": "Bltb"},
            {"id": "v2", "type": "branch", "op": "branch", "arms": [
                [{"id": "a", "type": "Cmp", "op": "Bcompare"}],
                [{"id": "b", "type": "E", "op": "Bfrexp.2"}, {"id": "c", "type": "SF", "op": "B2SF"}]]}]}

    def test_valid_documents(self):
        values = decode(self.sig, [3, 0, 4, -2, 1, 0, -1])
        self.assertEqual([v.id for v in observe.flatten(values)], ["v0", "v1", "v2", "a"])
        values = decode(self.sig, [0, 1, 0, 0, 0, 1, 7, 3, 1, 99, -9])
        self.assertEqual([v.id for v in observe.flatten(values)], ["v0", "v1", "v2", "b", "c"])

    def test_invalid_documents_raise(self):
        for doc in ([3, 0, 4, -2, 1, 0], [3, 0, 4, -2, 1, 0, -1, 5], [4, 0, 4, -2, 1, 0, -1],
                    [3, 2, 4, -2, 1, 0, -1], [3, 0, 8, -2, 1, 0, -1], [3, 0, 2, -2, 1, 0, -1],
                    [2, 0, 1, 0, 1, 0, -1], [3, 0, 4, -2, 2, 0, -1], [3, 0, 4, -2, 1, 0, 3],
                    [3, 0, 4, -2, 1, 2, 5], [0, 0, 5, 0, 1, 0, -1], [3, 0, 4, -2, 1, 1, 7, 3, 5, 9, 9],
                    [3, 0, 4, -2, 1, 1, 7, 3, 0, 0, 9]):
            with self.subTest(doc=doc), self.assertRaises(DecodeError):
                decode(self.sig, doc)


class VerdictTests(unittest.TestCase):
    SIG = {"p": 3, "emax": 4, "bindings": [{"id": "v0", "type": "BSN", "op": "Bone"},
                                            {"id": "v1", "type": "Bool", "op": "Bltb"}]}
    DOC = (3, 0, 4, -2, 1)
    OTHER = (3, 0, 5, -2, 1)
    INVALID = (3, 0, 4, -2)

    def outcomes(self) -> list[Outcome]:
        return [Outcome("ok", document=self.DOC), Outcome("ok", document=self.OTHER),
                Outcome("ok", document=self.INVALID), Outcome("harness", detail="x"),
                Outcome("kernel-true"), Outcome("kernel-false"), Outcome("not-run"),
                *(Outcome("infra", stage=s) for s in sorted(verdict.STAGES)), Outcome("infra", stage="lean-elab:k")]

    def test_infra_is_never_a_match_and_taxonomy_is_closed(self):
        references = [Outcome("ok", document=self.DOC), Outcome("ok", document=self.INVALID),
                      Outcome("infra", stage="timeout"), Outcome("harness")]
        seen: Counter[str] = Counter()
        for path in CLONE_PATHS:
            for reference in references:
                for clone in self.outcomes():
                    v = judge(self.SIG, path, reference, clone)
                    seen[v.verdict] += 1
                    self.assertIn(v.verdict, verdict.VERDICTS)
                    ref_valid = reference.status == "ok" and reference.document == self.DOC
                    if v.verdict == "match":
                        self.assertTrue(ref_valid)
                        self.assertTrue((path != "lean-kernel" and clone.document == self.DOC) or
                                        (path == "lean-kernel" and clone.status == "kernel-true"))
                    if clone.status == "infra" or reference.status == "infra":
                        self.assertNotIn(v.verdict, ("match", "observation-mismatch"))
                    if reference.status == "infra" and clone.status not in ("harness",):
                        self.assertIn(v.verdict, ("reference-infra-failure", "both-infra-failure"))
                    if reference.status == "ok" and clone.status == "infra":
                        self.assertEqual(v.verdict, "clone-infra-failure" if ref_valid else "harness-error")
                        if ref_valid:
                            self.assertEqual(v.stage, clone.stage)
                    if "harness" in (reference.status, clone.status):
                        self.assertEqual(v.verdict, "harness-error")
        self.assertEqual(set(seen), set(verdict.VERDICTS))

    def test_mismatch_records_first_divergence(self):
        v = judge(self.SIG, "lean-meta", Outcome("ok", document=self.DOC), Outcome("ok", document=(3, 0, 4, -2, 0)))
        self.assertEqual(v.verdict, "observation-mismatch")
        self.assertEqual(v.divergence, {"id": "v1", "op": "Bltb", "type": "Bool", "reference": [1], "clone": [0]})

    def test_outcome_invariants(self):
        for bad in (lambda: Outcome("infra"), lambda: Outcome("infra", stage="made-up"),
                    lambda: Outcome("ok"), lambda: Outcome("match"), lambda: Outcome("kernel-true", stage="timeout")):
            with self.assertRaises(ValueError):
                bad()
        with self.assertRaises(ValueError):
            Verdict("lean-meta", "sort-of-match")


def proc(stdout: str = "", stderr: str = "", returncode: int | None = 0, timed_out: bool = False) -> ProcResult:
    return ProcResult(("x",), stdout, stderr, returncode, timed_out, 0.0)


def message(line: int, severity: str, data: str, kind: str = "[anonymous]") -> str:
    return json.dumps({"pos": {"line": line, "column": 0}, "severity": severity, "kind": kind, "data": data})


class ParserTests(unittest.TestCase):
    def test_rocq(self):
        out = "FSCASE a\nOK [1; -2]\nFSCASE b\nOK\n[1; 2;\n 3]\nFSCASE c\nTIMEOUT\n"
        got = parse_rocq(out, "", 0, False, ["a", "b", "c", "d"])
        self.assertEqual(got["a"].document, (1, -2))
        self.assertEqual(got["b"].document, (1, 2, 3))
        self.assertEqual((got["c"].status, got["c"].stage), ("infra", "timeout"))
        self.assertEqual(got["d"].status, "harness")
        for stderr, code, timed_out in (("Error: x", 1, False), ("", 1, False), ("warning", 0, False), ("", None, True)):
            got = parse_rocq(out, stderr, code, timed_out, ["a", "b"])
            self.assertTrue(all(o.status == "harness" for o in got.values()))

    def test_meta(self):
        ranges = {"a": (10, 12), "b": (13, 15), "c": (16, 18), "d": (19, 21), "e": (22, 24)}
        lines = [message(12, "information", "[Int.ofNat 3, Int.negSucc 1]"),
                 message(15, "error", "failed", "lean.synthInstanceFailed._namedError"),
                 message(15, "information", "?m.6.1 1 true"),
                 message(18, "error", "timeout", "runtime.maxHeartbeats"),
                 message(21, "information", "BinarySingleNaN.Bplus x ⋯")]
        got = parse_meta(proc("\n".join(lines) + "\n", returncode=1), ranges)
        self.assertEqual(got["a"].document, (3, -2))
        self.assertEqual(got["b"].stage, "lean-elab:synthInstanceFailed")
        self.assertEqual(got["c"].stage, "heartbeats")
        self.assertEqual(got["d"].stage, "meta-stuck")
        self.assertEqual(got["e"].status, "harness")
        timed = parse_meta(proc(lines[0] + "\n", returncode=None, timed_out=True), ranges)
        self.assertEqual(timed["e"].stage, "timeout")
        stray = parse_meta(proc(message(2, "error", "header broke", "lean.x._namedError") + "\n", returncode=1), ranges)
        self.assertTrue(all(o.status == "harness" for o in stray.values()))
        anonymous = parse_meta(proc(message(12, "error", "Type mismatch") + "\n", returncode=1), ranges)
        self.assertEqual(anonymous["a"].status, "harness")

    def test_ir(self):
        ranges = {"a": (10, 12), "b": (13, 15), "c": (16, 18)}
        ok = parse_ir(proc("FSOUT a [1, -2]\nFSOUT b [3]\n", "FSBEGIN a\nFSBEGIN b\nFSBEGIN c\n", returncode=0),
                      ["a", "b", "c"], ranges)
        self.assertEqual(ok[0]["a"].document, (1, -2))
        self.assertEqual(ok[0]["c"].stage, "ir-crash")
        panic = parse_ir(proc("FSOUT a [0]\n", "FSBEGIN a\nPANIC at x\nbacktrace\n", returncode=0), ["a"], ranges)
        self.assertEqual(panic[0]["a"].stage, "ir-panic")
        crash = parse_ir(proc("FSOUT a [0]\n", "FSBEGIN a\nFSBEGIN b\nStack overflow\n", returncode=134),
                         ["a", "b", "c"], ranges)
        self.assertEqual(crash[0]["b"].stage, "ir-crash")
        self.assertEqual(crash[1], ["c"])
        compile_error = parse_ir(proc(message(14, "error", "noncomputable", "lean.dependsOnNoncomputable._namedError")
                                      + "\n", returncode=1), ["a", "b", "c"], ranges)
        self.assertEqual(compile_error[0]["b"].stage, "noncomputable")
        self.assertEqual(compile_error[1], ["a", "c"])
        garbage = parse_ir(proc("hello\n", "", returncode=0), ["a"], ranges)
        self.assertEqual(garbage[0]["a"].status, "harness")

    def test_kernel_two_pass(self):
        ranges = {"a": (10, 12), "b": (13, 15), "c": (16, 18), "d": (19, 21)}
        first = parse_kernel(proc("\n".join([
            message(15, "error", DECIDE_REJECTION_PREFIXES[0] + "\n  p\nis false"),
            message(18, "error", DECIDE_REJECTION_PREFIXES[1] + "\n  p\ndid not reduce"),
            message(21, "error", "(deterministic) timeout", "runtime.maxHeartbeats")]) + "\n", returncode=1), ranges)
        self.assertEqual(first["a"], Outcome("kernel-true"))
        self.assertEqual((first["b"], first["c"]), (REJECTED, REJECTED))
        self.assertEqual(first["d"].stage, "heartbeats")
        second = parse_kernel(proc(message(18, "error", DECIDE_REJECTION_PREFIXES[1]) + "\n", returncode=1),
                              {"b": (13, 15), "c": (16, 18)})
        final = combine_kernel(first, second)
        self.assertEqual(final["a"].status, "kernel-true")
        self.assertEqual(final["b"].status, "kernel-false")
        self.assertEqual(final["c"].stage, "kernel-stuck")
        self.assertEqual(combine_kernel({"x": REJECTED}, {})["x"].status, "harness")
        timed = parse_kernel(proc("", returncode=None, timed_out=True), ranges)
        self.assertTrue(all(o.stage == "timeout" for o in timed.values()))  # type: ignore[union-attr]

    def test_message_classification_is_by_kind(self):
        self.assertEqual(harness.classify_error(Message(1, "error", "runtime.maxRecDepth", "x"), "lean-meta").stage,
                         "max-recdepth")
        self.assertEqual(harness.classify_error(Message(1, "error", "[anonymous]", "maximum recursion depth"),
                                                "lean-meta").status, "harness")


class CostTests(unittest.TestCase):
    def test_programs_respect_the_budget(self):
        for budget in (300.0, 3000.0):
            config = GenConfig(budget_ms=budget)
            for index in range(300):
                result = generate(Chooser(seed=program_seed(31, index)), config)
                slack = 12 * 60.0  # mints are always affordable (cheap total fallback)
                self.assertLessEqual(result.cost_ms, budget + slack, result.program.fmt.name)

    def test_pack_is_ordered_and_bounded(self):
        costs = [5.0, 5.0, 20.0, 1.0, 1.0, 1.0, 50.0]
        batches = pack(costs, 21.0, 3)
        self.assertEqual([i for b in batches for i in b], list(range(len(costs))))
        for batch in batches:
            self.assertTrue(len(batch) <= 3 and (len(batch) == 1 or sum(costs[i] for i in batch) <= 21.0))


class NumericTests(unittest.TestCase):
    def test_classify(self):
        b16 = FORMATS["b16"]
        self.assertEqual(classify(Fraction(1025, 1024) + Fraction(1, 2048), b16), {"tie"})
        self.assertEqual(classify(Fraction(3, 2), b16), {"exact"})
        self.assertEqual(classify(Fraction(1, 3), b16), {"inexact"})
        self.assertIn("overflow_range", classify(Fraction(65520), b16))
        self.assertIn("subnormal_range", classify(Fraction(1, 2 ** 20), b16))

    def test_tie_corner_is_confirmed_exactly(self):
        found = 0
        for index in range(40):
            program = generate(Chooser(seed=f"tie:{index}"), GenConfig(force_forms=("corner:tie_plus",),
                                                                        swarm_include=("Bplus", "Bminus"))).program
            stmts = {s.id: s for s in program.stmts}
            corner = next(s for s in program.stmts if s.corner == "tie_plus")
            values = [mint_value(program.fmt, stmts[str(arg.value)]) for arg in corner.args]
            reference = decode({"p": program.fmt.p, "emax": program.fmt.emax, "bindings": [
                {"id": str(a.value), "type": "BSN", "op": "x"} for a in corner.args] + [
                {"id": corner.id, "type": "BSN", "op": corner.op}]},
                [n for v in values for n in v] + [3, 0, 1 << (program.fmt.p - 1), 1 - program.fmt.p])
            tags = numeric_tags(program.with_stmts([stmts[str(a.value)] for a in corner.args] + [corner]), reference)
            found += tags["tie"] + tags["exact"]
            self.assertFalse(tags["inexact"], (program.fmt.name, values, corner.op))
        self.assertEqual(found, 40)


class ShrinkOfflineTests(unittest.TestCase):
    def fake_run(self, programs_: list[Program]):
        out = []
        for program in programs_:
            sig = signature(program)
            doc: list[int] = []
            fmt = program.fmt

            def fill(rows):
                for row in rows:
                    if row["type"] == "branch":
                        doc.append(0)
                        fill(row["arms"][0])
                    else:
                        doc.extend(one_value(fmt) if row["type"] in ("BSN", "SF") else [0])
            fill(sig["bindings"])
            reference = decode(sig, doc)
            target = next((v for v in observe.flatten(reference) if v.op == "Bfma"), None)
            v = (Verdict("lean-meta", "observation-mismatch", divergence={"id": target.id, "op": "Bfma"})
                 if target is not None else Verdict("lean-meta", "match"))
            out.append((v, reference))
        return out

    def test_passes_preserve_types_and_target(self):
        shrunk = 0
        for index in range(25):
            program = generate(Chooser(seed=f"shrink:{index}"),
                               GenConfig(force_ops=("Bfma",), force_forms=("fold", "branch", "select"))).program
            (initial, reference), = self.fake_run([program])
            divergent = str(initial.divergence["id"])  # type: ignore[index]
            check_program(flatten(program, reference))
            result = shrink(program, reference, divergent, Target("lean-meta", "observation-mismatch", "Bfma"),
                            self.fake_run)
            check_program(result.program)
            self.assertTrue(Target("lean-meta", "observation-mismatch", "Bfma").holds(self.fake_run([result.program])[0][0]))
            self.assertLessEqual(len(result.program.stmts), len(program.stmts))
            shrunk += len(result.program.stmts) < len(program.stmts)
            self.assertLessEqual(len(result.program.stmts), 4)
        self.assertGreater(shrunk, 20)

    def test_pin_uses_reference_values(self):
        fmt = FORMATS["t3_4"]
        program = Program(fmt, (Stmt("v0", "op", "BSN", op="Bone"),
                                Stmt("v1", "op", "BSN", op="Bplus", mode=0, args=(Arg.ref("v0"), Arg.ref("v0"))),
                                Stmt("v2", "op", "E", op="Bfrexp.2", args=(Arg.ref("v1"),)),
                                Stmt("v3", "op", "BSN", op="Bldexp", mode=2, args=(Arg.ref("v1"), Arg.ref("v2")))))
        reference = decode(signature(program), [3, 0, 4, -2, 3, 0, 4, -1, 2, 3, 0, 4, 1])
        pinned = pin(cut_after(program, "v3"), "v3", reference)
        check_program(pinned)
        self.assertEqual([s.id for s in pinned.stmts], ["v1", "v3"])
        self.assertEqual(pinned.stmts[0].args, (Arg.sf(3, 0, 4, -1),))
        self.assertEqual(pinned.stmts[1].args, (Arg.ref("v1"), Arg.int_(2)))


# -- live ----------------------------------------------------------------------

FIXTURES = Path(__file__).resolve().parent / "fixtures" / "flocqsmith"


class DescriptorTests(unittest.TestCase):
    def test_op_families_partition_the_signature_table(self):
        check_families()
        self.assertEqual(set(FAMILY_OF), {row.name for row in OPS})
        self.assertEqual(sum(len(ops) for ops in FAMILIES.values()), len(OPS))

    def test_committed_descriptors_load_and_cover_every_format(self):
        for path in sorted(FIXTURES.glob("*.descriptor.json")):
            row, lanes = load_descriptor(path)
            reachable = {name for lane in lanes for name, weight in lane.config.format_weights if weight > 0}
            self.assertEqual(reachable, set(FORMATS), path.name)
            self.assertIn("controls", {lane.kind for lane in lanes}, f"{path.name}: no positive-control lane")

    def test_descriptor_rejects_duplicate_seeds_and_unknown_fields(self):
        base = {"schema": "flocqsmith-campaign-descriptor-v1", "lanes": [
            {"name": "a", "kind": "run", "seed": 1, "n": 1}, {"name": "b", "kind": "run", "seed": 1, "n": 1}]}
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "d.json"
            path.write_text(json.dumps(base))
            with self.assertRaises(ValueError):
                load_descriptor(path)
            base["lanes"] = [{"name": "a", "kind": "run", "seed": 1, "n": 1, "sede": 2}]
            path.write_text(json.dumps(base))
            with self.assertRaises(ValueError):
                load_descriptor(path)
            base["lanes"] = [{"name": "a", "kind": "run", "seed": 1, "n": 1, "controls": ["enc_sign_flip"]}]
            path.write_text(json.dumps(base))
            with self.assertRaises(ValueError):
                load_descriptor(path)

    def test_root_signature_names_the_op_mode_and_differing_fields(self):
        fmt = FORMATS["t3_4"]
        one = Arg.sf(3, 0, 4, -2)
        program = Program(fmt, (Stmt("v0", "op", "BSN", op="SF2B'", args=(one,)),
                                Stmt("v1", "op", "BSN", op="Bplus", mode=4,
                                     args=(Arg.ref("v0"), Arg.ref("v0")))))
        divergence = {"id": "v1", "op": "Bplus", "type": "BSN", "reference": [3, 0, 4, -1], "clone": [3, 1, 4, 0]}
        rows = {"lean-meta": {"path": "lean-meta", "verdict": "observation-mismatch", "divergence": divergence},
                "lean-ir": {"path": "lean-ir", "verdict": "match"},
                "lean-kernel": {"path": "lean-kernel", "verdict": "observation-mismatch"}}
        sig = _root_signature(program, rows, disagree=True)
        self.assertEqual((sig["op"], sig["mode"], sig["fields"], sig["paths"]),
                         ("Bplus", "NA", ["sign", "exponent"], ["lean-kernel", "lean-meta"]))
        self.assertEqual(_signature_key(sig), "Bplus|BSN|sign,exponent|NA|t3_4|lean-kernel+lean-meta")
        kernel_only = {"lean-kernel": {"path": "lean-kernel", "verdict": "observation-mismatch"}}
        self.assertEqual(_root_signature(program, kernel_only, disagree=False)["kind"], "kernel-only")

    def test_committed_minimized_replays_regenerate_their_digests(self):
        for path in sorted((FIXTURES / "replays").glob("*.json")):
            with self.subTest(path.name):
                load_case(json.loads(path.read_text()), from_ir=True)


@unittest.skipUnless(LIVE, "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    """Real Rocq vm_compute and Lean #reduce / lean --run / decide +kernel."""

    @classmethod
    def setUpClass(cls):
        cls.flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cls.tools = Toolchain(cls.flocq, fb.configured_coqc(cls.flocq))

    def test_generator_validity_every_op_form_and_corner_in_both_provers(self):
        names = list(FORMATS)
        configs = [GenConfig(format_weights=((names[k % len(names)], 1),), force_ops=(row.name,), max_size=4)
                   for k, row in enumerate(OPS)]
        forms = ["select", "case4", "fold", "branch", *(f"corner:{c}" for c in CORNERS)]
        configs += [GenConfig(format_weights=((names[(k * 3) % len(names)], 1),), force_forms=(form,), max_size=4)
                    for k, form in enumerate(forms)]
        subjects = [Subject(f"valid{k:02d}", generate(Chooser(seed=f"valid:{k}"), config).program, BASELINE)
                    for k, config in enumerate(configs)]
        covered = Counter()
        for s in subjects:
            covered.update(structural_tags(s.program))
        self.assertTrue(all(covered[f"op:{row.name}"] for row in OPS))
        self.assertTrue(all(covered[f"fmt:{name}"] for name in FORMATS))
        with tempfile.TemporaryDirectory(prefix="flocqsmith-validity-") as directory:
            batch = execute_batch(subjects, Path(directory) / "batch", self.tools)
            self.assertTrue(all(o.status == "ok" for o in batch.rocq.values()), "Rocq rejected a program")
            for case_id, rows in batch.verdicts.items():
                for v in rows:
                    self.assertEqual(v.verdict, "match", (case_id, v.to_json()))
            self.assertEqual(batch.disagreements, [])

    def test_decide_rejection_text_is_pinned(self):
        subject = Subject("pin", Program(FORMATS["t3_4"], (Stmt("v0", "op", "BSN", op="Bone"),)), BASELINE)
        with tempfile.TemporaryDirectory(prefix="flocqsmith-decide-") as directory:
            folder = Path(directory)
            for negated in (False, True):
                lean = harness.kernel_file([subject], {"pin": (3, 0, 5, -2)}, 10 ** 7, "", negated=negated)
                (folder / f"K{negated}.lean").write_text(lean.text)
                result = harness.run_capture(harness._lean(folder / f"K{negated}.lean"), 600)
                got = parse_kernel(result, lean.ranges)["pin"]
                self.assertEqual(got, Outcome("kernel-true") if negated else REJECTED)

    def test_replay_from_record_is_deterministic(self):
        case = new_case(424242, 3, GenConfig(max_size=6))
        with tempfile.TemporaryDirectory(prefix="flocqsmith-replay-") as directory:
            root = Path(directory)
            record = root / "case.json"
            record.write_text(json.dumps(case.to_json()))
            from_tape = load_case(json.loads(record.read_text()))
            self.assertEqual(from_tape.program, case.program)
            self.assertEqual(load_case(json.loads(record.read_text()), from_ir=True).program, case.program)
            reports = [replay(record, self.flocq, root / "tape", allow_dirty=True),
                       replay(record, self.flocq, root / "ir", allow_dirty=True, from_ir=True)]
            self.assertEqual([r["status"] for r in reports], ["passed", "passed"])
            streams = [sorted((root / name / "batches").rglob("rocq.stdout"))[0].read_text() for name in ("tape", "ir")]
            self.assertEqual(streams[0], streams[1])
            tampered = case.to_json()
            tampered["rocq_sha256"] = "0" * 64
            with self.assertRaises(ReplayError):
                load_case(tampered)

    def test_shrinking_preserves_the_verdict(self):
        fmt = FORMATS["t4_8"]
        e = fmt.emin
        stmts = (
            Stmt("v0", "op", "BSN", op="Bone"),
            Stmt("v1", "op", "BSN", op="SF2B'", args=(Arg.sf(3, 0, 13, -3),)),
            Stmt("v2", "op", "BSN", op="binary_normalize", mode=0, args=(Arg.int_(1), Arg.int_(e), Arg.bool_(False))),
            Stmt("v3", "op", "Bool", op="Bltb", args=(Arg.ref("v2"), Arg.ref("v1"))),
            Stmt("v4", "select", "BSN", args=(Arg.ref("v3"), Arg.ref("v2"), Arg.ref("v1"))),
            Stmt("v5", "op", "BSN", op="Bopp", args=(Arg.ref("v4"),)),
            Stmt("v6", "fold", "BSN", op="Bplus", mode=0, args=(Arg.ref("v0"),),
                 steps=((Arg.ref("v1"),), (Arg.ref("v1"),))),
            Stmt("v7", "op", "BSN", op="Bfma", mode=1, args=(Arg.ref("v4"), Arg.ref("v4"), Arg.ref("v5"))),
            Stmt("v8", "op", "BSN", op="Bsqrt", mode=0, args=(Arg.ref("v7"),)),
        )
        case = case_from_program("hand-fma", Program(fmt, stmts), origin="test")
        with tempfile.TemporaryDirectory(prefix="flocqsmith-shrink-") as directory:
            root = Path(directory)
            record = root / "case.json"
            record.write_text(json.dumps(case.to_json()))
            report = shrink_case(record, self.flocq, root / "out", "fma_double_rounding", "lean-meta",
                                 allow_dirty=True)
            self.assertEqual(report["status"], "preserved", json.dumps(report.get("steps"))[:2000])
            self.assertEqual(report["target"], {"path": "lean-meta", "verdict": "observation-mismatch", "op": "Bfma"})
            self.assertEqual(report["final"]["divergence"]["op"], "Bfma")  # type: ignore[index]
            self.assertLess(report["statements_after"], report["statements_before"])
            minimized = json.loads((root / "out" / "minimized.json").read_text())
            self.assertEqual(load_case(minimized).program.stmts[-1].op, "Bfma")
            # The minimized record replays on the unmutated port as an all-path match.
            replayed = replay(root / "out" / "minimized.json", self.flocq, root / "again",
                              controls=("fma_double_rounding",), allow_dirty=True)
            self.assertEqual(replayed["verdicts"], {p: {"match": 1} for p in CLONE_PATHS})
            self.assertEqual(replayed["controls"]["fma_double_rounding"]["detected"], 1)  # type: ignore[index]

    def test_every_positive_control_is_detected(self):
        with tempfile.TemporaryDirectory(prefix="flocqsmith-controls-") as directory:
            names = tuple(c.name for c in CONTROLS)
            report = run_campaign(Options(self.flocq, Path(directory) / "out", seed=5, n=40,
                                          config=GenConfig(), controls=names, allow_dirty=True,
                                          focus_controls=True))
            print("\ncontrol detection (seed 5, n 40, control-focused corpus):", file=sys.stderr)
            controls = report["controls"]
            for name in names:
                row = controls[name]  # type: ignore[index]
                print(f"  {name:26s} exposed {row['exposed']:3d} detected {row['detected']:3d} "
                      f"rate {row['detection_rate']} first {row['cases_to_first_detection']} "
                      f"paths {row['detected_by_path']}", file=sys.stderr)
                self.assertGreater(row["detected"], 0, name)
                self.assertEqual(row["non_mismatch_verdicts"], {}, name)
                self.assertTrue(row["ok"], name)
            self.assertEqual(report["mismatches"], [])
            self.assertEqual(report["infra"], [])
            self.assertEqual(report["harness_errors"], [])
            self.assertEqual(report["verdicts"], {p: {"match": 40} for p in CLONE_PATHS})

    def test_verify_rejudges_and_detects_tampering(self):
        with tempfile.TemporaryDirectory(prefix="flocqsmith-verify-") as directory:
            out = Path(directory) / "out"
            report = run_campaign(Options(self.flocq, out, seed=99, n=6, controls=("enc_sign_flip",),
                                          allow_dirty=True))
            self.assertEqual(report["status"], "passed")
            self.assertEqual(verify(out)["status"], "verified")
            stream = next(out.glob("batches/batch_*/meta.stdout"))
            text = stream.read_text()
            stream.write_text(text.replace("Int.ofNat 3,", "Int.ofNat 2,", 1))
            result = verify(out)
            self.assertEqual(result["status"], "failed")
            self.assertTrue(any("digest mismatch" in p for p in result["problems"]))
            self.assertTrue(any("re-judged verdicts differ" in p for p in result["problems"]))


if __name__ == "__main__":
    unittest.main()
