"""flocqsmith regressions (generator layer).

Offline tests cover the signature table, format arithmetic, the draw tape
(deterministic replay, typed replay errors and the mutated-tape sweep), IR
typing, observation decoding, the cost model and exact numeric tags.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import json
import random
import unittest

from flocqsmith import observe
from flocqsmith.choose import Chooser, Draw, GeneratorBug, ReplayError
from flocqsmith.cost import pack
from flocqsmith.formats import FORMATS, Format
from flocqsmith.generate import CORNERS, GenConfig, generate, program_seed
from flocqsmith.ir import Arg, IRError, Program, Stmt, check_program, signature
from flocqsmith.numeric import classify, numeric_tags, structural_tags
from flocqsmith.observe import DecodeError, decode
from flocqsmith.render import lean_term, rocq_term
from flocqsmith.table import LEAN_ALLOWED_PREFIXES, LEAN_FORBIDDEN, OPS, check_table


def programs(seed: int, count: int, config: GenConfig | None = None) -> list[tuple[Chooser, Program]]:
    out = []
    for index in range(count):
        chooser = Chooser(seed=program_seed(seed, index))
        out.append((chooser, generate(chooser, config or GenConfig()).program))
    return out


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


if __name__ == "__main__":
    unittest.main()
