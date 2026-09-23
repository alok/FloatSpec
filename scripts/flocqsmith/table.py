"""The signature table: one row per executable BinarySingleNaN export (§3.3).

Both renderers read only this table. A row records the argument and result IR
types, the Lean and Rocq templates (each with its own argument order and proof
arguments), an optional source-facade Lean spelling, the Flocq source anchor
and a cost class. Placeholders: ``{p}``/``{e}`` (precision/emax), ``{m}``
(mode), ``{sm}`` (source-facade mode), ``{a0}``.. (rendered arguments).

Trap rows paid for once (see FLOCQSMITH.md §3.3): Rocq needs
``Prec_gt_0``/``Prec_lt_emax`` proofs as ``eq_refl`` while Lean resolves
instances from a ``letI`` prefix; ``Bnearbyint`` takes only ``Prec_lt_emax``
and ``Bfrexp`` only ``Prec_gt_0``; ``Bopp``/``Babs``/``Btrunc``/``B2SF`` and
the predicates take no proofs; ``Bnormfr_mantissa`` returns ``Nat``/``N``.
"""

from __future__ import annotations

from dataclasses import dataclass

# IR value types. Mode and Pos only occur as literal arguments.
VALUE_TYPES = ("BSN", "SF", "Z", "E", "N", "Bool", "Cmp")
LITERAL_TYPES = ("Z", "E", "Bool", "Pos", "SF")

LEAN_MODES = (".RNE", ".RTZ", ".RTN", ".RTP", ".RNA")
LEAN_SOURCE_MODES = (".mode_NE", ".mode_ZR", ".mode_DN", ".mode_UP", ".mode_NA")
ROCQ_MODES = ("mode_NE", "mode_ZR", "mode_DN", "mode_UP", "mode_NA")
MODE_NAMES = ("NE", "ZR", "DN", "UP", "NA")

PP = "{p} {e} eq_refl eq_refl"
BSN = "BinarySingleNaN"
SOURCE = "FloatSpec.IEEE754.BinarySingleNaN.Source"

# Lean namespaces the renderer may emit (§3.6). Anything else fails the
# allowlist test at table-build time.
LEAN_ALLOWED_PREFIXES = (f"{BSN}.", f"{SOURCE}.", "FlocqsmithMutant.")
# Root Binary754 operations, Binary32/Binary64 and bridge namespaces are
# noncomputable or differently typed duplicates and must never be emitted.
LEAN_FORBIDDEN = ("Binary32", "Binary64", "BinarySingleNaNBridge.", "ExperimentalBinaryRound.",
                  "ExperimentalSingleNaNArithmetic.", "_root_.")


@dataclass(frozen=True)
class OpRow:
    name: str
    args: tuple[str, ...]
    result: str
    has_mode: bool
    lean: str
    rocq: str
    source: str
    cost: str
    lean_source: str | None = None

    @property
    def lean_head(self) -> str:
        return self.lean.lstrip("(").split()[0]


def _arith(name: str, arity: int, line: int, cost: str) -> OpRow:
    args = " ".join(f"{{a{k}}}" for k in range(arity))
    return OpRow(name, ("BSN",) * arity, "BSN", True,
                 f"{BSN}.{name} {{m}} {args}", f"@{BSN}.{name} {PP} {{m}} {args}",
                 f"src/IEEE754/BinarySingleNaN.v:{line} {name}", cost,
                 f"{SOURCE}.{name} {{sm}} {args}")


def _unary(name: str, line: int, proofs: bool, cost: str = "unary") -> OpRow:
    rocq = f"@{BSN}.{name} {PP} {{a0}}" if proofs else f"@{BSN}.{name} {{p}} {{e}} {{a0}}"
    return OpRow(name, ("BSN",), "BSN", False, f"{BSN}.{name} {{a0}}", rocq,
                 f"src/IEEE754/BinarySingleNaN.v:{line} {name}", cost)


def _predicate(name: str, line: int, arity: int = 1) -> OpRow:
    args = " ".join(f"{{a{k}}}" for k in range(arity))
    return OpRow(name, ("BSN",) * arity, "Bool", False, f"{BSN}.{name} {args}",
                 f"@{BSN}.{name} {{p}} {{e}} {args}", f"src/IEEE754/BinarySingleNaN.v:{line} {name}", "unary")


OPS: tuple[OpRow, ...] = (
    _arith("Bplus", 2, 1940, "gap"),
    _arith("Bminus", 2, 2042, "gap"),
    _arith("Bmult", 2, 1578, "arith"),
    _arith("Bdiv", 2, 2307, "div"),
    _arith("Bfma", 3, 2094, "gap"),
    _arith("Bsqrt", 1, 2466, "div"),
    _unary("Bopp", 445, proofs=False),
    _unary("Babs", 497, proofs=False),
    _unary("erase", 424, proofs=False),
    _unary("Bsucc", 3242, proofs=True),
    _unary("Bpred", 3412, proofs=True),
    _unary("Bulp", 3099, proofs=True),
    _unary("Bsucc'", 3661, proofs=True),
    _unary("Bpred_pos'", 3453, proofs=True),
    _unary("Bulp'", 3173, proofs=True),
    OpRow("Bldexp", ("BSN", "E"), "BSN", True, f"{BSN}.Bldexp {{m}} {{a0}} {{a1}}",
          f"@{BSN}.Bldexp {PP} {{m}} {{a0}} {{a1}}", "src/IEEE754/BinarySingleNaN.v:2857 Bldexp", "ldexp"),
    OpRow("Bfrexp.1", ("BSN",), "BSN", False, f"({BSN}.Bfrexp {{a0}}).1",
          f"fst (@{BSN}.Bfrexp {{p}} {{e}} eq_refl {{a0}})", "src/IEEE754/BinarySingleNaN.v:3042 Bfrexp", "unary"),
    OpRow("Bfrexp.2", ("BSN",), "E", False, f"({BSN}.Bfrexp {{a0}}).2",
          f"snd (@{BSN}.Bfrexp {{p}} {{e}} eq_refl {{a0}})", "src/IEEE754/BinarySingleNaN.v:3042 Bfrexp", "unary"),
    OpRow("Bnearbyint", ("BSN",), "BSN", True, f"{BSN}.Bnearbyint {{m}} {{a0}}",
          f"@{BSN}.Bnearbyint {{p}} {{e}} eq_refl {{m}} {{a0}}", "src/IEEE754/BinarySingleNaN.v:2653 Bnearbyint",
          "ldexp"),
    OpRow("Btrunc", ("BSN",), "Z", False, f"{BSN}.Btrunc {{a0}}", f"@{BSN}.Btrunc {{p}} {{e}} {{a0}}",
          "src/IEEE754/BinarySingleNaN.v:2680 Btrunc", "ldexp"),
    OpRow("Bone", (), "BSN", False, f"{BSN}.Bone (prec := {{p}}) (emax := {{e}})", f"@{BSN}.Bone {PP}",
          "src/IEEE754/BinarySingleNaN.v:2723 Bone", "mint"),
    OpRow("Bmax_float", (), "BSN", False, f"{BSN}.Bmax_float (prec := {{p}}) (emax := {{e}})",
          f"@{BSN}.Bmax_float {PP}", "src/IEEE754/BinarySingleNaN.v:2816 Bmax_float", "mint"),
    OpRow("binary_normalize", ("Z", "E", "Bool"), "BSN", True,
          f"{BSN}.binary_normalize (prec := {{p}}) (emax := {{e}}) {{m}} {{a0}} {{a1}} {{a2}}",
          f"@{BSN}.binary_normalize {PP} {{m}} {{a0}} {{a1}} {{a2}}",
          "src/IEEE754/BinarySingleNaN.v:1751 binary_normalize", "normalize"),
    OpRow("SF2B'", ("SF",), "BSN", False, f"{BSN}.SF2B' (prec := {{p}}) (emax := {{e}}) {{a0}}",
          f"@{BSN}.SF2B' {{p}} {{e}} {{a0}}", "src/IEEE754/BinarySingleNaN.v:73 SF2B'", "mint"),
    OpRow("B2SF", ("BSN",), "SF", False, f"{BSN}.B2SF {{a0}}", f"@{BSN}.B2SF {{p}} {{e}} {{a0}}",
          "src/IEEE754/BinarySingleNaN.v:85 B2SF", "unary"),
    OpRow("binary_round", ("Bool", "Pos", "E"), "SF", True,
          f"{BSN}.binary_round (prec := {{p}}) (emax := {{e}}) {{m}} {{a0}} {{a1}} {{a2}}",
          f"@{BSN}.binary_round {{p}} {{e}} {{m}} {{a0}} {{a1}} {{a2}}",
          "src/IEEE754/BinarySingleNaN.v:1701 binary_round", "normalize"),
    _predicate("Beqb", 628, 2),
    _predicate("Bltb", 652, 2),
    _predicate("Bleb", 666, 2),
    OpRow("Bcompare", ("BSN", "BSN"), "Cmp", False, f"{BSN}.Bcompare {{a0}} {{a1}}",
          f"@{BSN}.Bcompare {{p}} {{e}} {{a0}} {{a1}}", "src/IEEE754/BinarySingleNaN.v:559 Bcompare", "unary"),
    _predicate("Bsign", 327),
    _predicate("is_nan", 398),
    _predicate("is_finite", 350),
    _predicate("is_finite_strict", 262),
    OpRow("Bfma_szero", ("BSN", "BSN", "BSN"), "Bool", True, f"{BSN}.Bfma_szero {{m}} {{a0}} {{a1}} {{a2}}",
          f"@{BSN}.Bfma_szero {{p}} {{e}} {{m}} {{a0}} {{a1}} {{a2}}", "src/IEEE754/BinarySingleNaN.v:2089 Bfma_szero",
          "unary"),
    OpRow("Bnormfr_mantissa", ("BSN",), "N", False, f"{BSN}.Bnormfr_mantissa {{a0}}",
          f"@{BSN}.Bnormfr_mantissa {{p}} {{e}} {{a0}}", "src/IEEE754/BinarySingleNaN.v:2820 Bnormfr_mantissa", "unary"),
)

OP_BY_NAME: dict[str, OpRow] = {row.name: row for row in OPS}

# Fold accumulator shapes (§3.2): op, position of the accumulator among the
# op's BSN arguments, and the extra argument types consumed per step.
FOLD_SHAPES: dict[str, tuple[int, tuple[str, ...]]] = {
    "Bplus": (0, ("BSN",)),
    "Bmult": (0, ("BSN",)),
    "Bfma": (2, ("BSN", "BSN")),
    "Bsucc": (0, ()),
    "Bpred": (0, ()),
    "Bldexp": (0, ("E",)),
}

# Observers: IR type -> (Lean, Rocq) templates producing a list of integers.
# Widths are fixed per type; decoding is by the observation signature.
OBSERVERS: dict[str, tuple[str, str, int]] = {
    "BSN": (f"standard ({BSN}.B2SF {{v}})", f"standard (@{BSN}.B2SF {{p}} {{e}} {{v}})", 4),
    "SF": ("standard {v}", "standard {v}", 4),
    "Z": ("[{v}]", "[{v}]", 1),
    "E": ("[{v}]", "[{v}]", 1),
    "N": ("[({v} : Int)]", "[Z.of_N {v}]", 1),
    "Bool": ("[boolean {v}]", "[boolean {v}]", 1),
    "Cmp": ("[({v}.map comparisonCode).getD 2]", "[comparison_code {v}]", 1),
}

# Lean type ascriptions for bindings whose type is not inferable from use.
LEAN_TYPES: dict[str, str] = {
    "BSN": "BinarySingleNaN.binary_float {p} {e}", "SF": "StandardFloat", "Z": "Int", "E": "Int",
    "N": "Nat", "Bool": "Bool", "Cmp": "Option Ordering",
}
ROCQ_TYPES: dict[str, str] = {
    "BSN": "BinarySingleNaN.binary_float {p} {e}", "SF": "SpecFloat.spec_float", "Z": "Z", "E": "Z",
    "N": "N", "Bool": "bool", "Cmp": "option comparison",
}


def check_table() -> None:
    """Static allowlist and shape checks; raises on any violation (§3.6)."""
    seen: set[str] = set()
    for row in OPS:
        if row.name in seen:
            raise AssertionError(f"duplicate op {row.name}")
        seen.add(row.name)
        for template in (row.lean, row.lean_source or row.lean):
            head = template.lstrip("(").split()[0]
            if not head.startswith(LEAN_ALLOWED_PREFIXES):
                raise AssertionError(f"{row.name}: Lean head {head} outside the allowlist")
            if any(bad in template for bad in LEAN_FORBIDDEN):
                raise AssertionError(f"{row.name}: forbidden Lean name in {template}")
        for template in (row.lean, row.rocq, row.lean_source or ""):
            for k in range(len(row.args)):
                if template and template.count(f"{{a{k}}}") != 1:
                    raise AssertionError(f"{row.name}: argument {k} must occur once in {template}")
        if row.has_mode != ("{m}" in row.lean) or row.has_mode != ("{m}" in row.rocq):
            raise AssertionError(f"{row.name}: mode placeholder disagrees with has_mode")
        if row.result not in VALUE_TYPES or any(a not in VALUE_TYPES + ("Pos",) for a in row.args):
            raise AssertionError(f"{row.name}: unknown type")
    for op, (acc, extra) in FOLD_SHAPES.items():
        row = OP_BY_NAME[op]
        bsn_args = [a for a in row.args if a == "BSN"]
        if row.result != "BSN" or acc >= len(row.args) or row.args[acc] != "BSN" or len(row.args) != 1 + len(extra):
            raise AssertionError(f"fold shape {op} disagrees with the table")
        del bsn_args
