"""The program generator (FLOCQSMITH.md §3, §4, §13).

Programs are valid by construction: every argument is either an in-scope
binding of the right type or a total literal mint, every draw goes through
:class:`~flocqsmith.choose.Chooser`, and every op is priced at emission.
There are no rejection loops.

Values are biased to boundaries: each leaf draws a class from the format
catalogue (zeros, infinities, NaN, subnormal edges, 1 and its neighbours, the
maximum finite value, powers of two, half-integers, random normal and
subnormal values) and about one step in eight is a *relational corner* that
constructs operands with a known relationship (a tie, a cancellation, an
overflow edge, a tiny product, an equal pair, a sticky-bit gap).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable

from .choose import Chooser, GeneratorBug
from .cost import Info, op_cost, result_info
from .formats import DEFAULT_FORMAT_WEIGHTS, FORMATS, Format
from .ir import Arg, Program, Stmt, check_program, e_bound
from .numeric import round_ne
from .table import FOLD_SHAPES, OP_BY_NAME, OPS

FORMS = ("op", "corner", "select", "case4", "fold", "branch")


@dataclass(frozen=True)
class GenConfig:
    format_weights: tuple[tuple[str, int], ...] = tuple(DEFAULT_FORMAT_WEIGHTS.items())
    min_size: int = 4
    max_size: int = 12
    budget_ms: float = 3000.0
    force_ops: tuple[str, ...] = ()
    force_forms: tuple[str, ...] = ()
    corner_weight: int = 2
    op_weight: int = 12
    swarm_include: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not 1 <= self.min_size <= self.max_size:
            raise ValueError("need 1 <= min_size <= max_size")
        for name, weight in self.format_weights:
            if name not in FORMATS or weight < 0:
                raise ValueError(f"bad format weight {name}={weight}")
        for op in self.force_ops + self.swarm_include:
            if op not in OP_BY_NAME:
                raise ValueError(f"unknown op {op}")
        for form in self.force_forms:
            if form not in FORMS and not (form.startswith("corner:") and form[7:] in CORNERS):
                raise ValueError(f"unknown forced form {form}")

    def to_json(self) -> dict[str, object]:
        return {"format_weights": dict(self.format_weights), "min_size": self.min_size,
                "max_size": self.max_size, "budget_ms": self.budget_ms, "force_ops": list(self.force_ops),
                "force_forms": list(self.force_forms), "corner_weight": self.corner_weight,
                "op_weight": self.op_weight, "swarm_include": list(self.swarm_include)}

    @staticmethod
    def from_json(row: dict[str, object]) -> "GenConfig":
        weights = row["format_weights"]
        assert isinstance(weights, dict)
        return GenConfig(tuple((str(k), int(v)) for k, v in weights.items()), int(row["min_size"]),  # type: ignore[call-overload]
                         int(row["max_size"]), float(row["budget_ms"]),  # type: ignore[arg-type,call-overload]
                         tuple(row["force_ops"]), tuple(row["force_forms"]),  # type: ignore[arg-type]
                         int(row["corner_weight"]), int(row["op_weight"]),  # type: ignore[call-overload]
                         tuple(row.get("swarm_include", ())))  # type: ignore[arg-type]


@dataclass
class GenResult:
    program: Program
    cost_ms: float
    swarm: tuple[str, ...]
    modes: tuple[int, ...]


# Relational corners: name -> ops that realize it (legal if any is in the swarm).
CORNERS: dict[str, tuple[str, ...]] = {
    "tie_plus": ("Bplus", "Bminus"),
    "tie_mult": ("Bmult",),
    "cancel": ("Bplus", "Bminus", "Bfma"),
    "overflow_edge": ("Bplus", "Bmult"),
    "tiny": ("Bmult", "Bdiv"),
    "equal_pair": ("Beqb", "Bltb", "Bleb", "Bcompare"),
    "half_int": ("Bnearbyint", "Btrunc"),
    "max_succ": ("Bsucc", "Bsucc'", "Bpred"),
    "sticky_gap": ("Bplus", "Bminus", "Bfma"),
    "fma_error": ("Bfma",),
}


# Mode weights (NE, ZR, DN, UP, NA) per corner.
CORNER_MODES: dict[str, tuple[int, int, int, int, int]] = {
    "tie_plus": (6, 1, 1, 1, 3), "tie_mult": (6, 1, 1, 1, 3), "cancel": (1, 1, 4, 1, 1),
    "overflow_edge": (1, 4, 2, 2, 1), "half_int": (3, 1, 1, 1, 4),
}
# Relative corner weights; ties and the rounding-direction corners dominate.
CORNER_WEIGHTS: dict[str, int] = {"tie_plus": 3, "tie_mult": 2, "cancel": 2, "overflow_edge": 2, "fma_error": 2,
                                  "half_int": 2}


@dataclass
class _Block:
    stmts: list[Stmt] = field(default_factory=list)
    scope: dict[str, Info] = field(default_factory=dict)
    prefix: str = "v"
    counter: int = 0


class Generator:
    def __init__(self, chooser: Chooser, config: GenConfig) -> None:
        self.c = chooser
        self.config = config
        weights = dict(config.format_weights)
        self.fmt: Format = self.c.choose("format", [(FORMATS[name], weights.get(name, 0)) for name in FORMATS])
        self.swarm = self._draw_swarm()
        self.modes = self._draw_modes()
        self.budget = config.budget_ms
        self.spent = 0.0
        self.block = _Block()

    # -- swarm -----------------------------------------------------------------

    def _draw_swarm(self) -> tuple[str, ...]:
        chosen = []
        for row in OPS:
            forced = row.name in self.config.force_ops or row.name in self.config.swarm_include
            if self.c.choose(f"swarm.{row.name}", [(True, 1), (False, 0 if forced else 1)]):
                chosen.append(row.name)
        return tuple(chosen)

    def _draw_modes(self) -> tuple[int, ...]:
        modes = [m for m in range(5) if self.c.coin(f"modes.{m}", 1, 2)]
        if not modes:
            modes = [self.c.below("modes.fallback", 5)]
        return tuple(modes)

    def mode(self) -> int:
        return self.c.choose("mode", [(m, 1 if m in self.modes else 0) for m in range(5)])

    def corner_mode(self, corner: str) -> int:
        """Corners draw from all five modes, biased to the mode that makes them bite.

        A tie separates NE from NA, an exact cancellation's zero sign depends
        on DN, and an overflow edge separates ZR/DN/UP from the nearest modes.
        """
        bias = CORNER_MODES.get(corner, (1, 1, 1, 1, 1))
        return self.c.choose(f"{corner}.mode", list(zip(range(5), bias)))

    # -- bookkeeping -----------------------------------------------------------

    def fresh(self) -> str:
        name = f"{self.block.prefix}{self.block.counter}"
        self.block.counter += 1
        return name

    def emit(self, stmt: Stmt, info: Info, cost: float) -> str:
        self.block.stmts.append(stmt)
        self.block.scope[stmt.id] = info
        self.spent += cost
        return stmt.id

    def remaining(self) -> float:
        return self.budget - self.spent

    def bindings(self, type_: str) -> list[str]:
        return [name for name, info in self.block.scope.items() if info.type == type_]

    # -- literal mints ---------------------------------------------------------

    def finite_class(self, site: str) -> tuple[int, int, int]:
        """A canonical finite value (sign, m, e) from the boundary catalogue."""
        f = self.fmt
        p, emin, top = f.p, f.emin, f.emax_field
        classes: list[tuple[Callable[[], tuple[int, int]], int]] = [
            (lambda: (1 << (p - 1), 1 - p), 2),                        # one
            (lambda: ((1 << p) - 1, top), 2),                          # max finite
            (lambda: (1, emin), 2),                                    # min subnormal
            (lambda: ((1 << (p - 1)) - 1, emin), 1 if p >= 2 else 0),  # max subnormal
            (lambda: (1 << (p - 1), emin), 2),                         # min normal
            (lambda: ((1 << (p - 1)) + 1, 1 - p), 1 if p >= 2 else 0), # one + ulp
            (lambda: ((1 << p) - 1, -p), 1 if -p >= emin else 0),      # one - ulp/2
            (lambda: (1 << (p - 1), self.c.randint(f"{site}.pow2", emin, top)), 2),
            (lambda: self._small_int(site), 3),
            (lambda: self._half_int(site), 2),
            (lambda: (self.c.randint(f"{site}.m", 1 << (p - 1), (1 << p) - 1),
                      self.c.randint(f"{site}.e", emin, top)), 6),       # random normal
            (lambda: (self.c.randint(f"{site}.sm", 1, max(1, (1 << (p - 1)) - 1)), emin), 2 if p >= 2 else 0),
            (lambda: (self.c.randint(f"{site}.cm", 1 << (p - 1), (1 << p) - 1),
                      self.c.randint(f"{site}.ce", max(emin, -p - 2), min(top, 2))), 4),  # near one
        ]
        make = self.c.choose(f"{site}.class", classes)
        m, e = make()
        canonical = f.canonical(m, e)
        if canonical is None:
            raise GeneratorBug(f"catalogue produced unrepresentable ({m}, {e}) in {f.name}")
        sign = self.c.below(f"{site}.sign", 2)
        return sign, canonical[0], canonical[1]

    def _small_int(self, site: str) -> tuple[int, int]:
        high = min((1 << self.fmt.p) - 1, 15, (1 << max(self.fmt.emax - 1, 0)) - 1)
        return self.c.randint(f"{site}.int", 1, max(1, high)), 0

    def _half_int(self, site: str) -> tuple[int, int]:
        """An odd multiple of 1/2 when the format has one, else the integer 1."""
        high = min((1 << self.fmt.p) - 1, 31)
        if self.fmt.emin > -1:
            return 1, 0
        k = self.c.randint(f"{site}.half", 0, (high - 1) // 2)
        return 2 * k + 1, -1

    def mint_value(self, site: str, sign: int, m: int, e: int, *, allow_named: bool = True) -> str:
        """Emit a mint statement for the exact finite value (sign, m, e)."""
        f = self.fmt
        canonical = f.canonical(m, e)
        if canonical is None:
            raise GeneratorBug(f"mint of unrepresentable value in {f.name}")
        m, e = canonical
        info = Info.point(f, sign, m, e)
        is_one = sign == 0 and (m, e) == (1 << (f.p - 1), 1 - f.p)
        is_max = sign == 0 and (m, e) == ((1 << f.p) - 1, f.emax_field)
        arms: list[tuple[str, int]] = [("sf", 2), ("normalize", 2),
                                       ("Bone", 3 if is_one and allow_named else 0),
                                       ("Bmax_float", 3 if is_max and allow_named else 0)]
        how = self.c.choose(f"{site}.ctor", arms)
        name = self.fresh()
        if how == "sf":
            stmt = Stmt(name, "op", "BSN", op="SF2B'", args=(Arg.sf(3, sign, m, e),))
        elif how == "normalize":
            mode = self.mode()
            stmt = Stmt(name, "op", "BSN", op="binary_normalize", mode=mode,
                        args=(Arg.int_(-m if sign else m), Arg.int_(e), Arg.bool_(bool(sign))))
        else:
            stmt = Stmt(name, "op", "BSN", op=how)
        return self.emit(stmt, info, op_cost(stmt.op or "", f, [], [e]))

    def mint_special(self, site: str, kind: int, sign: int) -> str:
        f = self.fmt
        name = self.fresh()
        if kind == 0 and self.c.coin(f"{site}.zero_ctor", 1, 3):
            e = self.c.randint(f"{site}.zero_e", f.emin, f.emax_field)
            stmt = Stmt(name, "op", "BSN", op="binary_normalize", mode=self.mode(),
                        args=(Arg.int_(0), Arg.int_(e), Arg.bool_(bool(sign))))
        else:
            stmt = Stmt(name, "op", "BSN", op="SF2B'", args=(Arg.sf(kind, sign if kind != 2 else 0, 1, 0),))
        exponent = int(stmt.args[1].value) if stmt.op == "binary_normalize" else 0  # type: ignore[call-overload]
        return self.emit(stmt, Info("BSN", f.emin, f.emin, finite=False), op_cost(stmt.op or "", f, [], [exponent]))

    def mint_bsn(self, site: str) -> str:
        f = self.fmt
        which = self.c.choose(f"{site}.leaf", [("zero", 3), ("inf", 2), ("nan", 1), ("finite", 16),
                                               ("noncanonical", 1)])
        if which == "zero":
            return self.mint_special(site, 0, self.c.below(f"{site}.zsign", 2))
        if which == "inf":
            return self.mint_special(site, 1, self.c.below(f"{site}.isign", 2))
        if which == "nan":
            return self.mint_special(site, 2, 0)
        if which == "noncanonical":
            m = self.c.randint(f"{site}.ncm", 1, 1 << (f.p + 2))
            e = self.c.randint(f"{site}.nce", f.emin - 3, f.emax_field + 3)
            sign = self.c.below(f"{site}.ncs", 2)
            name = self.fresh()
            stmt = Stmt(name, "op", "BSN", op="SF2B'", args=(Arg.sf(3, sign, m, e),))
            info = Info.point(f, sign, m, e) if f.is_canonical(m, e) else Info("BSN", f.emin, f.emin, finite=False)
            return self.emit(stmt, info, op_cost("SF2B'", f, [], [e]))
        sign, m, e = self.finite_class(site)
        return self.mint_value(site, sign, m, e)

    # -- arguments -------------------------------------------------------------

    def _existing(self, type_: str) -> list[tuple[str | None, int]]:
        names = self.bindings(type_)
        return [(name, 4 if index >= len(names) - 2 else 2) for index, name in enumerate(names)]

    def arg(self, site: str, type_: str) -> Arg:
        f = self.fmt
        if type_ == "BSN":
            name = self.c.choose(f"{site}.bsn", self._existing("BSN") + [(None, 3)])
            return Arg.ref(name if name is not None else self.mint_bsn(site))
        if type_ == "E":
            name = self.c.choose(f"{site}.e", self._existing("E") + [(None, 3)])
            if name is not None:
                return Arg.ref(name)
            bound = e_bound(f)
            span = self.c.choose(f"{site}.eclass", [("small", 3), ("range", 2), ("extreme", 1)])
            if span == "small":
                return Arg.int_(self.c.randint(f"{site}.es", -4, 4))
            if span == "range":
                return Arg.int_(self.c.randint(f"{site}.er", f.emin - f.p, f.emax))
            return Arg.int_(self.c.randint(f"{site}.ex", -bound, bound))
        if type_ == "Z":
            name = self.c.choose(f"{site}.z", self._existing("Z") + [(None, 3)])
            if name is not None:
                return Arg.ref(name)
            if self.c.coin(f"{site}.zsmall", 2, 3):
                return Arg.int_(self.c.randint(f"{site}.zs", -20, 20))
            return Arg.int_(self.c.randint(f"{site}.zl", -(1 << (f.p + 3)), 1 << (f.p + 3)))
        if type_ == "Bool":
            name = self.c.choose(f"{site}.b", self._existing("Bool") + [(None, 2)])
            return Arg.ref(name) if name is not None else Arg.bool_(self.c.coin(f"{site}.bl", 1, 2))
        if type_ == "Pos":
            return Arg.pos(self.c.randint(f"{site}.pos", 1, 1 << (f.p + 2)))
        if type_ == "SF":
            name = self.c.choose(f"{site}.sf", self._existing("SF") + [(None, 2)])
            if name is not None:
                return Arg.ref(name)
            kind = self.c.choose(f"{site}.sfk", [(0, 1), (1, 1), (2, 1), (3, 5)])
            sign = self.c.below(f"{site}.sfs", 2)
            if kind != 3:
                return Arg.sf(kind, sign if kind != 2 else 0, 1, 0)
            if self.c.coin(f"{site}.sfcanon", 7, 8):
                s, m, e = self.finite_class(f"{site}.sfv")
                return Arg.sf(3, s, m, e)
            return Arg.sf(3, sign, self.c.randint(f"{site}.sfm", 1, 1 << (f.p + 2)),
                          self.c.randint(f"{site}.sfe", f.emin - 3, f.emax_field + 3))
        raise GeneratorBug(f"no argument generator for {type_}")

    def info_of(self, arg: Arg, type_: str) -> Info:
        if arg.kind == "ref":
            return self.block.scope[str(arg.value)]
        return Info(type_)

    # -- statement forms -------------------------------------------------------

    def worst_cost(self, op: str) -> float:
        row = OP_BY_NAME[op]
        full = Info.full(self.fmt)
        return op_cost(op, self.fmt, [full if a == "BSN" else Info(a) for a in row.args],
                       [None for a in row.args if a == "E"])

    def affordable(self, op: str) -> bool:
        # Mints are always affordable: they are the cheap total fallback (§3.4).
        return OP_BY_NAME[op].cost == "mint" or self.worst_cost(op) <= self.remaining()

    def apply(self, op: str, site: str, corner: str | None = None, args: list[Arg] | None = None,
              mode: int | None = None) -> str:
        row = OP_BY_NAME[op]
        if args is None:
            args = [self.arg(f"{site}.a{k}", t) for k, t in enumerate(row.args)]
        if row.has_mode and mode is None:
            mode = self.mode()
        spelling = "core"
        if row.lean_source is not None:
            spelling = self.c.choose(f"{site}.spelling", [("core", 3), ("source", 1)])
        infos = [self.info_of(a, t) for a, t in zip(args, row.args)]
        exponents: list[int | None] = [int(a.value) if a.kind == "int" else None  # type: ignore[call-overload]
                                       for a, t in zip(args, row.args) if t == "E"]
        cost = op_cost(op, self.fmt, infos, exponents)
        stmt = Stmt(self.fresh(), "op", row.result, op=op, mode=mode if row.has_mode else None,
                    spelling=spelling, args=tuple(args), corner=corner)
        return self.emit(stmt, result_info(op, self.fmt, infos), cost)

    def step_op(self, forced: str | None = None) -> None:
        if forced is not None:
            self.apply(forced, "op")
            return
        arms = [(row.name, (3 if row.cost in ("gap", "arith", "div") else 1)
                 if row.name in self.swarm and self.affordable(row.name) else 0) for row in OPS]
        if sum(w for _, w in arms) == 0:
            arms = [(row.name, 1 if row.cost == "mint" else 0) for row in OPS]
        self.apply(self.c.choose("op", arms), "op")

    def step_select(self) -> None:
        types = sorted({info.type for info in self.block.scope.values()})
        type_ = self.c.choose("select.type", [(t, 3 if t == "BSN" else 1) for t in types])
        cond = self.arg("select.c", "Bool")
        names = self.bindings(type_)
        a = self.c.choose("select.a", [(n, 1) for n in names])
        b = self.c.choose("select.b", [(n, 1) for n in names])
        info = self.block.scope[a].union(self.block.scope[b])
        stmt = Stmt(self.fresh(), "select", type_, args=(cond, Arg.ref(a), Arg.ref(b)))
        self.emit(stmt, info, 1.0)

    def step_case4(self) -> None:
        x, y = self.arg("case4.x", "BSN"), self.arg("case4.y", "BSN")
        types = sorted({info.type for info in self.block.scope.values()})
        type_ = self.c.choose("case4.type", [(t, 3 if t == "BSN" else 1) for t in types])
        names = self.bindings(type_)
        picks = [self.c.choose(f"case4.arm{k}", [(n, 1) for n in names]) for k in range(4)]
        info = self.block.scope[picks[0]]
        for name in picks[1:]:
            info = info.union(self.block.scope[name])
        stmt = Stmt(self.fresh(), "case4", type_, args=(x, y, *(Arg.ref(n) for n in picks)))
        self.emit(stmt, info, op_cost("Bcompare", self.fmt, [], []))

    def step_fold(self, any_op: bool = False) -> None:
        ops = sorted(FOLD_SHAPES)
        op = self.c.choose("fold.op", [(o, 1 if (any_op or o in self.swarm) and self.affordable(o) else 0)
                                       for o in ops])
        row = OP_BY_NAME[op]
        _, extra = FOLD_SHAPES[op]
        acc = self.arg("fold.acc", "BSN")
        mode = self.mode() if row.has_mode else None
        per_step = self.worst_cost(op)
        max_k = max(1, min(6, int(self.remaining() // max(per_step, 1.0))))
        k = self.c.randint("fold.k", 1 if max_k == 1 else 2, max_k)
        steps = tuple(tuple(self.arg(f"fold.s{i}.a{j}", t) for j, t in enumerate(extra)) for i in range(k))
        stmt = Stmt(self.fresh(), "fold", "BSN", op=op, mode=mode, args=(acc,), steps=steps)
        self.emit(stmt, Info.full(self.fmt), per_step * k)

    def step_branch(self) -> None:
        cond = self.arg("branch.c", "Bool")
        outer = self.block
        name = self.fresh()
        arms: list[tuple[Stmt, ...]] = []
        start = self.spent
        worst = 0.0
        for tag in range(2):
            self.block = _Block(scope=dict(outer.scope), prefix=f"{name}a{tag}_")
            self.spent = start
            for _ in range(self.c.randint(f"branch.len{tag}", 1, 3)):
                self.step_op()
            arms.append(tuple(self.block.stmts))
            worst = max(worst, self.spent - start)
        self.block = outer
        self.spent = start
        self.emit(Stmt(name, "branch", "branch", args=(cond,), arms=tuple(arms)), Info("branch"), worst)
        del self.block.scope[name]

    def step_corner(self, forced: str | None = None) -> None:
        legal = [(c, CORNER_WEIGHTS.get(c, 1) if forced == c or (
                     forced is None and any(op in self.swarm and self.affordable(op) for op in ops)) else 0)
                 for c, ops in CORNERS.items()]
        corner = self.c.choose("corner", legal)
        ops = CORNERS[corner]
        op = self.c.choose(f"{corner}.op", [(o, 3 if o in self.swarm else 1 if forced == corner else 0)
                                            for o in ops])
        getattr(self, f"corner_{corner}")(op)

    # -- relational corners (§4.2) -------------------------------------------------

    def corner_apply(self, op: str, corner: str, args: list[Arg]) -> None:
        """Apply a corner's op to its constructed operands.

        With probability 1/2 (when affordable) the op is applied once under
        every mode: a mode sweep over the same operands exposes mode-dispatch
        defects that a single drawn mode would usually miss.
        """
        row = OP_BY_NAME[op]
        if not row.has_mode:
            self.apply(op, corner, corner=corner, args=args)
        elif self.c.coin(f"{corner}.sweep", 1, 2) and 5 * self.worst_cost(op) <= self.remaining():
            for mode in range(5):
                self.apply(op, corner, corner=corner, args=args, mode=mode)
        else:
            self.apply(op, corner, corner=corner, args=args, mode=self.corner_mode(corner))

    def corner_tie_plus(self, op: str) -> None:
        f = self.fmt
        e = self.c.randint("tie_plus.e", f.emin + 1, f.emax_field)
        m = self.c.randint("tie_plus.m", 1 << (f.p - 1), (1 << f.p) - 1)
        sx = self.c.below("tie_plus.sx", 2)
        sy = self.c.below("tie_plus.sy", 2)
        x = self.mint_value("tie_plus.x", sx, m, e)
        y = self.mint_value("tie_plus.y", sy, 1, e - 1)
        self.corner_apply(op, "tie_plus", [Arg.ref(x), Arg.ref(y)])

    def corner_tie_mult(self, op: str) -> None:
        f = self.fmt
        if f.p < 3:
            self.corner_cancel("Bplus" if "Bplus" in self.swarm else "Bminus")
            return
        c = self.c.randint("tie_mult.c", f.emin, f.emax_field)
        low = max(f.emin, c + 1 - f.emax)
        high = min(f.emax_field, c - 1 - f.emin)
        b = self.c.randint("tie_mult.b", low, high)
        a = c - 1 - b
        x = self.mint_value("tie_mult.x", self.c.below("tie_mult.sx", 2), 3, a)
        y = self.mint_value("tie_mult.y", self.c.below("tie_mult.sy", 2), (1 << (f.p - 1)) + 1, b)
        self.corner_apply(op, "tie_mult", [Arg.ref(x), Arg.ref(y)])

    def corner_cancel(self, op: str) -> None:
        sign, m, e = self.finite_class("cancel.v")
        x = self.mint_value("cancel.x", sign, m, e)
        if op == "Bminus":
            y = self.mint_value("cancel.y", sign, m, e) if self.c.coin("cancel.fresh", 1, 2) else x
            self.corner_apply(op, "cancel", [Arg.ref(x), Arg.ref(y)])
        elif op == "Bplus":
            y = self.mint_value("cancel.y", 1 - sign, m, e)
            self.corner_apply(op, "cancel", [Arg.ref(x), Arg.ref(y)])
        else:
            one = self.mint_value("cancel.one", self.c.below("cancel.os", 2), 1 << (self.fmt.p - 1), 1 - self.fmt.p)
            info = self.block.scope[one].exact
            assert info is not None
            z = self.mint_value("cancel.z", 1 - (sign ^ info[0]), m, e)
            self.corner_apply(op, "cancel", [Arg.ref(x), Arg.ref(one), Arg.ref(z)])

    def corner_overflow_edge(self, op: str) -> None:
        f = self.fmt
        sign = self.c.below("overflow.s", 2)
        x = self.mint_value("overflow.x", sign, (1 << f.p) - 1, f.emax_field)
        if op == "Bplus":
            which = self.c.choose("overflow.plus", [("half_ulp", 2), ("self", 1)])
            y = (self.mint_value("overflow.y", sign, 1, f.emax_field - 1) if which == "half_ulp" else x)
        else:
            y = self.mint_value("overflow.y", self.c.below("overflow.ys", 2),
                                (1 << (f.p - 1)) + (1 if f.p >= 2 else 0), 1 - f.p)
        self.corner_apply(op, "overflow_edge", [Arg.ref(x), Arg.ref(y)])

    def corner_tiny(self, op: str) -> None:
        f = self.fmt
        x = self.mint_value("tiny.x", self.c.below("tiny.xs", 2), 1 << (f.p - 1), f.emin)
        m = self.c.randint("tiny.m", 1 << (f.p - 1), (1 << f.p) - 1)
        # A factor just below 1 for a product, just above 1 for a quotient;
        # clamped into the format (a format with emin >= 0 has no factor < 1).
        low, high = (-f.p - 2, -f.p) if op == "Bmult" else (1 - f.p, 3 - f.p)
        low, high = max(f.emin, low), min(f.emax_field, high)
        e = self.c.randint("tiny.e", low, high) if low <= high else f.emin
        y = self.mint_value("tiny.y", self.c.below("tiny.ys", 2), m, e)
        self.corner_apply(op, "tiny", [Arg.ref(x), Arg.ref(y)])

    def corner_equal_pair(self, op: str) -> None:
        which = self.c.choose("equal.kind", [("same", 2), ("zeros", 1), ("copy", 1)])
        if which == "zeros":
            x = self.mint_special("equal.x", 0, 0)
            y = self.mint_special("equal.y", 0, 1)
        else:
            sign, m, e = self.finite_class("equal.v")
            x = self.mint_value("equal.x", sign, m, e)
            y = x if which == "same" else self.mint_value("equal.y", sign, m, e)
        self.corner_apply(op, "equal_pair", [Arg.ref(x), Arg.ref(y)])

    def corner_half_int(self, op: str) -> None:
        m, e = self._half_int("half_int")
        x = self.mint_value("half_int.x", self.c.below("half_int.s", 2), m, e)
        self.corner_apply(op, "half_int", [Arg.ref(x)])

    def corner_max_succ(self, op: str) -> None:
        f = self.fmt
        sign = 1 if op == "Bpred" else 0
        if self.c.coin("max_succ.flip", 1, 4):
            sign = 1 - sign
        x = self.mint_value("max_succ.x", sign, (1 << f.p) - 1, f.emax_field)
        self.corner_apply(op, "max_succ", [Arg.ref(x)])

    def corner_sticky_gap(self, op: str) -> None:
        f = self.fmt
        e = self.c.randint("sticky.e", min(f.emin + f.p + 2, f.emax_field), f.emax_field)
        m = self.c.randint("sticky.m", 1 << (f.p - 1), (1 << f.p) - 1)
        gap = self.c.randint("sticky.gap", f.p, f.p + 3)
        ye = max(f.emin, e - gap)
        ym = self.c.randint("sticky.ym", 1 << (f.p - 1), (1 << f.p) - 1) if ye > f.emin else 1
        x = self.mint_value("sticky.x", self.c.below("sticky.sx", 2), m, e)
        y = self.mint_value("sticky.y", self.c.below("sticky.sy", 2), ym, ye)
        if op == "Bfma":
            one = self.mint_value("sticky.one", 0, 1 << (f.p - 1), 1 - f.p)
            self.corner_apply(op, "sticky_gap", [Arg.ref(x), Arg.ref(one), Arg.ref(y)])
        else:
            self.corner_apply(op, "sticky_gap", [Arg.ref(x), Arg.ref(y)])

    def corner_fma_error(self, op: str) -> None:
        """``fma(x, y, -RN(x*y))``: the exact rounding error of a product (TwoProduct).

        A fused fma returns the (representable) error; a product rounded
        before the addition returns zero.
        """
        f = self.fmt
        # t = e1 + e2 + p is about the exponent field of RN(x*y). Prefer a
        # product whose error is representable and that cannot overflow; tiny
        # formats fall back to any exponent pair.
        low, high = f.emin + f.p, f.emax_field - 1
        if low > high:
            low, high = 2 * f.emin + f.p, 2 * f.emax_field + f.p
        t = self.c.randint("fma_error.t", low, high)
        e1 = self.c.randint("fma_error.e1", max(f.emin, t - f.p - f.emax_field), min(f.emax_field, t - f.p - f.emin))
        e2 = t - f.p - e1
        m1 = self.c.randint("fma_error.m1", 1 << (f.p - 1), (1 << f.p) - 1)
        m2 = self.c.randint("fma_error.m2", 1 << (f.p - 1), (1 << f.p) - 1)
        s1, s2 = self.c.below("fma_error.s1", 2), self.c.below("fma_error.s2", 2)
        x = self.mint_value("fma_error.x", s1, m1, e1)
        y = self.mint_value("fma_error.y", s2, m2, e2)
        rounded = round_ne(Fraction(m1 * m2) * Fraction(2) ** (e1 + e2), f)
        if rounded is None:
            z = self.mint_special("fma_error.z", 1, 1 - (s1 ^ s2))
        else:
            z = self.mint_value("fma_error.z", 1 - (s1 ^ s2), *rounded)
        self.corner_apply(op, "fma_error", [Arg.ref(x), Arg.ref(y), Arg.ref(z)])

    # -- driver ------------------------------------------------------------------

    def run(self) -> GenResult:
        size = self.c.randint("size", self.config.min_size, self.config.max_size)
        for k in range(self.c.randint("leaves", 1, 3)):
            self.mint_bsn(f"leaf{k}")
        for op in self.config.force_ops:
            self.step_op(forced=op)
        for form in self.config.force_forms:
            self.step_form(form, forced=True)
        for _ in range(size):
            if self.remaining() <= 0:
                break
            has_bool = bool(self.bindings("Bool"))
            fold_legal = any(o in self.swarm and self.affordable(o) for o in FOLD_SHAPES)
            corner_legal = any(any(op in self.swarm and self.affordable(op) for op in ops)
                               for ops in CORNERS.values())
            form = self.c.choose("form", [
                ("op", self.config.op_weight),
                ("corner", self.config.corner_weight if corner_legal else 0),
                ("select", 1), ("case4", 1),
                ("fold", 1 if fold_legal else 0),
                ("branch", 1 if has_bool else 0)])
            self.step_form(form)
        program = Program(self.fmt, tuple(self.block.stmts))
        check_program(program)
        return GenResult(program, self.spent, self.swarm, self.modes)

    def step_form(self, form: str, forced: bool = False) -> None:
        if form == "op":
            self.step_op()
        elif form == "select":
            self.step_select()
        elif form == "case4":
            self.step_case4()
        elif form == "fold":
            self.step_fold(any_op=forced)
        elif form == "branch":
            if not self.bindings("Bool"):
                self.apply(self.c.choose("branch.pred", [("Bltb", 1), ("Bsign", 1), ("is_nan", 1)]), "branch.pred")
            self.step_branch()
        elif form == "corner":
            self.step_corner()
        elif form.startswith("corner:"):
            self.step_corner(forced=form[len("corner:"):])
        else:
            raise GeneratorBug(f"unknown form {form}")


def generate(chooser: Chooser, config: GenConfig) -> GenResult:
    result = Generator(chooser, config).run()
    chooser.finish()
    return result


def program_seed(seed: int, index: int) -> str:
    return f"flocqsmith:{seed}:{index}"
