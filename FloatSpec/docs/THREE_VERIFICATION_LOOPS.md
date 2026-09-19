# Run the three verification loops

The aim is not to trust two matching programs blindly. We check mathematical
invariants on each side, then compare the implementations on identical inputs,
then turn the reference observations into checked Lean regression statements.

## 1. Lean checks itself

`lake build FloatSpec.Test FloatSpecTests floatspec` builds the port, its tests,
and the executable on the selected toolchain. In addition to the existing
regressions, `Test/ArithmeticProperties.lean` contains three finite grid theorems:

- 8,316 exact-rational midpoint classifications. Represent a point inside a
  small interval by its quarter-integer numerator and compare it with the
  enclosing interval's midpoint. This checks `new_location` independently of
  the implementation's even/odd branch split.
- 2,145 signed quotient/remainder invariants, including the totalized
  division-by-zero behavior. Check reconstruction, remainder bounds, and sign.
- 273 integer square-root brackets. Check `q² ≤ m < (q+1)²` and exactness for
  nonnegative inputs, plus the specified convention for negative inputs.

These Lean statements are proved by reduction in the kernel, without
`native_decide`, new axioms, or admitted proofs. They certify the enumerated
finite grids, not all integers.

The current `floatspec` executable's `main` does nothing. Running it is a
launch smoke test only, not an arithmetic regression; the checks described here
execute inside the test modules and bridge. Native machine arithmetic is a
separate coverage target.

## 2. Flocq checks itself

`scripts/fixtures/ArithmeticProperties.v` checks the same independent invariants
with Rocq's evaluator and closes the resulting equality proofs. It imports the
actual Flocq definitions from the pinned gitlink; it does not implement a second
version of those arithmetic routines in the test.

The reference is built separately from the user's modified `Deps/flocq`
checkout. A supplied cached checkout must match the gitlink and have no changed
tracked sources or untracked `.v` source files. The runner uses that checkout's
configured Rocq compiler. On the audit Mac, the cached reference uses Homebrew
Rocq 9.2, while the project-local `coqc` is 9.1; those compiled artifacts are not
interchangeable.

## 3. Connect the two

`scripts/flocq_bridge.py` creates one JSON input corpus and translates each row
into calls to the real imported definitions in both languages. The adapters
only construct inputs and serialize results. Location values are encoded as
`Exact=0`, `Lt=1`, `Eq=2`, `Gt=3`; signed integers remain signed integers.

The initial eight test families cover integer power, signed division, the three
location update functions, six rounding decisions/increment operations,
truncation, core addition, core division, and core square root. The corpus mixes
small boundary grids with seeded random cases, including negative operands,
zero divisors, negative shifts, and several radices. Tests outside a theorem's
preconditions check total-function correspondence only.

Lean reduces the calls with `#reduce`; Rocq uses `vm_compute`. The runner rejects
compiler failures, unknown output, abbreviated output, missing rows, and empty
corpora. It compares every output row. For agreeing batches, it then generates
`OracleRegressions.lean`: equality statements with Rocq's observed values as the
expected results. Lean checks those statements using `decide +kernel`.

A disagreement retains the exact input, both results, the generated `.lean`
and `.v` files, and a `replay.json` corpus. This is the feedback step: inspect
the source, fix the incorrect definition or adapter, and preserve the case as
a regression. Do not automatically alter the implementation merely to agree
with a possibly faulty adapter.

## 4. One command runs all three

From the repository root:

```sh
bash scripts/test_flocq_conformance.sh
```

This creates and builds a detached reference worktree, runs the standalone
Rocq and Lean checks, runs the differential bridge, and executes the harness's
own tests, including a live mutation that recreates the historical
negative-exponent bug. That mutation must cause a failed comparison and emit a
replay case. The temporary reference worktree is removed; bridge artifacts are
retained at the path printed by the runner.

For a previously built reference checkout:

```sh
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq FLOCQ_SKIP_BUILD=1 \
  FLOCQ_BRIDGE_SEED=483921 FLOCQ_BRIDGE_SAMPLES=1000 \
  bash scripts/test_flocq_conformance.sh
```

Replay saved inputs without regenerating them:

```sh
uv run scripts/flocq_bridge.py --flocq-dir /path/to/pinned-flocq \
  --replay /path/to/replay.json
```

The bridge rebuilds its Lean imports before executing, records compiler
versions, source commit and worktree status, and retains a `report.json` with
the seed, per-family counts, completed regression count, and final status.
An interrupted or errored run is not a pass. CI currently runs the Lean grids
and fast harness-unit tests; the live Rocq bridge is separately executed on
this Mac and is not yet installed as a hosted-CI job.

## 5. What this still does not establish

No finite grid or random corpus proves universal source equivalence. The bridge
does not yet exercise all of IEEE arithmetic, native machine execution,
real-valued noncomputable mathematics, or theorem hypotheses/conclusions.
The four named native/bit proof debts remain separate. Read the
[audit ledger](ASTRA_AUDIT_2026-09-19.md) for observed results and unreviewed scope.
