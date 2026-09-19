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
execute inside the test modules and bridges. Native execution is covered by
the three-way binary64 bridge described below, not by that no-op executable.

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

The first eight test families cover integer power, signed division, the three
location update functions, six rounding decisions/increment operations,
truncation, core addition, core division, and core square root. The corpus mixes
small boundary grids with seeded random cases, including negative operands,
zero divisors, negative shifts, and several radices. Tests outside a theorem's
preconditions check total-function correspondence only.

Four more families extend this to integer digit counts, all four exponent
functions (`FIX`, `FLX`, `FLT`, `FTZ`), primitive float operations (alignment,
negation, absolute value, addition, subtraction, multiplication), and combined
format-dependent addition/division/square root/truncation. The adapters account
explicitly for parameter-order differences between the Lean and Coq APIs.

A thirteenth family tests IEEE overflow in all five rounding modes: result
constructor, sign, mantissa, exponent, and actual canonical/bounded validity.
It enforces `0 < prec < emax`, the source contract's precision premises. The
real validity predicate is essential here; the legacy always-true predicate
would provide no evidence about whether an overflow result is representable.

Lean reduces the calls with `#reduce`; Rocq uses `vm_compute`. The runner rejects
compiler failures, unknown output, abbreviated output, missing rows, and empty
corpora. It compares every output row. For agreeing batches, it then generates
`OracleRegressions.lean`: a separate equality statement for each input, with
Rocq's observed values as the expected results. Lean checks those statements
using `decide +kernel`. Separate statements avoid the expensive normalization
of one enormous conjunction/list equality for the more complex operations.

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
Rocq and Lean checks, runs all three differential bridges, and executes their own
tests. Live mutations recreate the historical negative-exponent bug and replace
native successor by predecessor, and swap native arithmetic operands. Each
mutation must cause a failed comparison
and emit a replay case. The temporary reference worktree is removed; bridge
artifacts are retained at the paths printed by the runners.

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

Target just the newer source families while keeping the other loop intact:

```sh
uv run scripts/flocq_bridge.py --flocq-dir /path/to/pinned-flocq \
  --operations formats,digits,operations,format_calc --seed 7831 --samples 100
```

The bridge rebuilds its Lean imports before executing, records compiler
versions, source commit and worktree status, and retains a `report.json` with
the seed, per-family counts, completed regression count, and final status.
It also hashes project Lean sources and dependency configuration, rejecting a
change observed after the build or any batch. This prevents a successful run
from silently mixing edited source snapshots; it is not binary attestation.
An interrupted or errored run is not a pass. CI currently runs the Lean grids
and fast harness-unit tests; the live Rocq bridge is separately executed on
this Mac and is not yet installed as a hosted-CI job.

## 5. Native binary64: three implementations, one input

`scripts/native_ieee_bridge.py` adds actual native execution via `lean --run`
and its floating-point FFI. For each raw 64-bit input, it compares five fields:
decoded/canonicalized input, successor, predecessor, `frExp` significand, and
signed `frExp` exponent. The other two paths reduce the Lean logical Flocq
carrier in the kernel and execute the pinned Rocq definitions with `vm_compute`.

The boundary corpus covers both signs, zero, subnormal powers of two and their
neighbors, minimum normals, exponent transitions, maximum finite values,
infinities, and signaling/quiet NaN payloads. Seeded arbitrary bit patterns
supplement that corpus. All three result streams are retained independently.

Two qualifications are deliberate and visible in the report:

- NaNs are observed through the single-NaN model. All payloads and signs map to
  `0x7ff8000000000000`; agreement does **not** establish payload preservation.
- Native `frExp` equivalence is asserted only for nonzero finite values, as in
  the theorem's precondition. The observed exceptional exponent is `0` on this
  Mac, versus `-2101` in the logical Flocq model. Those exceptional observations
  remain in the report; their input decoding and successor/predecessor results
  are still compared. Lean-model versus Rocq comparison includes **all** fields
  on **all** inputs, including the exceptional cases.

Every agreeing model/Rocq row becomes a checked Lean equality. This proves the
individual logical-model result, not the native FFI correspondence theorem.
The native minimum-subnormal case is also a permanent model regression in
`FloatSpec/Test/NativeIEEE.lean`, paired with `scripts/fixtures/NativeIEEE.v`.

```sh
uv run scripts/native_ieee_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 20260919 --samples 200 --batch-size 25
# Use --replay /path/to/cases.json to run exactly the same bit patterns again.
```

The combined shell runner accepts `FLOCQ_NATIVE_SAMPLES` and
`FLOCQ_NATIVE_BATCH_SIZE` for this additional loop.

## 6. Arithmetic at real binary64 sizes

`scripts/native_arithmetic_bridge.py` sends each pair of raw binary64 words
through native Lean arithmetic, the port's `FaithfulPrimFloat` operations, and
Flocq's `b64_plus`, `b64_minus`, `b64_mult`, `b64_div`, and `b64_sqrt`. All use
round-to-nearest, ties-to-even. Each row contains seven fields: both canonical
inputs, sum, difference, product, quotient, and square root of the left operand.
Unlike `frExp`, these comparisons include every exceptional case: signed zero,
infinity, NaN, zero divisors, and negative square-root inputs. NaN payloads are
still quotiented out explicitly, not accidentally treated as preserved.

The fixed grid crosses 32 boundary words with each other. Random pairs are
augmented with equal operands, opposite signs (cancellation), and adjacent bit
patterns. Particular boundaries include half an ULP at one, half the smallest
subnormal, the normal/subnormal transition, and maximum finite overflow.
Every model/Rocq agreement is again checked as a separate kernel theorem.

Running this exposed a practical defect hidden by the old small grids:
`binaryPositiveOfNat` constructed its answer using `n-1` successor operations.
It was provably correct but could not reduce ordinary 53-bit mantissas. The
replacement recurses over binary digits, retains the same public type and
proved value theorem, and now supports the actual arithmetic tests. This is
an execution repair, not a change to the mathematical rounding algorithm.

```sh
uv run scripts/native_arithmetic_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 526913 --samples 100 --batch-size 20
# Replay uses a JSON array of [left_bits, right_bits] pairs.
```

The combined runner accepts `FLOCQ_ARITHMETIC_SAMPLES` and
`FLOCQ_ARITHMETIC_BATCH_SIZE`. Its harness tests each output column, deliberately
swaps native operands, and verifies that timeout/interruption records are
errors with zero completed cases, never passes. Do not rebuild dependencies
or edit imported Lean source during an active run: rebuilding can temporarily
remove `.olean` files that another evaluator is reading. Finish or explicitly
stop the run, rebuild, and then start a fresh evidence run.

## 7. What this still does not establish

No finite grid or random corpus proves universal source equivalence. The bridge
does not yet exercise all of IEEE arithmetic, every native primitive,
real-valued noncomputable mathematics, or all theorem hypotheses/conclusions.
The four named native/bit proof debts remain separate. Read the
[audit ledger](ASTRA_AUDIT_2026-09-19.md) for observed results and unreviewed scope.
