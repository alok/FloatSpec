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

`Test/BitsExecution.lean` additionally executes 10,000 binary32 and 10,000
binary64 decode/re-encode roundtrips in compiled Lean, retaining NaN payloads.
It uses a documented fixed-seed recurrence, not floating-point arithmetic to
generate inputs. Kernel examples separately pin ordinary values and a signed
signaling NaN. The paired `BitsProperties.v` checks the same independent
roundtrip invariants in Rocq.

`Test/BitOrderExecution.lean` executes 2,000 pure ordering-law checks and
separately compares the actual binary32/binary64 comparison APIs with 200,000
native Float/Float32 comparisons (seed `388312`). Kernel examples pin signed
zero, ordinary ordering, a signaling NaN, and the successor of a negative
minimum subnormal. `BitOrderProperties.v` checks the same 2,000 independent
ordering-law cases in Rocq. The combined runner directly re-executes the Lean
test files, so an already cached test module does not skip these runtime loops.

`Test/NativeSourceArithmetic.lean` adds 100,100 comparisons of the port's
compiled binary32/binary64 add/subtract/multiply/divide/sqrt operations with
native Float32/Float. Twenty explicit input pairs cover exceptional values,
ties, underflow and overflow; 20,000 additional pairs come from seed `489231`.
This native grid quotients NaNs explicitly, retains signed zero, and reports a
replayable `[width, mode, left, right, third]` input if any column disagrees.
`RoundingWalkthrough.lean` and its Rocq fixture execute and prove the reading
guide's three-bit halfway example in all five modes, for both signs.

The standalone paired fixtures add independent contract and error checks:

- `DoubleRoundingWitness`: `73/64` rounded directly to three bits differs from
  rounding through four bits; both signs have closed equality proofs.
- `SingleNaNValidity`: canonical, subnormal, overflow, and invalid raw-carrier
  boundaries, including why `binary_fit_aux` requires canonical input.
- `RelativeErrorGrid`: 4,092 nearest-error bounds and an underflow counterexample
  to using an unconditional relative bound.
- `ExactArithmeticLaws`: 275 exact-input checks, 1,055 Sterbenz checks, and
  5,714 nearest-addition-error representability checks.
- `RoundingOracle`: 35,845 finite rounding cases in all five modes, selected
  independently by enumerating candidates and comparing exact distances.
  Lean executes the full grid and proves 95 boundary cases in the kernel;
  Rocq closes its full grid with `vm_compute`.

`Test/SourcePremiseContracts.lean` additionally has 45 source-premise guards,
paired typed consumers for the Prop, integer-rounding, canonical-exponent,
real-comparison, and generic IEEE comparison exports, and four deliberate
negative guard examples. The corresponding Rocq fixture checks the paired
consumer signatures. These
checks caught real section-instance leakage that the former bare `#check`
regressions did not detect. The combined runner re-executes all these fixtures;
the CI workflow also runs their Lean side. Local success is not a claim that
hosted CI has run.

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

Two more families directly test binary32/binary64 bit decoding, re-encoding,
field splitting, and validity. They preserve NaN payloads and signs instead of
canonicalizing them. Inputs include unbounded negative and over-width integers:
Flocq's input is `Z`, and its sign comparison is not machine-word wrapping.

A sixteenth family executes the integer-width `Bits.Source.join_bits` and
`split_bits` interfaces, including negative widths and invalid field ranges.
It observes packing, splitting, and both compositions. A negative shift is a
right shift, not a clamp to width zero. These total-function tests do not assert
the roundtrip theorem outside its width/field hypotheses. An 836-case run
(seed `593873`, 500 random inputs) agreed in compiled Lean, kernel reduction,
and Rocq and generated 836 passing kernel regression equalities.

Two further families execute the fixed-width comparison APIs, negation,
absolute value, proof erasure, predecessor, and successor. Their fourteen output
columns retain both decoded input words, both comparison directions, the
five fixed-width unary results, and the generic `Binary.Bpred`, `Bsucc`, and
`Bulp` results, followed by full-float and SingleNaN comparison results.
The generic neighbor algorithms are compiled rather than replaced by the
fixed-width wrappers. Fixed-width and generic comparison now share the proved
source algorithm; their agreement is an API wiring check, not independent
implementation evidence. Comparison has type `Option Ordering`; only the
serialization adapter uses integers (`lt=-1`, `eq=0`, `gt=1`, unordered `2`).
Signed zeros compare equal; NaNs remain unordered and unary source operations
preserve their exact signs and payloads. The boundary corpus crosses all
selected operand pairs and includes negative/over-width integer decoder inputs.

A nineteenth family audits SingleNaN validity and total conversion. It compares
the actual validity Boolean, the raw-carrier validity proposition, and three
converter views. Its raw precision/exponent parameters can violate later
arithmetic hypotheses; its mantissa must be positive because that is a source
constructor requirement. Seed `860213` found 240 mismatches in 1,180 inputs
before the raw-boundary repair and none afterwards. All 1,180 repaired cases
also pass as generated kernel equalities. A deliberate conversion mutation
must reproduce the noncanonical `(mantissa=1, exponent=0)` failure.
The fifteenth observation column now checks the repaired legacy
`valid_binary_SF` name independently too. Its always-true predecessor disagreed
with Rocq on three of a five-case red corpus; that corpus is retained for
replay. A separate deliberate always-true mutation must be rejected in both
compiled Lean and kernel reduction.

The twenty-first family directly exercises generic SingleNaN successor,
predecessor, and ulp across precisions 1, 2, 3, 4, 24, and 53, with seeded
supplemental formats. Seventeen columns retain input validity, the total
converter's result, and each operation's constructor/sign/mantissa/exponent.
Input grids straddle the minimum exponent, normal/subnormal transition, and
overflow boundary, and include signed zero, infinities, NaN, and invalid raw
carriers. Invalid raw inputs are visibly rejected to NaN before arithmetic;
they are not mislabeled as valid arithmetic inputs. The operation's precision
premises `0 < prec < emax` remain enforced. A successor-to-predecessor mutation
must fail in both compiled Lean and kernel reduction against Rocq.

The twenty-second family executes generic comparison over ten formats,
including nonpositive precision and `emax <= prec`. These exports have no
precision premises in Flocq. Eleven columns retain both raw validity flags,
both converted values, and the ordering result. Invalid raw finite carriers
are explicitly converted to NaN; signed zeros, infinities, and unordered NaNs
are preserved. An operand-swap mutation must fail in both Lean execution
paths. The public `Binary.Bcompare` and `BinarySingleNaN.Bcompare` now return
`Option Ordering` and execute integer comparisons, with closed value and
reversal proofs. The legacy raw-carrier integer-coded adapter is named
`BcompareIntCompat` rather than presented as the source interface.

Lean both executes compiled calls with `--run` and reduces them with `#reduce`;
Rocq uses `vm_compute`. Enabling compiled execution required removing
unnecessary `noncomputable` markers from twelve integer-only Calc definitions
and three bit decoders; their bodies and public types did not change. The runner rejects
compiler failures, unknown output, abbreviated output, missing rows, and empty
corpora. It compares all expected columns of all three result streams. For
kernel/Rocq-agreeing batches, it then generates
`OracleRegressions.lean`: a separate equality statement for each input, with
Rocq's observed values as the expected results. Lean checks those statements
using `decide +kernel`. Separate statements avoid the expensive normalization
of one enormous conjunction/list equality for the more complex operations.
The core bridge builds its imports by default. Its explicit `--skip-build`
option is only for a known prebuilt, stable snapshot and records
`fresh_build: false`; it must not be used to hide stale imports.

A disagreement retains the exact input, all three results, the generated `.lean`
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
Rocq and Lean checks, runs all five differential bridges, and executes their own
tests. Live mutations recreate the historical negative-exponent bug and replace
native successor by predecessor, swap native arithmetic operands, and alter
only compiled Lean while kernel/Rocq still agree. Each
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
`uv run scripts/check_compiled_trust.py` independently checks all elaborated
source declarations and their transitive axiom dependencies against the four
named proof debts. Its regression fixture deliberately includes theorem and
opaque sorries, a propagated sorry, a new axiom, an unsafe definition, and
runtime overrides; the gate must observe and reject all of those hazards.
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

On macOS/Linux each prover command now runs in its own process group. A
timeout or interruption kills that group and reaps the immediate child;
the regression suite checks that a spawned descendant cannot continue writing
after the timeout. The old runner killed only its immediate process and failed
that test. The result parser also accepts Lean's line-wrapped integer
constructors, including the 309-digit maximum finite binary64 integer.
Neither repair changes what counts as a pass: errors, incomplete output,
or missing observations still fail closed.

## 7. All five IEEE rounding modes, including fused multiply-add

The standalone `scripts/ieee_modes_bridge.py` directly exercises the port's
binary32 and binary64 APIs under nearest-even, toward-zero, downward, upward,
and nearest-away rounding. Each row retains three exact input encodings and
six results: add, subtract, multiply, divide, square root, and fused
multiply-add. Unlike the native arithmetic bridge, it preserves NaN signs and
payloads and checks the source's first-NaN propagation policy.

This runs compiled integer-only Lean, Lean kernel reduction, and Rocq,
**not** native hardware directed rounding. The fixed-width source operations
now compile directly. Most of that repair only removed unnecessary
`noncomputable` markers. Square root additionally needed its real-valued input
witness moved inside the erased validity proof; its integer computation and
public type were preserved.
Its cases include half-ULP ties, tiny subnormal products, cancellation after an
overflowing intermediate product, signed zeros, infinities, negative square
roots, and NaNs in each of the three operand positions. Random triples are
generated separately for every format/mode pair. Every agreeing batch produces
kernel-checked Lean equality statements, with replay artifacts on a mismatch.

```sh
uv run scripts/ieee_modes_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 923451 --samples 30 --batch-size 5
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_ieee_modes_bridge.py -v
```

The live harness replaces upward rounding with nearest-even in only the Lean
adapter and requires a failed comparison with the exact replay input. A second
mutation changes only compiled Lean and must fail even when kernel/Rocq agree.
All nine columns and all three execution paths are mandatory. Timeout
and interruption tests must report errors, never successful zero-case runs.
The combined shell suite includes this bridge and its live harness; use
`FLOCQ_MODES_SAMPLES` and `FLOCQ_MODES_BATCH_SIZE` to size this phase. It also
runs the compiled trust gate and its adversarial fixtures. These additions
postdate the completed seed-8491 aggregate receipt in the audit ledger; that
receipt must not be relabeled as a run of later additions. A later complete
run with seed `709541` passed 8,684 core, 622 native unary, 1,424 native
arithmetic, and 590 all-mode cases, with all generated kernel regressions and
live harness tests. Its source fingerprint is
`541bfc055e147a800162233e5b08d920f28b595340f739d971caaa80993ea3c3`.
The newly added premise/error/oracle fixtures were executed separately after
that frozen run; do not retroactively include them in that aggregate receipt.

## 8. Scaling and decomposition: four execution paths

`scripts/ieee_scale_bridge.py` runs `Binary.Bldexp` and `Binary.Bfrexp`
directly as compiled Lean, kernel reduction, and pinned Rocq. Those three
paths compare all five fields exactly: original bits, scaled bits, fraction
bits, exponent, and the reconstructed input. NaN signs/payloads are retained.
The definitions are integer-only; enabling execution removed unnecessary
`noncomputable` markers without changing their bodies or types.

A fourth path uses native `Float` and `Float32`. Its scale comparison is
restricted to nearest-even, because native `scaleB` does not accept a mode.
Its fraction/exponent comparison is restricted to nonzero finite inputs,
the domain of the source normalization theorem. Native exceptional outputs
are retained in the report with an explicit list of checked fields. NaNs
are quotiented only for this native comparison, never between Lean and Rocq.

```sh
uv run scripts/ieee_scale_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 604719 --samples 20 --batch-size 40
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_ieee_scale_bridge.py -v
# Replay rows are [width, mode, unsigned_input_word, integer_shift].
```

The first extended run passed **2,360 cases and 2,360 kernel regressions**
in 408.335 seconds, at source SHA-256
`f5db09e6d0e537474ceb0d2d02e391d8646ed86e9588e43d0103728de8f790cd`.
All seven harness tests pass, including separately mutated kernel/compiled/
native scaling, missing paths/columns, and interruption/timeout/source drift.
The corpus crosses signed zeros, least subnormals, the normal transition,
finite overflow, infinities, and signed NaNs in all five modes and both widths.
Its shifts are bounded; it does not claim practical execution of arbitrary
enormous integer shifts. The combined runner now includes this phase through
`FLOCQ_SCALE_SAMPLES` and `FLOCQ_SCALE_BATCH_SIZE`.

## 9. Integer rounding and unbounded truncation

`scripts/ieee_integer_bridge.py` executes the actual Binary and SingleNaN
`Bnearbyint`/`Btrunc` APIs in compiled Lean, kernel reduction, and pinned Rocq.
Its five observations are input bits, full-float nearby bits, full-float
truncation integer, SingleNaN nearby bits, and SingleNaN truncation integer.
Source paths retain NaN signs/payloads exactly; integer outputs are unbounded.

Native Float/Float32 provides a fourth path. Its floor, ceil, and ties-away
rounding check four modes; its `round` is not claimed to implement nearest-even.
Native unsigned conversion checks truncation only for finite `|x| < 2^64`.
Every excluded native field remains in the report with its explicit scope;
all source fields still compare exactly even outside that native range.

```sh
uv run scripts/ieee_integer_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 730519 --samples 20 --batch-size 50
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_ieee_integer_bridge.py -v
# Replay rows are [width, mode, unsigned_input_word].
```

The corpus includes both signs, every mode, integer/halfway boundaries,
adjacent inputs, the integer-spacing transition, the unsigned-conversion
boundary, maximum finite values, infinities, and NaNs. A separate twentieth
core family (`--operations nearby`) executes both raw integer helpers over
precision/exponent parameters including invalid later-theorem domains. It
observes the intermediate integer, resulting representation, and both input
and output validity. Its source mantissa must still be positive.

The independent paired `IntegerRounding.lean` / `.v` fixtures check 5,125
eighth-integer inputs using division, distance, and parity rather than the
implementation's shifts. Both check idempotence, and Lean closes the whole
finite grid in its kernel. The combined runner includes this fixture and
the new bridge through `FLOCQ_INTEGER_SAMPLES` and `FLOCQ_INTEGER_BATCH_SIZE`.

## 10. What this still does not establish

The expanded combined runner completed at commit `ba3e2a8b`, seed `961703`,
with 10,788 core cases, 672 native unary cases, 1,624 arithmetic pairs,
690 all-mode IEEE cases, and 2,560 scale/decomposition cases. All generated
kernel regressions, independent fixtures, and 48 live bridge-harness tests
passed. The exact source fingerprint and per-phase times are recorded in the
audit ledger; this is a receipt for that snapshot, not later changes.

No finite grid or random corpus proves universal source equivalence. The bridge
does not yet exercise all of IEEE arithmetic, every native primitive,
real-valued noncomputable mathematics, or all theorem hypotheses/conclusions.
The four named native/bit proof debts remain separate. Read the
[audit ledger](ASTRA_AUDIT_2026-09-19.md) for observed results and unreviewed scope.
