# Run the three verification loops

The package sets `restoreAllArtifacts := true`: standalone `lake env lean`
fixtures require import artifacts in the normal build directory. With a global
`LAKE_ARTIFACT_CACHE=true` and restoration disabled, Lake can report a successful
build while those fixtures fail on missing `.olean` files. This setting keeps
the user's cache enabled while making its outputs available to the fixtures.

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
- `RawIEEERounding`: nine literal rounding and invalid-precondition cases,
  including signed-zero results mined from the differential bridge. Both
  languages check the same expected values, independently of the adapter.
- `RawOverflow`: seven literal constructor/mantissa/exponent expectations,
  including the positive-carrier fallback at nonpositive precision. A Lean
  theorem separately proves that the shared helper is positive at every
  integer precision, without a format-validity instance.
- `SingleNaNArithmetic`: 30 literal one-bit-format results in all five modes,
  through both the direct and source-mode SingleNaN APIs. The cases cover
  overflow, signed cancellation, underflow ties, square root, and an FMA whose
  unrounded intermediate product would overflow if evaluated separately.
  Lean checks both APIs by kernel reduction and compiled execution; the paired
  Rocq fixture proves the same literal results independently.
- `MultiplicationErrorGrid`: 55 independently enumerated exact inputs and
  5,385 multiplication-error representability checks in all five modes.
  Products satisfy the source underflow premise and stay below overflow;
  error membership is tested against the enumeration, without re-rounding
  the error. Both languages close the full grid by reduction, and Lean also
  executes it. A subnormal-product counterexample checks why the hypothesis
  cannot simply be omitted.

`SingleNaNHelpers` separately checks 13 literal helper results, four
decompositions, and two signed shifts, closed independently in both assistants
and executed in Lean. The one-bit decomposition explicitly checks the branch
outside the normalized-fraction theorem's `2 < emax` hypothesis.
Two additional closed counterexamples show that alternate ulp equality needs
a finite input and positive-only predecessor equality needs a positive input.

`NativeSingleNaNArithmetic.lean` additionally executes **200,200** nearest-even
comparisons against native Float32/Float, calling both direct and source-mode
SingleNaN APIs. Seed `831557` supplies 10,000 pairs at each width, plus ten
explicit boundary pairs per width; five operations are observed through each
API. Signed zeros are preserved and NaNs are quotiented. A reported failing
word pair can be replayed through the fixture's public `observations32` or
`observations64`; the mode bridge now calls these same SingleNaN APIs against
Rocq on those words, in addition to the full-payload baseline. This is finite native execution, not a hardware
correctness proof or a native FMA/directed-rounding test.

`Test/SourcePremiseContracts.lean` additionally has 72 source-premise guards,
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

A separate Rocq 9.2 `coqchk -silent -o -Q src Flocq` run checked all 35 built
reference modules, recursively including their dependencies, without `-admit`
or `-norec`. This checks compiled proof objects, not just executable examples.
Its successful context report records classical-real/function-extensionality
assumptions and Rocq's primitive integer/float axioms. It is **not** an
axiom-free certification of native hardware. The report found no type-in-type,
unsafe (co)fixpoint, or assumed-positivity dependencies. The exact command and
receipt are retained in the audit ledger.

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

A thirteenth family tests IEEE overflow in all five rounding modes. Its 21
columns retain the source-facing SingleNaN result, actual canonical/bounded
validity, both legacy full-float routes, the standard helper, and the exact
positive-mantissa full-float result. Constructor, sign, mantissa, and exponent
are compared for every route. The total source function accepts arbitrary
integer precision/exponent bounds; only its validity theorem requires
`0 < prec < emax`. The former harness incorrectly imposed those theorem
premises on runtime inputs and therefore missed a real difference.

At nonpositive precision, Rocq's `Z.to_pos (2^prec - 1)` defaults to 1, whereas
the old Lean raw result had mantissa 0. Expanding the domain found 87
disagreements in 680 cases (seed `827419`). The exact full-float embedding
already enforced positivity, so its output agreed even when earlier raw
stages did not. This is why the expanded test retains each stage rather than
checking only the last conversion. The shared corrected helper is positive
for every integer precision; its ordinary positive-precision formula is
unchanged. All 87 inputs are retained in `RawOverflowReplay.json` and replayed
by the aggregate runner. A separate mutation of each of the five mantissa
columns must be detected in both Lean paths. The real validity predicate is
still observed; nonpositive-precision finite outputs are not declared valid.

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
precision premises in Flocq. Fourteen columns retain both raw validity flags,
both converted values, the ordering result, and the public `Beqb`, `Bltb`,
and `Bleb` results. Invalid raw finite carriers
are explicitly converted to NaN; signed zeros, infinities, and unordered NaNs
are preserved. Operand-swap, NaN-equality, and strict/non-strict Boolean
mutations must fail in both Lean execution paths. The paired
`scripts/fixtures/BooleanComparison.lean` and `.v` independently check eight
boundary cases with literal expected answers. `Test/BitOrderExecution.lean`
also checks the three Boolean APIs against 600,000 native Float/Float32
Boolean observations using the existing seed `388312`.
The public `Binary.Bcompare` and `BinarySingleNaN.Bcompare` now return
`Option Ordering` and execute integer comparisons, with closed value and
reversal proofs. The legacy raw-carrier integer-coded adapter is named
`BcompareIntCompat` rather than presented as the source interface.

The twenty-third family, `small_ieee`, executes full-payload Lean arithmetic
in precisions 2, 3, 4, and 8 with two exponent ranges each, against pinned
Rocq SingleNaN arithmetic. Each row runs addition, subtraction, multiplication,
division, square root, and fused multiply-add in one of the five modes.
Eighty-seven columns retain raw validity, the converted three inputs, and all
six results through three independently called public entry points: full-payload
`Binary`, direct `BinarySingleNaN`, and the source-mode SingleNaN facade.
Every pair in the twelve-value boundary pool is included; FMA's
third operand rotates through that pool and is not exhaustively enumerated.
Seeded supplemental triples add coverage beyond the boundary pool.

This family deliberately erases NaN payloads using a fixed valid handler;
the separate binary32/64 mode bridge checks payload policy. It requires
`1 < prec < emax`, because the chosen payload must fit. Invalid finite raw
carriers are visibly converted to NaN rather than silently treated as valid
arithmetic operands. Three separate live addition-to-subtraction mutations
alter one public entry point at a time; each must fail in both Lean paths,
and the unaffected result columns must stay equal. The paired one-bit fixture
above covers a format outside this full-payload family's domain.
It is included automatically in the combined runner, or run it
alone with `--operations small_ieee --seed 491733 --samples 10`.

The twenty-fourth family, `ieee_round`, executes `binary_round_aux` and
`binary_round` through both SingleNaN and full-payload wrappers. Sixteen
columns retain all four results, including full NaN sign/payload. Its nine
formats deliberately include nonpositive precision and `emax <= prec`:
these raw functions have no precision premises in the pinned source.
Only the source carrier's positive argument to `binary_round` is enforced;
the auxiliary mantissa is signed. All five modes, both signs, and all four
discarded-part locations are exercised. Negative raw mantissas are tests
of the total API, not witnesses satisfying its real-value theorem.

Seed `826411` with 150 supplemental samples per format found 197 differences
in 6,354 cases. All involved negative auxiliary mantissas; the ordinary
positive-mantissa `binary_round` outputs agreed in that run. The cause was
using the nonnegative-only `shr_truncate` equivalence without its condition.
The correction uses signed shifting for negative inputs. Every discovered
input is retained in `scripts/fixtures/RawIEEERoundingReplay.json`; the
combined runner replays that file independently of its random seed:

```sh
uv run scripts/flocq_bridge.py --flocq-dir /path/to/pinned-flocq \
  --replay scripts/fixtures/RawIEEERoundingReplay.json
```

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

The twenty-fifth family, `single_helpers`, calls the newly executable helper
exports themselves. A row carries precision, maximum exponent, rounding mode,
raw input constructor/sign/mantissa/exponent, a scaling shift, and a separate
signed normalization mantissa. It observes raw validity before conversion;
the converted input; normalization; both one constants; scaling;
decomposition; alternate ulp, positive predecessor and successor; the
decomposition exponent; and both exported signed-shift aliases. All **46**
fields are mandatory.

The family spans one-bit through IEEE binary64 formats, all five modes,
invalid raw encodings, nonfinite values, signed zeros, and shifts crossing
underflow/overflow. Its operation types require `0 < prec < emax`; it does not
invent calls outside those carrier hypotheses. Total-function comparisons of
`Bulp'` on nonfinite inputs and `Bpred_pos'` on negative inputs are not claims
that their conditional correctness theorems apply there. The two shift aliases
expose Rocq Stdlib `SpecFloat.shr_fexp` through Flocq notation rather than a
standalone declaration defined in Flocq's own sources.
The test header permits powers through exponent 5,000, matching the other
large-format bridges. It still rejects all warning-bearing or partially
reduced output. A live regression removes this resource option to reproduce
the binary64 threshold failure, then checks three-path agreement with it.

## 4. One command runs all three

From the repository root:

```sh
bash scripts/test_flocq_conformance.sh
```

This creates and builds a detached reference worktree, runs the standalone
Rocq and Lean checks, runs all six differential bridges, and executes their own
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
six full-payload results: add, subtract, multiply, divide, square root, and fused
multiply-add. These first nine columns preserve NaN signs and payloads and
check the source's first-NaN propagation policy. Another 48 columns observe
the six direct SingleNaN results and the six source-mode facade results,
each as `(kind, sign, mantissa, exponent)`. NaN has one constructor in those
two APIs; this does not erase the separate full-payload observations.
The complete 57-column row is retained with its column names in the receipt.

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
Two further live mutations independently change direct and source-mode
SingleNaN addition to subtraction. Both Lean execution paths must disagree
only in the mutated API's result fields; every untouched field must still
match pinned Rocq. Literal directed-tie and NaN-constructor checks additionally
pin the serialization layout. All 57 columns and all three execution paths are mandatory. Timeout
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

The later 57-column bridge passes **490 cases and 490 kernel equalities**,
seed `832561`, in 529.655 seconds, with 49 cases per format/mode group. This
tests all three public APIs, unlike the earlier nine-column receipt. It shares
the unchanged library source SHA-256
`17689e21deca9fc135815da4c8f10276cb6099dcc9c5b1568bc6b98d51e8ef66`
with the passing 27,771-case all-family core run (seed `828431`, 3,081.590
seconds). The audit ledger retains both separate reports and their scopes.

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
