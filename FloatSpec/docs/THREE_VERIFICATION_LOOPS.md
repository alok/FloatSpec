# Run the three verification loops

## Source-ordered prelude (September 21)

`scripts/flocq_port_queue.py` derives module order from actual `coqdep` output
and declaration order from matching-digest Rocq `.glob` files. See the generated
[queue](SOURCE_REVIEW_QUEUE.md). Its manual reviews bind direct Lean type/body
hashes and the noncomputable flag; they do not certify transitive dependencies.

```sh
lake env lean scripts/fixtures/ZauxPreludeContracts.lean
uv run scripts/zaux_prelude_bridge.py --flocq-dir "$FLOCQ_AUDIT_DIR" \
  --seed 864211 --samples 120
uv run scripts/test_zaux_prelude_bridge.py -v
uv run scripts/flocq_port_queue.py --check-lean-reviews
```

The paired Rocq fixture checks the same typed contracts and fixed observations.
The bridge calls actual conditional negation and positive iteration, compares
three execution paths and a closed geometric-sum oracle, and bootstraps checked
Lean equalities. The live test requires `FLOCQ_AUDIT_DIR` and rejects two
mutations applied to both assistants simultaneously. Nonpositive counts are
protocol errors, not silently converted into the positive integer one.

## Canonical comparison bridge (September 21)

The `prim_comparison` profile now observes 26 fields, including all twelve
opt-in dyadic comparisons on proof-carrying canonical inputs. Raw comparisons
are still observed before conversion; invalid raw records are rejected by
`SF2B'`, not silently normalized. The main library defaults to the raw API.
The trust audit explicitly imports the opt-in module so this separation cannot
hide an axiom or a proof debt.

```sh
uv run scripts/flocq_bridge.py --flocq-dir "$FLOCQ_AUDIT_DIR" \
  --operations prim_comparison --seed 864101 --samples 120
uv run scripts/test_flocq_bridge.py \
  LiveTests.test_primitive_comparison_raw_and_validated_boundaries \
  LiveTests.test_primitive_comparison_every_api_is_independently_observed -v
```

The live tests require `FLOCQ_AUDIT_DIR`; the second deliberately changes each
of 24 independently observed API results. Source snapshot `7c2c0450` passed
1,345 cases and generated kernel equalities; the 24 mutants were rejected.

The package sets `restoreAllArtifacts := true`: standalone `lake env lean`
fixtures require import artifacts in the normal build directory. With a global
`LAKE_ARTIFACT_CACHE=true` and restoration disabled, Lake can report a successful
build while those fixtures fail on missing `.olean` files. This setting keeps
the user's cache enabled while making its outputs available to the fixtures.

The aim is not to trust two matching programs blindly. We check mathematical
invariants on each side, then compare the implementations on identical inputs,
then turn the reference observations into checked Lean regression statements.

An additional independent IEEE grid oracle now audits IEEE return values
without copying the Flocq algorithm. It selects adjacent exact rational points;
square root uses squared midpoint comparisons. Run
`uv run scripts/test_ieee_exact_oracle.py -v`: fourteen oracle/receipt controls
always run, and two live Lean/Rocq tests run when `FLOCQ_AUDIT_DIR` is set.
The live tests cover 40 all-mode cases plus seven native arithmetic pairs,
produce 47 kernel regression proofs, and check 7,036 expected fields.
The next aggregate now includes this suite. It was not part of the already
running frozen aggregate, whose scripts remain unchanged. Both the native
arithmetic and all-mode bridge runners now apply these expectations to every
batch and retain independent assertion counts and oracle failures in their
reports. Shared wrong answers fail even when pairwise comparisons agree.
Logical outputs rejected by the oracle are not bootstrapped into regressions.

To audit **saved** observations independently, use
`uv run scripts/check_ieee_exact_oracle.py --profile modes /path/report.json`
(or `--profile native`). It requires a completed report, exact case/proof counts,
and every saved output path. It rejects common input/rounding corruption even
if all paths agree. Its output retains the historical source hash and explicitly
says it is not a fresh execution. Current scope includes NaN/infinite-input
arithmetic, zero divisors and negative square roots, as well as finite
overflow/underflow and signed-zero rules. The exceptional classifier retains
pinned Flocq's first-NaN payload policy; native observations canonicalize NaNs.
Hardware exception flags are not modeled, and no universal equivalence is inferred.
Two live shared mutations additionally replace FMA of infinity times zero with
the addend, and swap NaN priority in addition. Pairwise agreement remains, but
the independent oracle rejects both and prevents bootstrapping wrong expectations.

The standalone paired `scripts/fixtures/ExponentValidityBoundary.lean` / `.v`
provides eleven checked declarations explaining genuine source premises:
`Valid_exp` alone permits decreasing ULP. The alternate-binade format is valid,
contains every power of two, and has `ulp(1/2)=1/2 > 1/4=ulp(1)`.
It also represents `7/4` and `1`, but not their truncation remainder `3/4`,
so exponent monotonicity cannot be dropped from the remainder theorem either.
The ULP conclusion directly negates the overly broad monotonicity claim;
its trivial numerical side conditions are inside the proof.
All eleven Lean axiom lists exclude `sorryAx`; Rocq prints its classical-real
assumptions. This is proof-level testing of real definitions, not a native
real-arithmetic execution claim. The next aggregate runs this paired fixture,
along with the 27-client `CorePremiseBoundary` fixture; the preceding frozen
aggregate does not include them.

## Exact remainders: one premise, three checks

The paired `RemainderContracts.lean` / `.v` fixtures consume the four source
remainder types and prove the two-bit counterexample `1 - ceil(1/8)*8 = -7`.
The paired `RemainderGrid` fixtures prove and execute a complete finite grid:
55 signed inputs including zero, all pairs, and four quotient policies.
Run the compiler fixtures through `scripts/test_flocq_conformance.sh`, or:

```sh
lake env lean scripts/fixtures/RemainderContracts.lean
lake env lean scripts/fixtures/RemainderGrid.lean
uv run scripts/remainder_bridge.py --flocq-dir "$FLOCQ_AUDIT_DIR" \
  --coqc coqc --samples 0 --seed 862513
FLOCQ_AUDIT_DIR="$FLOCQ_AUDIT_DIR" uv run scripts/test_remainder_contracts.py -v
FLOCQ_AUDIT_DIR="$FLOCQ_AUDIT_DIR" uv run scripts/test_remainder_bridge.py -v
```

The bridge compares quotient, integer remainder and all four rounded-constructor
fields, then creates checked Lean equalities from the Rocq observations.
Its independent oracle uses exact rational quotient rules and enumeration of
the representable grid, not a second copy of the port's rounding algorithm.
The seed shuffles the exhaustive 12,100 inputs; nonzero random sample counts
are rejected rather than mislabeled additional coverage. Saved reports also
fingerprint the paired quotient protocol. These integer quotient routines are
test models, not established refinements of the noncomputable real operations.
Zero division here is mathematical total division, not IEEE infinity/NaN.

The seed-862513 run on `3c5a913d` passes 12,100 differential and generated
kernel checks plus 84,182 independent assertions in 453.569 seconds. Six
contract controls reject missing premises and false exactness; six bridge
tests validate the protocol and reject shared actual-program mutations of
signed division and the rounding stage. A failing compiler exit always wins,
even if a later runtime command prints a success line.

## Unindexed Pff arithmetic-contract boundary

`PffBasicSourceContracts` includes the four negation/absolute-value laws
and two addition/subtraction observer laws, with exact source types and
negative/zero-radix counterexamples in both assistants. Addition and subtraction
retain the source's positive-radix premise, including radix one.
Run `FLOCQ_AUDIT_DIR="$FLOCQ_AUDIT_DIR" uv run scripts/test_pff_basic_contracts.py -v`
for eight live mutation controls. The test deliberately removes positive-radix
premises, replaces negation by identity and subtraction by addition; both
checkers reject them.
`scripts/fixtures/PffSignLawsReplay.json` retains 72 focused raw-record inputs
across negative, zero, one and ordinary radices, both mantissa signs, zero,
and positive/negative odd/even exponents. Replay it with `scripts/pff_bridge.py`
to observe all 61 profile columns in all three paths. These executions do not
replace the universal Lean observer proofs or certify the whole Pff facade.

## Pff integer execution and constructive divisibility

`PffIntegerExecution.lean` and `.v` execute the actual `Pdiv`, `oZ`, `oZ1`,
`Zquotient`, `ZdividesP` and `maxDiv` exports. The Lean fixture also proves that
the constructive `maxDiv` agrees universally with its prior classical body.
That preservation theorem is separate from cross-assistant finite agreement.
Integer-only marker removals preserve the other four bodies and types.

```sh
lake env lean scripts/fixtures/PffIntegerExecution.lean
uv run scripts/pff_integer_bridge.py --flocq-dir "$FLOCQ_AUDIT_DIR" \
  --seed 863307 --samples 300 --output /tmp/pff-integer-results
FLOCQ_AUDIT_DIR="$FLOCQ_AUDIT_DIR" uv run scripts/test_pff_integer_bridge.py -v
```

The independent oracle uses exact rational truncation, Euclidean natural
division and finite enumeration of divisible powers. Complete optional records
are observed, not only their numeric payload. The corpus includes signed
127-bit quotients, zero divisors, smallest positives, zero/one/negative radices,
and truncated search bounds. Invalid positive carriers are rejected before
transport. Replay `scripts/fixtures/PffIntegerReplay.json` for a small boundary
set. Live mutations change both provers' programs together: floor division,
swapped quotient/remainder, a false option tag, reversed divisibility arguments,
and an always-zero search bound must still fail the independent oracle.

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

- `PrimitiveComparison`: 24 literal cases through twelve comparison APIs,
  with separate validity observations. Closed examples establish equal real
  values but unequal raw encoding order; no normalization is inserted before
  the raw observations. The Rocq primitive group executes native comparison,
  while its raw and proof-carrying groups execute integer algorithms.
- `DoubleRoundingWitness`: `73/64` rounded directly to three bits differs from
  rounding through four bits; both signs have closed equality proofs.
- `PffLogTotality`: paired closed counterexamples at negative radix retain
  Rocq's zero extension of logarithm. Lean additionally proves that the
  repaired source-facing definition preserves every positive-radix result,
  for arbitrary natural precision and real input. These are noncomputable
  real-number statements checked by the kernel, not native logarithm tests.
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

`SingleNaNHelpers` separately checks 13 literal helper results, eight
decompositions, and two signed shifts, closed independently in both assistants
and executed in Lean. The one-bit decomposition explicitly checks the branch
outside the normalized-fraction theorem's `2 < emax` hypothesis.
Two additional closed counterexamples show that alternate ulp equality needs
a finite input and positive-only predecessor equality needs a positive input.

`FrexpLaws.lean` and `.v` independently check **6,772** raw finite encodings
using explicit integer format membership and dyadic comparisons. Exactly
**2,086** are valid finite values; these must retain their sign, decompose
exactly, produce another valid finite value, and have a normalized fraction
when `2 < emax`. The other **4,686** encodings must become NaN with the source
sentinel exponent. The formats include eight-bit precision with `emax = 2`
and `3`, and parameters with an empty finite-value range. Both assistants
close the complete finite grid, and Lean also executes it. Adding one to the
returned exponent breaks both the kernel assertion and compiled check.

`NativeSingleNaNArithmetic.lean` additionally executes **200,200** nearest-even
comparisons against native Float32/Float, calling both direct and source-mode
SingleNaN APIs. Seed `831557` supplies 10,000 pairs at each width, plus ten
explicit boundary pairs per width; five operations are observed through each
API. Signed zeros are preserved and NaNs are quotiented. A reported failing
word pair can be replayed through the fixture's public `observations32` or
`observations64`; the mode bridge now calls these same SingleNaN APIs against
Rocq on those words, in addition to the full-payload baseline. This is finite native execution, not a hardware
correctness proof or a native FMA/directed-rounding test.

`CalcBrackets.lean` and its Rocq counterpart check **8,640 division** and
**2,496 square-root** brackets in bases 2, 3, and 10. Expected conditions are
integer inequalities obtained by clearing positive denominators; the oracle
uses neither another divider/square-root algorithm nor a correctness theorem.
It checks the midpoint location as well as the interval. A literal failure
outside square root's exponent premise makes that domain boundary executable.
Deliberately increasing the returned mantissa or replacing its location by
exact must break both the closed finite assertions and compiled checks.

`Test/SourcePremiseContracts.lean` additionally has 147 source-premise guards,
paired typed consumers for the Prop, integer-rounding, canonical-exponent,
real-comparison, division, square-root, FTZ inclusion, eleven FLT relationships,
two unrestricted FLX unit laws, parity/symmetry contracts, and generic IEEE comparison exports, and seven deliberate negative guard
examples. The corresponding Rocq fixture checks the paired
consumer signatures. These
checks caught real section-instance leakage that the former bare `#check`
regressions did not detect. The combined runner re-executes all these fixtures;
the CI workflow also runs their Lean side. Local success is not a claim that
hosted CI has run.

The paired `scripts/fixtures/CorePremiseBoundary.lean` / `.v` add 27
typed consumers without `Valid_exp`: sixteen generic-format/rounding exports
and eleven ULP exports. They preserve the other parameters and conclusions;
the successor upper bound still requires `Monotone_exp`. All 27 Lean
axiom lists exclude `sorryAx`. This tests the selected premise boundary,
not automatic cross-language equivalence of arbitrary theorem statements.

The FTZ guards explicitly recognize legacy `Fact (0 < prec)` instances as well
as named precision classes. A deliberate leaking instance tests that case.
Paired Lean/Rocq proofs show that zero has an FTZ witness at every integer
precision and is covered by the unrestricted forward-inclusion theorem.
The reverse source inclusion retains its positive-precision premise.

The FLT clients similarly distinguish unrestricted forward inclusions and
normal-range exponent/ulp/shift statements from genuinely restricted reverse
inclusions. Each language proves a precision-zero counterexample satisfying
all the reverse FIX-to-FLT theorem's other premises. This prevents the wider
interfaces from being mistaken for permission to remove every assumption.

The FLX unit laws are also unrestricted in the source: at radix two,
precision zero gives `ulp 1 = 2` and `succ 1 = 3`, while precision -1 gives
`ulp 1 = 4` and `succ 1 = 5`. Both provers close these examples without a
positive-precision premise. They are statements about total mathematical
definitions, not claims that a valid format of that precision exists or that
its successor is an adjacent representable number. Four guards prevent either
the named precision class or a legacy positivity `Fact` from leaking back.

The rounding-predicate clients require the exact proof-carrying result shapes:
`{f : ℝ // rnd x f}` for a value and `{f : ℝ → ℝ // ∀ x, rnd x (f x)}`
for a function. Both take `round_pred rnd` evidence. Paired identity examples
and rejection of an empty relation test this boundary; two closed Lean
theorems show that valid inputs retain the old selected values/functions.
These mathematical constructors legitimately use classical choice and do not
claim to be native-executable rounding algorithms.

Nearest-even parity statements can be formed without `Valid_exp`, and the
positive-to-signed parity implication needs neither `Valid_exp` nor
`Exists_NE`. Negation laws for nearest-even and round-to-odd are also
unrestricted in the exponent function. The source's nearest-even absolute
value theorem retains `Valid_exp`, but not `Exists_NE`. Paired typed
clients test all six repaired interfaces; eight new guards detect leaked
premises. The guard accepts several named parameters, with deliberate
instance/explicit leaks and a selective two-parameter control.
Both provers show that binary FLX precision one fails `Exists_NE`, while
its nearest-even rounding function still commutes with negation. This
checks a real domain excluded by the previous stronger Lean signature;
it does not claim the class is a necessary-and-sufficient totality criterion.

The paired `RoundNEPointContracts.lean` / `.v` clients additionally require
the concrete nearest-even result from `round_NE_pt`, now a direct proposition
with its two production Pff callers migrated. They retain the genuine
`Valid_exp` and `Exists_NE` assumptions. Four live mutation controls reject
weaker existence-only result types or a missing existence premise in both
assistants; each control first compiles its unchanged baseline.

`lake exe floatspec_demo` builds and runs the seven-part guided introduction
as a native executable, with kernel assertions and runtime checks against
literal expected answers. The combined runner executes this target as well.
The older `floatspec` executable's `main` still does nothing: running that
target is a launch smoke test only, not an arithmetic regression. Broader
native coverage comes from the four-path binary64 bridges described below.

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
`binary_round` through both SingleNaN and full-payload wrappers. The first sixteen
columns retain all four results, including full NaN sign/payload. Five further
columns now observe the local proof-carrying rounding adapter: an explicit
validity bit followed by its result, or a NaN-shaped rejection sentinel.
The source has no separate declaration for this local adapter; its oracle is
the raw source result when the adapter's validity premise holds. The flag
distinguishes rejection from an actual valid NaN. All **21** columns are required;
earlier sixteen-column receipts predate this extension. Its nine
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

The twenty-sixth family, `single_frexp`, isolates decomposition's weaker
source domain: **only positive precision**, with no `prec < emax` premise.
It compares eleven fields: raw validity, converted input, fraction, exponent,
and fraction validity. It includes nonpositive maximum exponents, equal
precision/maximum-exponent values, and precision greater than the maximum
exponent. These are source-legal parameters, not claims about IEEE hardware
formats. Invalid raw finite constructors are observed before their conversion
to NaN. Literal outputs and independent fraction/exponent mutations check the
adapter, while the paired law fixture separately checks mathematical meaning.

The twenty-seventh family, `normalize`, observes three separate entry points:
full-payload `Binary.binary_normalize`, legacy raw `binary_normalize`, and the
proof-carrying SingleNaN facade. It serializes each result independently into
four fields, for twelve required fields. Inputs retain a signed integer
mantissa, exponent, mode, and zero sign. The source-facing normalizers require
`0 < prec < emax`; invalid parameter combinations are rejected before code
generation, rather than silently supplied with invented proof arguments.
One-bit through binary64 formats cover both zero signs, halfway cases with
even and odd lower mantissas, subnormal transitions, and overflow. Separate
mode mutations affect one export at a time and must leave every other column
unchanged. Run just this family with `--operations normalize`.

The paired `Normalization.lean/.v` fixtures additionally check 150 literal
normalizer observations and six result-validity adapter boundaries. Their
expected values are written out, not generated by another normalizer.
The adapter's result-validity check is intentionally weaker than a blanket
assumption that format parameters describe an ordinary IEEE format: a
malformed format can still produce a valid zero. Compilation does not justify
discarding that distinction.

The twenty-eighth family, `prim_comparison`, keeps fourteen columns:
four raw comparisons, two input-validity flags, four primitive comparisons,
and four proof-carrying comparisons. Raw encodings are observed before any
validating conversion. The source mantissa is positive, so zero/negative
mantissas are rejected by the shared corpus validator instead of silently
coerced. Noncanonical positive encodings, extreme exponents, subnormal and
normal boundaries, both signs of zero, NaNs, and infinities are included.
Rocq's middle group executes its native primitive; the other two groups are
integer algorithms. Run it with `--operations prim_comparison`.

This family guards a distinction hidden by real-value equality:
`(3,-1)` and `(6,-2)` both denote 1.5 but the raw source comparator returns
greater-than. Both are invalid binary64 encodings; converting them first
would merely compare NaNs and hide the raw mismatch. Four permanent inputs
in `PrimitiveComparisonReplay.json` retain the source-contract regression.
The paired fixture checks 24 literal cases; twelve separate mutations alter
exactly one comparison column each and must fail in both Lean paths.

The twenty-ninth family, `prim_conversion`, tests the total raw-to-primitive
conversion in fourteen columns: input validity, converted result, its
proof-carrying projection, output validity, and the rejecting `SF2B'` result.
The numeric conversion is observed before any rejecting adapter. Both signs,
special values, noncanonical encodings, mantissas crossing uint63 boundaries,
subnormal double rounding, and enormous clamped exponents are included.
`PrimitiveConversionReplay.json` retains four original mismatches. Paired
pure fixtures check 31 literal results and prove that one-shot normalization
differs from the source conversion. Three deliberate replacements test that
rejection, omitted wrapping, and collapsed rounding stages are all detected.

The source's finite mantissa is positive; zero is rejected by this shared
corpus validator. The Lean definition's valid-input shortcut retains the
existing roundtrip proofs, but these finite observations do not constitute
a universal cross-prover equivalence theorem. Run the slice with
`--operations prim_conversion`.

The thirtieth through thirty-second families observe every remaining primitive
execution entry point at its public name:

- `prim_arithmetic` has 70 columns: three raw algorithms, two input-validity
  flags, five primitive operations, four arithmetic notation instances, and
  five proof-carrying arithmetic operations. Only the final group varies with
  the selected rounding mode; the primitive contract is nearest-even.
- `prim_helpers` has 68 columns: input validity, raw scaling, uint63 conversion,
  the two named primitive scaling exports, unsigned shifted scaling, ulp,
  neighbors, the constant two, and three decompositions including their
  exponents, plus the proof-carrying scaling/ulp/neighbor exports.
- `prim_round` has 16 columns: primitive-specialized raw rounding auxiliary,
  positive-mantissa rounding, signed normalization, and proof-carrying
  normalization under the selected mode. It includes negative auxiliary
  mantissas and noncanonical positive inputs, without claiming that the
  real-value theorems hold outside their premises.

These adapters call raw operations before conversion. Their primitive and
proof-carrying groups use actual numeric `SF2Prim`, not the rejecting
`SF2B'` adapter. Thus invalid encodings can become ordinary numeric values,
and raw and converted results need not have the same encoding. The corpus
keeps raw addition exponents bounded to avoid enormous exact alignments;
this is a resource bound on testing, not a new API precondition.

The paired `PrimitiveExecution` fixtures independently check 33 public
definitions and four notation instances against literal values, and separately
check three returned decomposition exponents. A closed example in both
provers distinguishes raw `(9,-2)` from canonical 2.25 after squaring raw
`(3,-1)`. The fixture executes actual clients, so reintroducing a
`noncomputable` dependency makes it fail even when logical reductions remain
possible. Forty deliberate mutations cover each of the 33 APIs and four
notation instances, plus the three returned exponents independently. Every
mutation must change its designated result and leave other columns intact in
both Lean execution paths.

The requested batch size is a maximum, not a promise to put every family in
one large compiler input. The three primitive families are capped at 25 cases
per homogeneous batch: a saved 200-case arithmetic input exceeded the kernel
runner's 120-second limit, while the same inputs passed in eight smaller
batches. Input order, duplicates, global case indices, and replay contents are
preserved. Ordinary families may share a batch: each result row is still
validated against its own operation's exact column count. For seed `848933`
and 100 samples, this reduces 48,614 unchanged inputs from 2,502 mostly tiny
batches to 378 batches. Heavy families remain isolated and capped. An actual
87-case mixed-family replay observes all 29 ordinary families in one batch
and checks all three paths plus generated kernel equalities.
Reports record `requested_batch_size`, `batch_size_limits`, and `batch_policy`.
Timeouts still fail the entire run; the runner does not silently retry or call
a completed prefix a pass.

Run only these families with
`--operations prim_arithmetic,prim_helpers,prim_round`. Exact run counts,
seeds, source hashes, and completion status belong in the audit ledger,
not in an assumption that merely launching this command is success.

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

## 5. Native binary64: four execution paths, one input

`scripts/native_ieee_bridge.py` adds actual native execution via `lean --run`
and its floating-point FFI. For each raw 64-bit input, it compares five fields:
decoded/canonicalized input, successor, predecessor, `frExp` significand, and
signed `frExp` exponent. Three further paths execute the Lean logical Flocq
carrier as compiled code, reduce that same carrier in the kernel, and execute
the pinned Rocq definitions with `vm_compute`. These are four execution paths
inside the three verification loops, not four independent algorithms or proofs.
The logical model adapter is executable without changing its body or type.

The boundary corpus covers both signs, zero, subnormal powers of two and their
neighbors, minimum normals, exponent transitions, maximum finite values,
infinities, and signaling/quiet NaN payloads. Seeded arbitrary bit patterns
supplement that corpus. All four result streams are retained independently;
reports include a separate `compiled_model_cases` count. Missing a path is an
error, never an implicit downgrade to a weaker comparison.

Two qualifications are deliberate and visible in the report:

- NaNs are observed through the single-NaN model. All payloads and signs map to
  `0x7ff8000000000000`; agreement does **not** establish payload preservation.
- Native `frExp` equivalence is asserted only for nonzero finite values, as in
  the theorem's precondition. The observed exceptional exponent is `0` on this
  Mac, versus `-2101` in the logical Flocq model. Those exceptional observations
  remain in the report; their input decoding and successor/predecessor results
  are still compared. Both compiled-model and kernel-model versus Rocq
  comparisons include **all** fields on **all** inputs, including exceptions.

Every agreeing model/Rocq row becomes a checked Lean equality. This proves the
individual logical-model result, not the native FFI correspondence theorem.
The native minimum-subnormal case is also a permanent model regression in
`FloatSpec/Test/NativeIEEE.lean`, paired with `scripts/fixtures/NativeIEEE.v`.
Independent mutations alter only native successor or only compiled-model
observations. A compiled-only error must still produce a mismatch and replay
even when the separate kernel/Rocq equality proof succeeds.

```sh
uv run scripts/native_ieee_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 20260919 --samples 200 --batch-size 25
# Use --replay /path/to/cases.json to run exactly the same bit patterns again.
```

The combined shell runner accepts `FLOCQ_NATIVE_SAMPLES` and
`FLOCQ_NATIVE_BATCH_SIZE` for this additional loop.

## 6. Arithmetic at real binary64 sizes

`scripts/native_arithmetic_bridge.py` sends each pair of raw binary64 words
through native Lean arithmetic, compiled and kernel execution of the port's
`FaithfulPrimFloat` operations, and
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
swaps native operands and independently swaps only compiled-model operands,
and verifies that timeout/interruption records are
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

## 10. Pff records, explicit radices, and indexed compatibility

`scripts/pff_bridge.py` reuses the strict three-path core runner with an
isolated profile. It observes 61 integer columns: source digit, shift,
addition, subtraction, normalization, sign/absolute value, bounds,
neighbors, parity, exponent-preserving zero, the zero predicate and unindexed
multiplication, plus the older indexed entry points. The legacy
normalized neighbor/parity columns explicitly say `type_radix_2`; their
Rocq counterparts use two even when the ignored legacy Lean argument is a
different integer. This distinction is an API boundary, not a mismatch
exception that discards fields.

```sh
uv run scripts/pff_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 850021 --samples 300 --batch-size 50
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_pff_bridge.py -v
lake env lean --run scripts/fixtures/PffWalkthrough.lean
```

There are 2,472 fixed cases plus two cases per requested seeded sample
(one unrestricted and one satisfying the neighbor premises). The corpus
includes negative/zero/unit radices, zero precision, 192-bit mantissas,
noncanonical and out-of-bound inputs, exact power boundaries, and exponent
boundaries. Natural arguments use Rocq's binary `Z.to_nat` codec to avoid
large unary-literal warnings without relaxing stderr rejection. Source
integer domains are retained even where mathematical correctness theorems
would require stronger premises.

After all three paths agree, an independent exact-rational oracle checks
value preservation, arithmetic, parity, zero normalization, and a
division-based digit count. Canonicality, strict ordering, and exact adjacency
assertions for neighbors apply only
when radix is at least two, precision is positive, the bound is exactly
radix-to-precision, and the input is bounded. Report metadata counts these
assertions separately and records the exact failing input on any oracle
error. Matching wrong outputs are therefore not automatically a pass.

The runner produces kernel-checked Lean equalities from Rocq observations,
retains the corpus/seed and mismatch replay, and rejects interrupted or
timed-out runs. Its fresh build targets the actual source facade; a supplied
`--skip-build` is explicit in the report. The profile restores every shared
runner binding on exit, including exceptions. Harness tests corrupt each
of the 61 observation columns, distinguish compiled-only mistakes, reject
wrong bootstrap expectations, and test partial/invalid outputs and failure
reporting. Actual-program shared mutations erase a zero's exponent or negate
one multiplication operand in all three paths; independent exact record checks
reject both before generating kernel regressions. All twenty harness tests pass.

Paired `PffBasicSourceContracts` fixtures check the exact unindexed interfaces:
`Fzero`, `is_Fzero`, `Fmult` and four observer laws. The multiplication theorem
accepts radix one (`0 < radix`), while the two forward zero laws accept every
integer radix. A proved radix-zero counterexample guards the multiplication
premise. This is distinct from a needlessly strengthened indexed signature.

Paired `PffExecution` fixtures exercise all eighteen newly
computable existing APIs; separate `PffLogTotality` proofs cover the
noncomputable real-logarithm convention.

### Auxiliary Pff bounds and local numerical helpers

`scripts/pff_aux_bridge.py` adds ten columns for actual `make_bound`,
`bsingle`, `bdouble`, and two normalized records through `PFnormalize`.
Unlike the unrestricted Pff record profile above, this profile rejects
radices below two because `make_bound` exports a valid-radix carrier.
Signed precision and exponent bounds remain unrestricted. The adapter's
reference explicitly uses `Z.abs_nat precision`; the report distinguishes
this mapping from the three source exports.

```sh
uv run scripts/pff_aux_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 852017 --samples 200 --batch-size 50
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_pff_aux_bridge.py -v
lake env lean FloatSpec/Test/PffAuxExecution.lean
```

The fixed corpus contains 2,016 boundary cases, followed by seeded samples.
Negative/zero precisions, both signs of exponent bounds, exponent endpoints
near subnormal limits, zero, and 192-bit random mantissas are retained.
Independent exact-rational checks cover value preservation, bound fields,
zero normalization and conditional canonical results. All ten differential
columns have live mutation tests. The kernel/runtime local-helper oracle
also rejects reversed comparisons; a separate closed kernel statement
positively establishes that the corrupted finite claim is false. A failed
compiler invocation alone is not that evidence.

The pure Lean fixture independently checks 70,227 numerical comparison,
maximum and minimum cases at radices two, three and ten, plus 225 smaller
kernel cases and all seven newly executable entry points. Those local
helpers are not separately invented Flocq exports. Paired Rocq fixtures
check the source bounds and a nontrivial normalization. The legacy identity
helper's idempotence theorem is explicitly not a normalization theorem.

### Real-valued Pff signed rounding

`PffRoundingSource.lean` and `.v` check ten identical literal observations
through the actual upward, downward and nearest-even definitions. Both
proof checkers cover positive/negative halfway ties, both strict-distance
branches, exact input, zero, negative radix and precision zero. The last
two test total definitions outside the general correctness premises; they
do not assert those parameters describe a valid floating-point format.
The Lean statements print their axiom dependencies, with no `sorryAx`.

```sh
lake env lean FloatSpec/Test/PffRoundingSource.lean
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_pff_rounding_contracts.py -v
```

Each live negative control checks the original halfway claim, substitutes
downward for nearest-even observation and requires semantic rejection, then
positively proves the altered expected answer. This distinguishes a detected
wrong answer from a broken compiler invocation. These are mathematical
kernel checks of noncomputable real-valued definitions, not native executions
and not a three-path runtime bridge.

### Double-rounding definitions and premise contracts

The paired permanent `DoubleRoundingContracts` fixtures check nine exact
definition bodies and six theorem clients. Multiplication uses no
`Valid_exp` assumptions; addition/subtraction, square root and division
retain the reviewed assumptions. Both assistants prove a concrete pair of
exponent functions separates the ordinary and radix-at-least-four square-root
hypotheses. Three live controls reject off-by-one body drift in both languages
and reintroduced extra multiplication premises in Lean.

```sh
lake env lean FloatSpec/Test/DoubleRoundingContracts.lean
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_double_rounding_contracts.py -v
```

These are persistent checks of the reviewed exports, not native real-valued
execution, exhaustive theorem auditing, or a proof of whole-module equivalence.

### Targeted Pff neighbor premises

The Pff profile now adds one premise-respecting random case for each broad
random case. Unrestricted random bounds almost never equal `radix ^ precision`,
so increasing that corpus alone had not increased the conditional neighbor
coverage. The new generator deliberately chooses that equality, positive
precision, a bounded signed mantissa and an exponent above the minimum.
It samples radices 2, 3, 10 and 16, both signs, zero, and the minimum-exponent
boundary. Its current Nat-transport bound is capped at 4096.

The original seed-859111 targeted replay had **200** cases and **1,000**
premise-gated normalization/neighbor assertions. Its September 20 continuation
replays the same inputs with a stronger oracle: **1,400** such assertions,
including **400 exact adjacency checks**. Every compiled/kernel/Rocq observation
and generated Lean equality passes in both runs.

The independent oracle views a format as one bounded integer grid per exponent.
At each exponent, exact rational floor and ceiling locate the nearest strict
neighbors. It stops after the grid's positive unit exceeds the input's absolute
value: all later nonzero values are farther away, and zero is already present.
This does not copy Flocq's normalization or neighbor case splits. The harness
also compares it with explicit finite-format enumeration over 180 queries.

Crucially, a canonical value on the correct side can still be the wrong neighbor.
For base three, precision two, the successor of one is `4/3`, not `5/3`;
its predecessor is `8/9`, not `7/9`. Two new mutations make all three result
streams agree on those wrong answers; the independent oracle rejects both.
All **19** Pff harness tests pass, including the existing generator-domain
check over 1,000 inputs. This is finite evidence for adjacency, not a universal
adjacency or source-equivalence proof.

### Logical-model adapters and integer bit inputs

`model_adapter_bridge.py` observes five paths at both binary32/binary64:
raw source decode/encode, source-to-model, UInt-model-to-source, its model
roundtrip, and source/model/source roundtrip. The model paths explicitly
canonicalize NaNs. Only routes entering through UInt wrap arbitrary integers;
the source total integer decoder uses its sign threshold even out of range.
This is an adapter-policy comparison, not a claim that Flocq exports Lean's
logical model and not a native float FFI test.

```sh
uv run scripts/model_adapter_bridge.py --flocq-dir /path/to/pinned-flocq \
  --seed 854033 --samples 500 --batch-size 25
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_model_adapter_bridge.py -v
lake env lean FloatSpec/Test/NativeModelAdapters.lean
```

The pure Lean oracle separately executes 60,032 inputs / 300,160 observations
and closes a 32-input kernel grid. Paired Rocq examples pin signed NaN,
wider-than-word finite input and negative-integer signed zero. The bridge
retains full corpus, seed, generated kernel equalities and oracle counts;
all columns have live mutation controls in both widths. Matching corrupted
answers are rejected by an independent arithmetic field classifier.

### Classical witness result types

`LpoSourceContracts.lean` and `.v` compile consumers of `LPO_min`, `LPO`
and `LPO_Z` that require proof-carrying alternatives, not a theorem about an
unrelated optional value. They extract a witness with its membership proof,
test a negative-only integer predicate and reject the impossible positive
branch for an empty predicate. Lean additionally proves universal projection
equalities to the old natural optional choices. No equality to the old
arbitrary integer choice is claimed.

```sh
lake env lean FloatSpec/Test/LpoSourceContracts.lean
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_lpo_contracts.py -v
```

The live controls first compile the unmutated clients, then reject all three
former property-only result shapes in Lean and an optional proof-erased result
in Rocq. Arbitrary-predicate LPO is genuinely noncomputable here: a successful
kernel/type check is not native execution of a predicate decision procedure.

### ULP witness construction and its validity premise

The permanent `UlpSourceChoice.lean` / `.v` pair checks exact bodies for
the negligible-exponent projection, ULP and its neighbor functions. Lean
additionally proves preservation of every previous ULP value under valid
radix/exponent assumptions. Both assistants prove that identity exponents
are invalid and that two admissible witnesses can give different powers.

```sh
lake env lean FloatSpec/Test/UlpSourceChoice.lean
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq uv run scripts/test_ulp_choice_contracts.py -v
```

Three live controls first compile the unchanged fixtures, then reject
zero-spacing body drift in both assistants and the removed validity premise
in Lean. These are kernel-checked mathematical contracts, not native
execution of the real-valued ULP function or arbitrary-predicate choice.

Twenty-two paired typed clients additionally consume the reviewed ULP/absolute-
value laws without irrelevant exponent-validity premises, and the integer
witness-equality lemma without a radix. The shared compiled-type guard covers
the 21 widened source laws and one compatibility wrapper. All 30 printed
Lean fixture axiom lists exclude `sorryAx`. The preservation theorem still
requires valid exponents; its negative control targets that theorem specifically.

### Nearest-rounding policies must survive in the theorem type

`scripts/fixtures/UlpNearestChoiceContracts.lean` and `.v` contain eight typed
clients for the supplied-policy midpoint/neighbor laws. They also prove that
rounding `1/2` to integers gives `0` with the false tie policy and `1` with the
true policy. The real-valued example is a closed mathematical proof, not
native real-number computation. A separate integer `round_N`/`cond_incr`
example actually evaluates to `[0, 1]` in both assistants and has a closed
kernel proof. All ten Lean axiom lists exclude `sorryAx`; the executable
example uses no axioms.

```sh
lake env lean scripts/fixtures/UlpNearestChoiceContracts.lean
FLOCQ_AUDIT_DIR=/path/to/pinned-flocq COQC=/opt/homebrew/bin/coqc \
  uv run scripts/test_ulp_nearest_contracts.py -v
```

Four mutation tests first compile the unchanged fixtures, then reject either
erasing the second choice from the expected contract or selecting the false
policy while expecting the true-policy midpoint result. This protects the
statement as well as its proof. The combined runner includes both fixtures
and all four controls.

The seed-861047 integrated-oracle runs completed on source `eb306bb5…722eb6`:
1,104 native-arithmetic cases and 390 all-mode cases, every generated kernel
equality, and 67,627 independent expected-field checks. The oracle's scope
at that run was finite-input arithmetic: exceptional-input results still had
pairwise cross-checking but were outside the independent expectation gate.
The eight later theorem repairs have source hash `687aa7a8…395d2`; their full
build, typed clients and mutation checks are separate evidence.

## 11. What this still does not establish

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

The larger frozen September 20 rerun also completed: **55,162 differential
case executions and generated kernel equalities**, including 292 saved replay
cases, plus **119** core/native/IEEE bridge-harness tests. Every one of its
ten reports records source fingerprint
`32ec11b5b0ac7fb6cba5d58635307df2857568f7228c9554e8343d498305dfbf`.
The final process exited zero and emitted the combined success marker.
Its core-only corpus has 48,614 cases; the remainder covers native unary,
arithmetic, all modes, scale/decomposition and integer rounding. Native scope
exceptions remain explicit in the reports, not silently treated as universal
four-way agreement. Later Pff/model/LPO changes have separate newer-snapshot
receipts and must not be conflated with this frozen full-run result.

The September 20 final receipt is available as
[`VERIFICATION_RECEIPT_2026-09-20.json`](VERIFICATION_RECEIPT_2026-09-20.json).
It separately records the newer **8,328-case** Pff/aux/model stress group and
the **360-case** replay after theorem-signature corrections. All requested
cases, comparisons and generated kernel equalities are complete in each
included report. Snapshot separation is deliberate: the larger old run was
not rerun wholesale after the final theorem-only changes.
