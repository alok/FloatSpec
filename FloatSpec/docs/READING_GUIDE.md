# FloatSpec, read from start to finish

FloatSpec is a Lean port of [Flocq](https://gitlab.inria.fr/flocq/flocq), a
mathematical library for floating-point formats and operations. The short
version is: **describe the right values, compute the right answers, prove the
right statements, and check that “right” still means what Flocq means.**
Those are separate jobs. A program can compile while its specification is wrong.

For a seven-part runnable introduction, start with
[the guided demo and exemplar reading list](DEMO_EXEMPLARS.md):
`lake exe floatspec_demo`.

This guide follows those jobs in order. The detailed
[original audit](FLOCQ_CONFORMANCE_AUDIT_2026-09-18.md) and
[independent continuation audit](ASTRA_AUDIT_2026-09-19.md) retain the
declaration-by-declaration findings and historical milestones.

## Wake-up summary — September 20, 2026, 16:01 UTC

**The port builds and runs on macOS with Lean 4.34.0, but it is not yet a
fully source-audited port.** All 35 built Flocq module names have Lean
counterparts. Four native/decoder proof obligations remain explicit, and
much of the existing theorem-by-theorem source comparison remains undone.
File coverage is not a completion percentage.

The latest verified library and tests are on the
[review branch](https://github.com/alok/FloatSpec/tree/codex/astra-flocq-audit).
Run `lake exe floatspec_demo` for the seven-part native executable.
Its examples and the **6,221-job build** pass. Fresh compiled checks cover
**13,553 declarations / 58 modules**, find exactly the four recorded proof
debts, and validate **262 pinned source anchors**.

The main conceptual repair is separating a **raw encoding**, a **canonical
value**, and a **native machine float**. Raw `(3,-1)` denotes 1.5 but is not
canonical binary64. Its raw square is `(9,-2)`; converting first and using
the primitive API gives a canonical encoding of 2.25. Both are source
behavior. Confusing these interfaces caused the old comparator and converter
bugs, now repaired with saved counterexamples. The demo walks through them.

The newest type repairs preserve equally important distinctions. A
predicate-to-rounding constructor now returns its value/function *with its
proof*, as Flocq does. FLX's two unit-value laws now accept all integer
precisions, also as Flocq does; this does not say an invalid precision
describes a valid format. Paired Lean/Rocq clients and closed Lean proofs
check these boundaries. Six more parity/symmetry interfaces now expose only
the assumptions in their compiled Flocq counterparts. In particular,
negation symmetry does not require the conditions used to prove
nearest-even correctness. There are **98** compiled premise guards, with
deliberate failures testing the guard itself. Sections 3 and 4 explain them.

**Execution evidence, with its limits:** the prior frozen primitive snapshot
passes **4,970 cross-tests**, seed `844763`, with compiled Lean, kernel Lean,
pinned Rocq, and 4,970 generated kernel equalities. The expanded harness
detects **40** independently corrupted API/instance/exponent observations.
The current persistent native bridges require four paths—native FFI,
compiled model, kernel model, Rocq—and pass their **19-test** harness.
Those are four executions inside the three verification loops, not four
independent proofs. Earlier 522-word and 1,224-pair scratch runs remain
separate evidence on the older snapshot.

**The broad rerun is running, not counted as passed.** It started at
14:38 UTC on pushed commit `5a6d16df`. The source/trust gates, pure Rocq
suites, pure Lean suites, and seven-part demo have passed on this snapshot;
the differential corpus and harness stages are still in progress.
The 13:57 run
on `2282a69b` passed source/trust gates, pure Rocq suites, Lean fixed fixtures,
and the demo, but was explicitly interrupted after a scheduling bottleneck
was identified. It retains an error result: 1,755 compared cases and 1,754
completed generated proofs, not a successful full run.
The exact **48,614-case**, seed-`848933` corpus is running again with 378
batches instead of 2,502; no inputs are removed or reordered. The integrated
87-case mixed-family pilot already passes in all three paths with all
87 generated proofs. Timeouts and interruptions remain errors.
The earlier 200-case primitive timeout is also retained alongside its
successful explicit smaller-batch replay. The
[audit ledger](ASTRA_AUDIT_2026-09-19.md) keeps exact snapshots and receipts.

Continue with sections 1–6 for the mathematical story.
The [demo guide](DEMO_EXEMPLARS.md) gives runnable examples, the
[three-loop guide](THREE_VERIFICATION_LOOPS.md) explains the tests, and the
[focused review ledger](SOURCE_CONTRACT_REVIEW.md) names the reviewed
contracts without certifying their surrounding modules.
Local macOS success is not a green hosted-CI claim: fork CI has a separate
known dependency-cache/toolchain mismatch.

**Newest semantic repair:** Pff's source-facing rounding now uses Rocq's
logarithm convention: `ln x = 0` when `x ≤ 0`. Lean's `Real.log` instead uses
the absolute value there. At radix −2 and input 2, the old formula returned
`(2,0)` while pinned Rocq returns `(-4,-1)`. Both records denote two, but they
are not the same source result. Paired closed Lean/Rocq regressions pin the
correct records for inputs 2 and −2. A closed Lean theorem proves that this
repair leaves **every positive-radix result unchanged**, at every precision
and real input. This is a mathematical definition repair, not a native
execution claim about real-number logarithms.

The old broad run remains frozen in its original worktree. This repair is
built and checked in a separate isolated worktree, so that run's evidence is
not silently relabeled as covering the new definition.

**New executable Pff interface:** source-facing neighbors and parity now use
one explicit integer radix, as pinned Flocq does. For a valid base-three
bound, the normalized successor of one is `(4,-1)`, meaning four thirds.
The older wrapper indexed by base two returns `(3,-1)` even when its extra
argument is `3`; that argument is ignored. The two interfaces are now
separately classified, not silently identified. Two closed carrier-bridge
theorems cover the raw neighbors; no global normalization equivalence is
claimed. Eighteen existing integer-only APIs now compile and run after
removing unnecessary `noncomputable` markers, without body or type changes.

Run `lake env lean --run scripts/fixtures/PffWalkthrough.lean` for this
small, linear example. Paired permanent Lean/Rocq fixtures check its records
and parity. The integrated **2,772-case / 56-column** profile now passes
in compiled Lean, kernel Lean, and pinned Rocq, with all 2,772 generated
kernel equalities. It also passes **45,368** independent exact-rational
assertions, including **3,510** premise-gated canonical-neighbor checks.
All **16** harness tests pass: every deliberately corrupted observation
column is detected in both Lean paths, compiled-only corruption is reported
and replayed, matching wrong outputs fail the independent oracle, and a
false generated Lean regression is rejected by the kernel.

Reviewable work is on
[`alok/FloatSpec:codex/astra-flocq-audit`](https://github.com/alok/FloatSpec/tree/codex/astra-flocq-audit).
Your fork is the default remote; BAIF remains `upstream`.
The original checkout, independent Claude changes, and modified
`Deps/flocq` are preserved. Current work uses an isolated worktree and a
separate clean pinned Flocq reference.

## 1. Start with one small rounding problem

Imagine binary floating point with three significant bits. Around one, the
representable values include `1.00₂ = 1` and `1.01₂ = 1.25`.
The exact value `1.001₂ = 1.125` lies halfway between them.

First compute the exact value and identify the adjacent representable values.
Then choose a rounding rule. Nearest-even chooses `1`: its three-bit
significand is `100₂`, whose last bit is even, whereas the upper choice has
`101₂`. Upward rounding chooses `1.25`. Downward and toward-zero rounding
choose `1` for this positive input. Nearest-away chooses `1.25`.

That separation is the architecture of the port:

- **Core** describes values, formats, magnitudes, and rounding predicates.
- **Calc** computes integer mantissas/exponents and records where the exact
  result lies relative to a rounding boundary.
- **IEEE754** adds finite exponent limits, signed zeros, infinities, NaNs,
  payload policies, and actual bit encodings.
- **Prop** proves relationships and error properties on top of those
  definitions. **Pff** connects an older floating-point presentation.

This example is executed and proved in both
[`RoundingWalkthrough.lean`](../Test/RoundingWalkthrough.lean) and
[`RoundingWalkthrough.v`](../../scripts/fixtures/RoundingWalkthrough.v).
The same test also rounds the negative halfway point:

| Mode | 1.125 rounds to | -1.125 rounds to |
|---|---:|---:|
| Nearest-even | 1 | -1 |
| Toward zero | 1 | -1 |
| Downward | 1 | -1.25 |
| Upward | 1.25 | -1 |
| Nearest-away | 1.25 | -1.25 |

Run `lake env lean FloatSpec/Test/RoundingWalkthrough.lean` to see the actual
sign/mantissa/exponent rows. Mantissa 4 or 5 at exponent -2 is 1 or 1.25.
Larger boundary corpora separately exercise real binary32/binary64 inputs.

One more small example explains why `Prop/Double_rounding` has hypotheses.
The exact number `73/64 = 1.140625` is just above that three-bit midpoint.
Nearest-even rounding straight to three bits gives `1.25`. Rounding first
to four bits gives `1.125`; rounding that to three bits gives `1` instead.
Extra intermediate precision is not automatically harmless. The matching
[Lean](../../scripts/fixtures/DoubleRoundingWitness.lean) and
[Rocq](../../scripts/fixtures/DoubleRoundingWitness.v) fixtures execute and
prove this example for both signs. This is a counterexample to unconditional
double-rounding equality, not to Flocq's conditional theorems.

## 2. Know what a value is before reading its arithmetic

A finite float has a sign, a positive integer mantissa, and an integer
exponent. Its mathematical value is the signed mantissa times a power of the
radix. Several representations can describe the same real number; a format
specifies which representations are allowed.

Flocq's source-shaped Lean types live in
[`IEEE754/Binary.lean`](../src/IEEE754/Binary.lean) and
[`IEEE754/BinarySingleNaN.lean`](../src/IEEE754/BinarySingleNaN.lean).
Their finite constructors carry validity evidence. The payload-preserving
type also checks NaN payload width. The older `Binary754` compatibility
wrapper is weaker: do not mistake its presence for a Flocq-valid carrier.

Validity is not just a test of the real number represented. In the three-bit
format, `(mantissa=1, exponent=0)` and `(4,-2)` both denote one, but only
the latter is canonical. The SingleNaN tests feed these representations to
the actual validators and total converters in Lean and Rocq. A source-facing
validity theorem must prove the canonical/bounded predicate, not merely a
compatibility predicate that always returns true.

Mapping a float to a real number loses distinctions. Positive and negative
zero have the same real value; NaNs and infinities need separate treatment.
Consequently, a theorem about `toReal` cannot prove equality of all raw bits.

Magnitude is another boundary worth getting exactly right. For nonzero `x`
and radix `β > 1`, Flocq's `mag x = e` means

```text
β^(e - 1) ≤ |x| < β^e.
```

The upper endpoint is strict. Thus `mag (β^k) = k + 1`, not `k`.
The Lean implementation uses floor-of-log plus one, not a ceiling. Its chosen
value at zero is one, but the magnitude bounds require a nonzero input.
[`Test/MagSource.lean`](../Test/MagSource.lean) checks the observable value
at one and the dependent bounds.

Formats then place different restrictions on mantissa and exponent.
`FIX` fixes the exponent; `FLX` fixes precision; `FLT` adds a minimum
exponent with gradual underflow; `FTZ` excludes the subnormal region.
Their source-facing predicates now explicitly describe the appropriate
witnesses. They are not merely aliases for a convenient generic predicate.

## 3. Follow the exact result to a rounded result

The integer algorithms in [`Calc`](../src/Calc.lean) avoid doing their
arithmetic with machine floating point. They align exponents, shift
mantissas, divide integers, and compute integer square roots.

The `Location` information in [`Bracket.lean`](../src/Calc/Bracket.lean)
says whether a result is exact or where an inexact result lies relative to
the halfway point. [`Round.lean`](../src/Calc/Round.lean) uses that
information, the sign, and the rounding choice to decide whether to increment.

There is also a mathematical, non-executable view. A rounding predicate
`rnd x f` says that `f` is an acceptable rounded value for `x`. Flocq's
predicate-to-function constructor requires proof that the relation is a
rounding predicate and returns both a value and evidence that it satisfies
the relation:

```lean
round_val_of_pred rnd h x : { f : ℝ // rnd x f }
```

The `.val` field gives the number; `.property` gives its proof. The function
constructor does the same for every input. This is why returning a bare real
and defaulting to zero was the wrong interface, even though the old conditional
correctness theorem could still hold. The repaired source-shaped constructors
remain `noncomputable`: selecting mathematical reals by classical choice is
not an integer rounding algorithm. Paired
[source clients](../Test/SourcePremiseContracts.lean) check their dependent
return types; closed Lean theorems also preserve the old selected value and
function on every valid input.

This explains one repaired interface mistake. Flocq's `truncate` accepts
a mantissa/exponent/location triple **and an exponent function**. The
function determines the target precision. An older Lean function with the
same name accepted an already-selected exponent instead. Both functions
were sensible, but they did not have the same contract. The source name now
has the source-shaped signature; the other utility is `truncate_at_exp`.

The IEEE layer then decides whether a rounded result is finite, subnormal,
zero, or an overflow result. Overflow is not always infinity: toward-zero
rounding selects the largest finite value. NaN propagation is a separate
policy again. The exact-payload bridge checks the first-NaN policy rather
than silently replacing every NaN by one canonical bit pattern.

## 4. Read a theorem as a contract, not as a badge

Check which assumptions a particular law actually needs. For example,
`ulp_FLX_1` and `succ_FLX_1` state formulas at the number one for **every
integer precision**, not just positive precision. With radix two and precision
zero they give `ulp 1 = 2` and `succ 1 = 3`; with precision -1 they give 4 and
5. These are legitimate equalities of the total definitions, not assertions
that such a precision describes a valid floating-point format. The repaired
Lean signatures and paired boundary proofs preserve that distinction.

Similarly, a symmetry of a rounding *function* is not the same contract as
a theorem that its output satisfies a nearest-even *predicate*. Flocq's
nearest-even and round-to-odd negation laws work for any exponent function.
The Lean signatures used to require stronger format/existence assumptions.
Both provers now check a revealing boundary: binary precision one fails the
source's `Exists_NE` condition, but its rounder still commutes with negation.
The repaired symmetry laws accept that case. Theorems actually establishing
nearest-even correctness retain their source assumptions; removing every
condition would be wrong.

Integer rounding gives a compact example of the executable/mathematical
boundary. `Binary.Bnearbyint` returns another float; `Binary.Btrunc` returns
an unbounded Lean integer. At `-2.5`, nearby nearest-even produces the float
`-2`, nearby nearest-away produces `-3`, and truncation produces the integer
`-2`. The source defines truncation of NaNs and infinities as integer zero;
that behavior must be read from the definition, not guessed from a native cast.

The public truncation operation now executes the source integer algorithm:
inspect the sign/mantissa/exponent, run the toward-zero integer helper, and
restore the sign. Its closed correctness theorem then relates that result to
rounding the represented mathematical real. The implementation no longer
tries to execute a definition made from noncomputable reals. The paired
[`IntegerRounding` oracle](../../scripts/fixtures/IntegerRounding.lean) checks
5,125 eighth-integer cases in all five modes and checks idempotence; its
expected answers come from integer division, distance, and parity.

A Lean proof establishes **the Lean proposition actually written down**.
It does not tell us that this proposition is the one intended by Flocq.

Division provides a concrete specification lesson. The input digit counts
and exponents give a candidate quotient exponent. Flocq's magnitude theorem
states that this computed integer brackets the actual magnitude within one.
The former Lean wrapper computed that integer but ignored it in the
postcondition, forcing every caller to reconnect digit counts to magnitudes.
The corrected theorem says the useful thing directly. Its companion
`Fdiv_core_correct` relates the returned mantissa/location to the exact real
quotient without wrapping this pure mathematical claim in an `Id` computation.
Both proofs are closed; making the contract easier to apply did not change
the integer division algorithm.

For square root, it matters which kind of assumption we are removing. The
high-level bracket theorem now permits any exponent function, matching Flocq;
its former extra validity premise was unused. The core algorithm still needs
`2 * outputExponent ≤ inputExponent`. Without that condition, its integer
scaling can zero the radicand: the paired bracket fixtures show a raw call on
nine returning zero when asked for too coarse an exponent. The high-level
routine avoids this by capping the chosen exponent. A checked bracket is not
yet a theorem that a rounding format is valid or that a result belongs to it.

The FTZ layer makes a related distinction. Its source predicate gives an
explicit representation witness, with a minimum exponent and normalized
mantissa bounds for nonzero values. Membership implies membership in the
normalized and generic formats at any integer precision; the source's reverse
characterization includes positive precision. The Lean forward theorems used
to inherit that stronger restriction unnecessarily. They now match the source,
and paired proofs show that zero has a witness at every precision. A theorem
and its converse must be audited separately, even when they are packaged as
one convenient equivalence inside the implementation.

Read the **elaborated type**, including implicit assumptions. Coq can erase
an unused section parameter from an exported theorem, while Lean may retain
a section instance. An earlier broad pass found 31 such unwanted premises
across 26 exports; subsequent focused passes have found more. For example,
representing a rounded value at the input exponent
does not require a valid exponent function, and multiplication by a radix
power preserves FLX format without assuming positive precision. Typed
consumers and compiler-backed premise guards now enforce these corrected
interfaces; merely printing a name with `#check` would not do that.

The same issue affected four canonical-exponent ordering lemmas: they need
only a monotone exponent function, not a valid rounding format. The tests
deliberately use `e ↦ e + 1`, which is monotone but invalid as a rounding
exponent. Five real-comparison theorem names also used to be numeric wrappers
introduced just for documentation links. They now state actual propositions;
the older integer encoding of real comparison is still called out explicitly.

Full-payload injectivity supplies another useful example. Nonzero finite
canonical values with the same real interpretation must be equal. If zeros
are allowed, their signs must also agree: `+0` and `-0` have the same real
value but are distinct float data. Neither statement needs a global positive-
precision or `prec < emax` assumption; the constructors already supply the
relevant representation validity. The old Lean exports required both anyway.
Those extra assumptions are removed from `Binary.B2R_inj`,
`Binary.B2R_Bsign_inj`, and the canonical-mantissa theorem they depend on.
Typed Lean/Rocq consumers now enforce their premise boundary.

For example, the old `valid_binary_SF2FF` statement compared validity after
a conversion with a wrapper defined to be that same expression. It was
provable but missed the intended relationship. The repaired theorem compares
full-float validity with an independently defined SingleNaN validity
predicate, under the source's non-NaN premise.

The legacy name `valid_binary_SF` now uses this same genuine finite validity
test too. In a three-bit format with maximum exponent four, mantissa one at
exponent zero denotes one but is not its canonical representation; mantissa
four at exponent minus two is canonical. The old check accepted both because
it returned `true` for every input. A retained failing cross-test motivated
the repair, and the permanent kernel fixture rejects the malformed case.

Assumptions matter for error bounds too. In the three-bit format with minimum
exponent -4, the usual nearest-rounding relative bound is `1/8`. But the tiny
value `2^-8` rounds to zero, so its relative error is one. Below normal
magnitude, an absolute error term is needed instead. The paired
[Lean](../../scripts/fixtures/RelativeErrorGrid.lean) and
[Rocq](../../scripts/fixtures/RelativeErrorGrid.v) tests check 4,092 signed
nearest-rounding cases using exact integer arithmetic, including this
counterexample to dropping the normal-magnitude premise. Their finite grid
is separate from the universal real-valued theorems.

Sterbenz's theorem gives another useful boundary: subtraction is exact when
two positive representable operands are within a factor of two. The premise
is essential. In our three-bit example, both `1` and `1/16` are representable,
but their difference `15/16` rounds to `1`. The paired
[exact-arithmetic fixtures](../../scripts/fixtures/ExactArithmeticLaws.lean)
check the premise-respecting cases in all five modes and prove this
counterexample to removing it.

FTZ had a similar issue at the definition level. Its old predicate was simply
generic-format membership, so conversion theorems concealed the intended
normalized-mantissa and minimum-exponent conditions. The source-shaped
witness predicate is now restored, and the nontrivial equivalence proof was
completed in `d4c44d9b`. Its fresh axiom check found only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`.

Many older theorems wrap pure computations in `Id` Hoare triples. Read
these as a legacy way of presenting a mathematical proposition. The project
does not invoke `mvcgen` or `mspec`; their unused annotations/imports and
the Hoare-style linter were removed. New source-facing work prefers pure
definitions and direct propositions. Existing triples are migrated with
their callers, not removed indiscriminately.

Four explicit proof debts remain in `proof_debts.json`: raw sign-bit
negation, native `frExp`, native next-up, and native next-down.
A theorem using `sorry` remains unproved even if its statement compiles.
The lexical debt gate and compiler-level dependency audit check that these
holes are named and that no additional source declarations silently depend
on them. Neither gate judges whether every mathematical statement is right.

## 5. Run three loops, then connect them

Start with the [runnable three-loop guide](THREE_VERIFICATION_LOOPS.md).
Its combined command is:

```sh
bash scripts/test_flocq_conformance.sh
```

The first loop checks independent finite properties in Lean: midpoint
classification, quotient/remainder invariants, integer-square-root bounds,
and bit roundtrips. The second checks the corresponding properties in
pinned Flocq using Rocq. The third gives identical inputs to both ports
and compares the observable results.

One particularly readable independent check is the
[finite rounding oracle](../../scripts/fixtures/RoundingOracle.lean): enumerate
all 55 finite values of the small format, discard candidates on the wrong side
for directed rounding, and choose by exact distance and the selected tie rule.
It executes 35,845 inputs/modes on each side without reusing the rounder's
shift, digit-count, or rounding-decision algorithm. Its claim excludes
overflow and exceptional encodings, which have separate IEEE tests.

The core bridge now runs **compiled Lean, Lean kernel reduction, and Rocq
computation**. It includes ordinary inputs and explicitly labeled inputs
outside theorem preconditions, such as negative shifts or zero divisors.
Agreement on those inputs is a total-function observation, not permission
to apply a theorem without its hypotheses.

Native binary64 bridges also execute real runtime `Float` operations.
They compare unary operations and nearest-even arithmetic with both the
Lean logical model and Rocq. Signed zero is retained. NaNs are deliberately
canonicalized in these native comparisons. Native `frExp` agreement has a
nonzero-finite precondition; exceptional exponent observations are retained
and reported separately.

A separate IEEE source-API bridge covers binary32/binary64 in all five
rounding modes, including fused multiply-add and exact NaN payloads.
That bridge checks compiled integer-only Lean, kernel reduction, and Rocq,
not native hardware directed rounding. Enabling the compiled path required
removing unnecessary `noncomputable` markers and moving square root's
real-valued witness inside its erased validity proof; the arithmetic itself
still uses integers. A separate 100,100-comparison runtime grid checks the
port's own binary32/binary64 arithmetic against native Float/Float32.
The separate [SingleNaN native fixture](../../scripts/fixtures/NativeSingleNaNArithmetic.lean)
adds 200,200 comparisons through the direct and source-mode public APIs, using
seed `831557`. These are nearest-even runtime checks, not kernel proofs of
hardware behavior or tests of native directed rounding. The one-bit fixture
and Rocq bridge separately cover all five modes and FMA.

Generic and fixed-width comparison now execute the source's constructor/sign/
exponent/mantissa algorithm with result type `Option Ordering`, not arbitrary
integer codes or noncomputable real comparison. It is also checked against
native Float/Float32 comparisons. Binary32/64 delegate to the proved generic
comparison, so agreement between those two Lean entry points checks wiring,
not two independent algorithms. Generic comparison needs no positive-precision
instance; tests include degenerate formats as well as ordinary IEEE formats.
The SingleNaN Boolean APIs use the same comparator:

| Comparison outcome | `Beqb` (=) | `Bltb` (<) | `Bleb` (≤) |
|---|---:|---:|---:|
| less | false | true | true |
| equal | true | false | true |
| greater | false | false | false |
| unordered (NaN) | false | false | false |

Thus `+0` and `-0` are equal, while `NaN ≤ NaN` is false. The finite
correctness theorems relate these results to comparisons of represented reals;
they explicitly require finite inputs. The reflexivity theorem separately
includes infinities and excludes only NaN. The paired
[`BooleanComparison.lean`](../../scripts/fixtures/BooleanComparison.lean) and
[Rocq fixture](../../scripts/fixtures/BooleanComparison.v) keep these boundaries
visible and executable. Checking several Lean wrappers of this shared
algorithm is a wiring check, not several independent numerical oracles.

The direct decoder and integer-width packing families avoid
using `Float.Model.ofBits` as a substitute for the port's own decoder.

Generic successor, predecessor, and ulp now execute too, using the integer
source algorithms with their validity proofs erased at runtime. Tests compare
them with the separate fixed-width implementations, and directly with Rocq
across small and IEEE precisions. Negative minimum subnormal stepping to
negative zero, maximum finite stepping to infinity, and NaN payload retention
are explicit regression cases. The pure ordering loop checks the generic
algorithms as well as their agreement with the bit-level neighbors.

For agreeing batches, Rocq's output becomes the expected value of generated
Lean equality statements. Lean checks each with `decide +kernel`.
This bootstraps a Lean regression oracle; it is not a universal equivalence
proof. Seeds, input JSON, generated programs, outputs, and replay files are
retained. Deliberate mutations must produce failures, and interrupted,
timed-out, or source-changing runs must remain errors.

## 6. What is done, and how much is left?

On the audit Mac, the checked-in Lean `v4.34.0` toolchain builds the project.
Mathlib and CSLib remain at their reviewed rc2 source pins. Compilation,
finite execution agreement, a proof of a Lean theorem, and universal
source correspondence are four different claims.

The source pin is
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`, stored in `Deps/flocq`'s
gitlink. Tests use a separate clean reference checkout; the user's modified
nested checkout is preserved.

The pinned checkout has 34 tracked `.v` modules plus the generated `Version.v`.
All 35 built module names have corresponding Lean files or umbrella modules,
as checked directly against the pinned file list. This corrects the earlier
unqualified count of 36. The old extraction plan lists 2,548 source declarations, with
2,472 automatic pairings and 76 separately classified items. Those are
navigation counts, **not a completed-port percentage**. Its 5,951 comparison
jobs include multiple jobs per declaration, and only 27 received valid
reviewed verdicts in that historical batch.

The remaining work is principally semantic review and repair, executable
coverage, and closing the explicit native proof gaps—not merely creating
missing filenames. Much of the full theorem-by-theorem port remains
unreviewed, including legacy compatibility predicates. The
[independent audit ledger](ASTRA_AUDIT_2026-09-19.md) says precisely which
changed surfaces have been checked.

Source links make that review navigable. `@[flocq_source]` records a pinned
Coq path, line, and name; `@[flocq_local]` explains a Lean-only helper.
Twelve source files enable strict public-definition classification; a targeted
section of `Binary.lean` additionally enables the same check.
The compiler-backed validator checks all 222 registered anchors, including
combined attributes and later attribute commands. These links are metadata,
not a proof that bodies or theorem signatures correspond.

Adjacent `Source:` URLs can be opened by editors that recognize URLs.
The attribute's path string itself does not yet have a special click action;
that remains low-priority editor integration.

The useful next step is always concrete: select one source declaration,
compare its type and branches, run a boundary case through both systems,
check its hypotheses, and then inspect its proof. That is the unit of
progress the audit is tracking.
