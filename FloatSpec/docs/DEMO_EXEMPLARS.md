# A runnable introduction, and examples worth learning from

Start here, then read [the linear guide](READING_GUIDE.md). From the repository root:

```sh
lake exe floatspec_demo
```

The [demo source](../../scripts/fixtures/GuidedDemo.lean) is short enough to read
in execution order. It uses the port's actual integer algorithms, not decimal
approximations as an oracle. Every section has both a `decide +kernel` assertion
and a compiled runtime check that throws on disagreement.
This command builds and runs a native executable through Lake. For the direct
Lean interpreter path, `lake env lean --run scripts/fixtures/GuidedDemo.lean`
still runs the same source and checks. The old `floatspec` executable remains
a no-op launch smoke test; it is not this demo.

## 1. Compute something unsurprising

Binary32 addition gives `1.5 + 2.25 = 3.75`, with result word `0x40700000`.
Start with `b32_plus` in [Bits](../src/IEEE754/Bits.lean): it delegates to the
generic IEEE operation in [Binary](../src/IEEE754/Binary.lean). Its finite path
aligns integer mantissas, computes, and rounds. The theorem beside an operation
states its interpretation; executing a particular input is a different check.

## 2. Watch the policy change the answer

With three significant bits, `1.125` is halfway between `1` and `1.25`.
The demo prints all five modes for both signs. A row `[s,m,e]` means
`(-1)^s * m * 2^e`, so `[0,4,-2]` is exactly one.
This leads into `binary_round`, integer truncation, and the location of a
discarded part relative to a midpoint. Direction and tie-breaking are separate
choices, particularly for negative inputs.

## 3. See why a theorem needs hypotheses

Round `73/64` directly to three bits: the answer is `1.25`. First round it to
four bits, then three: the answer is `1`. The intermediate result lands on a
midpoint. This is a counterexample to *unconditional* equality of the two
procedures, not to Flocq's conditional double-rounding theorems.
Read the paired [Lean](../../scripts/fixtures/DoubleRoundingWitness.lean) and
[Rocq](../../scripts/fixtures/DoubleRoundingWitness.v) witnesses before the
larger `Prop/Double_rounding` development.

### A remainder example with a necessary premise

At two-bit precision, both `1` and `8` are exactly representable. If we use
upward rounding for the quotient, `ceil(1/8)=1`, so the remainder is `-7`.
But seven needs three significant binary bits (`111`): that remainder is not
representable in the same format. Truncation or nearest rounding gives quotient
zero here and leaves remainder `1`, which is representable.

Read and run [RemainderContracts.lean](../../scripts/fixtures/RemainderContracts.lean)
with `lake env lean scripts/fixtures/RemainderContracts.lean`, then compare the
[Rocq proof](../../scripts/fixtures/RemainderContracts.v). The theorem states a
negation of the overbroad claim directly; its trivial numerical side conditions
are discharged inside the proof rather than put in the conclusion as clutter.
[RemainderGrid.lean](../../scripts/fixtures/RemainderGrid.lean) then expands this
lesson into a complete small finite test. These are additional standalone
examples, not an eighth section silently added to the seven-part demo command.

There is a second, independent premise: spacing must not get coarser as numbers
get smaller. The alternating-precision format in
[ExponentValidityBoundary.lean](../../scripts/fixtures/ExponentValidityBoundary.lean)
is valid but represents quarter steps above one and only half steps just below
one. Truncating the quotient `1.75 / 1` leaves remainder `0.75`, which it cannot
represent. Both assistants prove this too. This explains why merely changing
the integer rounding mode cannot remove the exponent-monotonicity assumption.

## 4. Separate bits, comparison, and real value

Positive and negative zero have different words but compare equal. NaN is
unordered, represented by `none : Option Ordering`. The successor of the
negative smallest subnormal is negative zero. These are examples where
real-valued equality alone cannot describe the whole interface.

The demo also prints the public Boolean APIs as `[=, <, <=]`. For `+0`
versus `-0`, that is `[true,false,true]`; for `+0` versus NaN, all three are
false. Follow `BinarySingleNaN.Beqb`, `Bltb`, and `Bleb` to `Bcompare`:
an unordered result must stay unordered rather than being coerced into
equality. These APIs are now executable; the previous real-based definitions
had valid finite correctness proofs but could not run in compiled clients.

## 5. Reproduce an actual audit lesson

### Two equal values that the raw source API compares differently

`3 × 2^-1` and `6 × 2^-2` both equal 1.5. However, Rocq's raw
`SpecFloat.SFcompare` compares exponents before mantissas: the first encoding
compares **greater**, because `-1 > -2`. Its numerical-order guarantee relies
on canonical representation. A total raw port must retain the source behavior
even for noncanonical inputs; replacing it with real-value comparison changes
that API.

Run the paired [Lean fixture](../../scripts/fixtures/PrimitiveComparison.lean):

```sh
lake env lean scripts/fixtures/PrimitiveComparison.lean
```

It checks 24 literal cases through twelve actual entry points. In the first
case, raw comparison returns greater-than, but validating either encoding as
binary64 rejects it and produces NaN. Therefore the validated comparison is
unordered. If the bridge only observed the final conversion, it would miss
the raw mismatch. Separate validity bits make that distinction visible.
The fixture also closes two proofs: the real values are equal, and the raw
comparison is greater-than. They are consistent propositions about different
interfaces, not a contradiction.

This definition comes from
[Rocq Corelib, not Flocq itself](https://github.com/rocq-prover/rocq/blob/adfbf1855c348766beb4b790dcc8ebc02f908f63/theories/Corelib/Floats/SpecFloat.v#L163).
The matching [Rocq fixture](../../scripts/fixtures/PrimitiveComparison.v)
calls that raw API, the native primitive, and Flocq's proof-carrying API
separately. A closed structural Lean theorem connects the raw comparator to
the generic proof-carrying comparator for every format; finite cross-tests
remain a separate check against the other language.

### Validity is not just a range check

The raw pairs `(1,0)` and `(4,-2)` both denote one. Only the latter is canonical
for this three-bit format. The demo checks `valid_binary_SF` returns
`[false,true]`. A former compatibility implementation returned true for every
input; accepting a noncanonical carrier was a semantic bug, not missing proof
automation. The exact regression is useful when explaining why a green build
cannot certify a port.

## 6. Watch cross-testing discover a missing precondition

The source shift sends integer `-1` to `0`; Euclidean division sends
`-1 / 2` to `-1`. They agree on nonnegative mantissas, which is precisely
the hypothesis of Flocq's `shr_truncate` theorem. The former raw-rounding
implementation used that shortcut for every integer. The demo now executes
the distinction and one saved input that previously produced NaN rather
than the source's negative zero.

This is not a claim that a negative raw mantissa denotes a valid float.
It separates two contracts: a total exported function's behavior, and the
conditional theorem explaining its real value. The paired
[Lean](../../scripts/fixtures/RawIEEERounding.lean) and
[Rocq](../../scripts/fixtures/RawIEEERounding.v) fixtures retain literal
expectations; the [197-case replay](../../scripts/fixtures/RawIEEERoundingReplay.json)
preserves every disagreement from the original seeded run.

The related [raw-overflow Lean](../../scripts/fixtures/RawOverflow.lean) and
[Rocq](../../scripts/fixtures/RawOverflow.v) examples show why we observe more
than the final output. At precision zero, the source converts its mantissa
expression to a positive integer and obtains 1. The former raw Lean helper
returned 0, but a later positive-carrier conversion silently restored 1.
Testing only that final conversion missed the earlier discrepancy. The
expanded bridge compares every exported stage and retains 87 replay inputs
from this separate finding.


## Nearest is stronger than larger

Before comparing interfaces, distinguish **a larger value** from **the next
value**. In base three with two digits, one normalizes to `3 * 3^-1`.
Its successor is `4/3`; `5/3` is also canonical and larger, but skips `4/3`.
Likewise its predecessor is `8/9`, not the also-canonical `7/9`.
Run `lake env lean --run scripts/fixtures/PffWalkthrough.lean` to see the
actual source-facing successor. The Pff bridge independently searches exact
per-exponent rational grids and rejects deliberately skipped neighbors even
when Lean and Rocq observations are both mutated to agree on the wrong answer.
This makes a useful small lesson in testing specifications: checking an
inequality is weaker than checking nearest adjacency.

## Agreement is stronger with an independent expectation

Three implementations can agree because their adapters share a mistake.
The [exact IEEE oracle](../../scripts/ieee_exact_oracle.py) therefore answers
a different question: which representable grid point is closest to the exact
result, under the requested rounding policy? It uses rational arithmetic and
integer comparisons, not a copy of Flocq's rounding program. For square root,
it compares **squared midpoints**, so it never approximates an irrational root.

For example, binary32 upward rounding of `1 + 2^-24` must produce word
`0x3f800001`. Nearest-even produces `0x3f800000`. A control deliberately changes
every observed language path to the latter word; pairwise agreement survives,
but the independent expectation rejects it. Another control changes all input
echoes together, checking that the test actually ran the requested input.

Run the oracle's exhaustive small-format and mutation controls with:

```sh
uv run scripts/test_ieee_exact_oracle.py -v
```

Setting `FLOCQ_AUDIT_DIR` to the built pinned checkout also runs the two live
Lean/Rocq tests and their generated Lean kernel proofs. Without it, those two
tests are explicitly skipped. The standalone checker can strengthen a retained
receipt without pretending it is a new execution:

```sh
uv run scripts/check_ieee_exact_oracle.py --profile modes /path/to/report.json
uv run scripts/check_ieee_exact_oracle.py --profile native /path/to/report.json
```

The oracle covers finite arithmetic, signed zeros, gradual underflow, overflow,
all five modes, and fused single-rounding semantics. A separate classifier
now covers infinities, NaNs, division by zero, and negative square roots too.
It follows pinned Flocq's payload policy: the first NaN operand is preserved
as-is; an invalid result without an input NaN gets the positive quiet default.
This is a source-library policy, not a claim about every hardware NaN policy.
The native adapter intentionally canonicalizes NaNs; source bit results do not.

For example, `infinity * 0 + 1` is NaN even though replacing the product by
zero would give one. A mutation changes every actual language expression to
return the addend; they all agree, but the independent expectation rejects
them. Another mutation reverses operand order in NaN addition, exposing the
wrong first-payload selection despite mathematical addition's commutativity.
FMA of `maximumFinite * 2 + negativeInfinity` is negative infinity: the exact
finite product is not prematurely rounded to infinity before the addition.
No hardware exception flags or universal conformance proof are claimed.

## A valid format can have decreasing ULP

Some source theorems do not need `Valid_exp`; others genuinely need the separate
`Monotone_exp` hypothesis. These are different properties, not stronger and
weaker names for the same thing. Read the small paired
[Lean](../../scripts/fixtures/ExponentValidityBoundary.lean) and
[Rocq](../../scripts/fixtures/ExponentValidityBoundary.v) examples in order.

The exponent function is `f(e) = e - 1` when `e` is even, and `e - 3` otherwise.
Both assistants prove that it is a valid format, that every power of two is
representable, and that the exponent function is not monotone. At two adjacent
binades it gives:

| Input | Binary magnitude | Selected exponent | ULP |
|---|---:|---:|---:|
| `1/2` | `0` | `f(0) = -1` | `1/2` |
| `1` | `1` | `f(1) = -2` | `1/4` |

Thus increasing the input can decrease its ULP, even in a valid format and
even when both inputs are representable. The format simply offers more bits
in the second binade. Removing `Monotone_exp` from the source ULP-monotonicity
theorem would make it false; removing an unrelated leaked section assumption
is a different operation.

```sh
lake env lean scripts/fixtures/ExponentValidityBoundary.lean
```

This checks six Lean declarations and prints their axiom dependencies, none
containing `sorryAx`. The paired Rocq file proves the same statements against
the pinned library and prints its classical-real assumptions. These are
checked propositions about noncomputable real-valued definitions, not native
execution of real logarithms or a proof of whole-library equivalence.

## One operation, three interfaces

Run `lake env lean scripts/fixtures/PrimitiveExecution.lean` and read the paired
[Lean](../../scripts/fixtures/PrimitiveExecution.lean) and
[Rocq](../../scripts/fixtures/PrimitiveExecution.v) fixtures. They deliberately
observe each entry point instead of treating similarly named functions as
interchangeable.

Start with the raw encoding `(mantissa = 3, exponent = -1)`, which denotes 1.5
but is not canonical binary64. Squaring it exposes three different jobs:

| Step | Actual API | Observed encoding |
|---|---|---|
| Compute on the supplied raw encodings | `SFmul raw raw` | `(9,-2)`, noncanonical 2.25 |
| Convert the input numerically | `SF2Prim raw` | `(6755399441055744,-52)`, canonical 1.5 |
| Multiply those primitive values | `x * x` | `(5066549580791808,-51)`, canonical 2.25 |

All three results are intentional. The raw helper's valid-output theorem
requires valid inputs; the supplied raw 1.5 does not satisfy that premise.
Its total source behavior is still observable and must still match Rocq.
Conversely, testing only the primitive result would conceal a mistake in the
raw helper. The fixture proves these literal results in both assistants and
executes the Lean ones. No real-number approximation is used as an oracle.

The broader `prim_arithmetic` bridge follows this separation: raw algorithms
first, explicit input validity, numeric primitive operations, arithmetic
notation, and proof-carrying operations under each rounding mode. The
`prim_helpers` family checks scaling, neighbors, ulp, and decomposition,
including the returned exponents. The `prim_round` family separately checks
raw rounding and normalization—including signed mantissas outside the
real-value theorem's hypotheses.

Why did these functions need work if the formulas were already present?
Lean's `noncomputable` marker prevented compiled clients from using them,
even though the algorithms now operate on integers and finite constructors.
Removing the unnecessary markers exposes the existing code to execution;
it does not by itself prove that code agrees with the source. The 37-entry
fixture checks every newly executable definition/instance, and the seeded
bridge supplies broader, explicitly finite tests.

## A second small demo: which radix does an API actually use?

```sh
lake env lean --run scripts/fixtures/PffWalkthrough.lean
```

Read [the walkthrough](../../scripts/fixtures/PffWalkthrough.lean) linearly.
It starts with one, stored as `(1,0)`. In a two-digit base-three format,
normalization produces `(3,-1)`, the successor is `(4,-1)` = four thirds,
and the predecessor of two is `(5,-1)` = five thirds. The normalized
mantissa of one is three, so its parity is odd.

The second half deliberately calls the older compatibility wrapper with a
Core type indexed by base two and an extra argument equal to three. That
extra argument is ignored; the results are `(3,-1)` and `(8,-1)` instead.
The bound was chosen for base three, so this does not refute a theorem about
valid base-two formats. It shows why source porting must inspect parameter
use and data types, not just similar names or denoted real values.

The correct explicit-radix interface is in
[Pff/SourceFacade](../src/Pff/SourceFacade.lean). The paired
[Lean](../Test/PffExecution.lean) and
[Rocq](../../scripts/fixtures/PffExecution.v) fixtures retain literal kernel
regressions. A separate bridge observes all 56 source/compatibility fields
on identical inputs; its report distinguishes runtime agreement from
independently checked value/canonical-neighbor invariants.

## A small follow-on: why fused multiply-add is a separate operation

Run `lake env lean scripts/fixtures/SingleNaNArithmetic.lean` and read the paired
[Lean](../../scripts/fixtures/SingleNaNArithmetic.lean) and
[Rocq](../../scripts/fixtures/SingleNaNArithmetic.v) files. Their deliberately
tiny format has one significant bit and a largest finite positive value of 2.
Under nearest-even, multiplying 2 by 2 alone overflows to infinity. But the
single operation `fma(2, 2, -2)` returns exactly 2: it computes the exact
product-plus-addend and rounds only once, after cancellation has made the
result representable again. It is not multiplication followed by addition.

The same fixture shows the division `1 / 2` at the underflow midpoint. Its
nearest-even result is positive zero; nearest-away returns 1. Both answers
follow the selected policy. These examples call the proof-carrying SingleNaN
API itself, including its separate source-mode facade, rather than a native
hardware float or a full-payload compatibility wrapper.

## A second follow-on: can the rounding error itself be a float?

The [multiplication-error Lean](../../scripts/fixtures/MultiplicationErrorGrid.lean)
and [Rocq](../../scripts/fixtures/MultiplicationErrorGrid.v) fixtures enumerate
all 55 finite real values of the three-bit format with minimum subnormal
`1/16` and maximum finite value `14`. They test a source theorem's sufficient
condition: a nonzero exact product is at least `2` in magnitude, and the
fixture additionally keeps it at most `14` to exclude IEEE overflow.
Across all five modes, 5,385 cases have a representable rounding error.
Membership is checked against the independently enumerated values, not by
feeding the error back into the same rounder.

The condition matters. `(1/16) × (1/16) = 1/256` rounds to zero under
nearest-even, so the rounding error is `-1/256`. That is smaller in magnitude
than this format's smallest nonzero value and is not representable. This does
not contradict the conditional theorem; it explains one of its hypotheses.

## Another useful boundary: decomposition is conditional

The [helper fixture](../../scripts/fixtures/SingleNaNHelpers.lean) has a paired
[Rocq version](../../scripts/fixtures/SingleNaNHelpers.v). In the three-bit
format, decomposing `1` gives `(1/2, 1)`: the value is `1/2 × 2¹`. Decomposing
the smallest positive subnormal `1/16` gives `(1/2, -3)`.

Now reduce the format to one bit with maximum exponent two. Its smallest
positive value is `1`; it cannot represent `1/2`. The source deliberately
returns `(1, 0)` instead. The exact product identity still holds, while the
claim that the fraction lies in `[1/2, 1)` requires `2 < emax`. This is a
small executable example of why preserving a theorem's hypotheses matters.
The same fixture checks signed zero, directed underflow, both one constants,
alternate neighbors, and signed shifts using literal expected results.

Two more checked non-examples guard against dropping source hypotheses.
In the three-bit format, `Bulp'(+infinity)` is `1/16`, while
`Bulp(+infinity)` is infinity; their equality theorem requires a finite
input. Also, `Bpred_pos'(-1)` returns `-1`, while ordinary `Bpred(-1)` is
`-1.25`. The positive-only algorithm subtracts a positive-side spacing and
then rounds, so using it on a negative boundary is not ordinary predecessor.
Its source theorem explicitly requires a positive real value. The fixture
proves both inequalities independently in Lean and Rocq.

There is another easy-to-miss type distinction: `Bfrexp` itself requires only
positive precision, not `prec < emax`. With eight-bit precision and
`emax = 2`, it decomposes `1/128` as `(1/128, 0)`. With `emax = 3`, it
decomposes `-1/256` as `(-1/2, -7)`. The source's exact-value identity works
in both cases; normalized fractions are only promised in the second domain.
The helper fixture now checks both examples without a precision-separation
instance. For the larger independent check, run
`lake env lean scripts/fixtures/FrexpLaws.lean`: it tests 6,772 encodings
against integer membership and exact dyadic arithmetic, without calling a
real-valued correctness theorem as its oracle.

## From an algorithm's answer to an independently checked bracket

Run `lake env lean scripts/fixtures/CalcBrackets.lean` and read its paired
[Lean](../../scripts/fixtures/CalcBrackets.lean) and
[Rocq](../../scripts/fixtures/CalcBrackets.v) definitions. The oracle does not
divide or take another square root to manufacture an expected answer.
Instead, it checks integer inequalities after clearing positive denominators.
It verifies both the enclosing interval and the location relative to its
midpoint. The 8,640 division and 2,496 square-root cases cover bases 2, 3,
and 10 with positive mantissas and mixed-sign exponents.

For example, divide seven by three in base two. At output exponent minus one,
the returned mantissa is four: the interval is `[2, 2.5)`, with midpoint 2.25,
so seven-thirds is classified above the midpoint. At output exponent one,
the mantissa is one: the interval is `[2, 4)`, with midpoint three, so the same
quotient is below the midpoint. Both literal results are checked in Lean and
Rocq. This is the purpose of the location field: it remembers enough discarded
information to make a later rounding decision.

Square root illustrates why the core algorithm requires
`2 * outputExponent ≤ inputExponent`. On mantissa nine, input exponent zero,
and requested output exponent one, that premise fails. The raw integer scaling
uses a negative power, which is zero in this integer operation; the algorithm
returns zero rather than a bracket for square root nine. Both fixtures prove
that this is a counterexample to dropping the premise. The high-level routine
always chooses a sufficiently fine exponent, and its bracket theorem does
not additionally require that the exponent function describes a valid format.

## Converting a raw encoding is not the same as validating it

Run `lake env lean scripts/fixtures/PrimitiveConversion.lean` and follow the
paired [Rocq example](../../scripts/fixtures/PrimitiveConversion.v).
Start with the raw encoding `(positive, 3, -1)`: it denotes `3 × 2^-1 = 1.5`,
but its mantissa/exponent pair is not the canonical binary64 encoding.
The validity adapter rejects it. The source's `SF2Prim` conversion instead
returns the canonical representation of `1.5`. The old Lean definition
confused these two interfaces and returned NaN.

The conversion has two less obvious details. Its mantissa passes through an
unsigned 63-bit word, so `2^63` wraps to zero and `2^63+1` wraps to one.
It then rounds the integer to binary64 **before** scaling by the input
exponent. Scaling can round again when the result is subnormal.

For a concrete double-rounding example, take mantissa `2^53+5` and exponent
`-1077`. The first rounding maps the mantissa to `2^53+4`. In units of the
smallest subnormal, scaling now asks for `(2^53+4)/8 = 2^50+1/2`; nearest-even
chooses `2^50`. A single rounding of the original value instead asks for
`(2^53+5)/8 = 2^50+5/8`, which chooses `2^50+1`. Both provers check this
one-unit difference explicitly. Keeping both stages is necessary to match
the source API, even though one-shot rounding might look more natural.

The fixture checks 31 literal conversions, including both signs and special
values. The differential corpus uses positive raw mantissas, as Rocq requires;
it does not silently broaden the claimed source domain to Lean's extra
Nat-zero constructor. This is another reason to read a definition's actual
interface before trusting a nearby roundtrip theorem: that theorem may only
cover already-valid encodings.

## When a precision assumption matters—and when it does not

The format relationships are easier to read as implications than as programs.
FLT describes bounded-precision numbers with a minimum exponent; FLX drops
the minimum-exponent restriction, and FIX uses one fixed spacing. In particular,
every FLT number is also an FLX number and a FIX number. Those forward
implications in Flocq do **not** require the precision parameter to be positive.
Eleven Lean statements had accidentally inherited that extra assumption from
their surrounding sections; their repaired signatures now match this boundary.

Do not infer that positive precision can be removed everywhere. Take base two,
minimum exponent zero, precision zero, and the number one. FIX at exponent
zero includes one: it is an integer multiple of `2^0`. But FLT's canonical
exponent is `max(mag(1) - 0, 0) = 1`. Dividing one by `2^1` gives one-half;
integer truncation gives zero, and reconstructing gives zero, not one.
Thus one is **not** in this FLT format. It even satisfies the reverse
inclusion's size bound, `|1| ≤ 2^(0 + 0)`. Positive precision really is needed
for that reverse theorem.

Run `lake env lean FloatSpec/Test/SourcePremiseContracts.lean`, and read the
final `FLTUnrestrictedSourceContracts` section with its
[paired Rocq clients](../../scripts/fixtures/SourcePremiseContracts.v).
It contains eleven clients that do not supply positive precision and a closed
proof of the counterexample above in each language. These are proofs about
mathematical formats, not an attempt to configure hardware with zero bits.

The broader lesson: a green build can hide an overly restrictive theorem.
The theorem may be true, yet unusable in cases supported by the source.
Conversely, removing all restrictions can turn a useful statement false.
The source comparison, unrestricted typed clients, and counterexamples check
different sides of that boundary.

## The same number through three normalization entry points

Run `lake env lean scripts/fixtures/Normalization.lean`, then read its paired
[Lean](../../scripts/fixtures/Normalization.lean) and
[Rocq](../../scripts/fixtures/Normalization.v) files. A signed mantissa nine
with exponent minus three denotes `1.125`; nearest-even returns `1`, while
nearest-away returns `1.25`. Eleven at the same exponent is halfway between
`1.25` and `1.5`, so nearest-even now chooses the larger endpoint.
The fixture spells out expected results for both signs, both zero signs,
underflow, and overflow, in all five modes.

Three Lean entry points are called separately: the proof-carrying full-payload
normalizer, its SingleNaN facade, and the older raw compatibility normalizer.
Their results have different types, but their observed numbers agree in these
150 checks. Removing an unnecessary `noncomputable` marker made two of these
clients runnable without changing the algorithm or claiming a new proof.

The same fixture explains a subtler boundary: a proof-carrying adapter needs
evidence that its **result** is valid. A malformed format parameter does not
automatically make every result invalid. Precision zero can still produce a
valid zero; a different malformed format produces a rejected finite result.
A valid NaN and a rejected result are separately recorded, even though the
test serializes the rejection with a NaN-shaped sentinel. The validity bit
keeps those meanings distinct.

## Exemplars inspected

These are reading recommendations, not dependencies adopted by FloatSpec.

| Exemplar | Best use | What was actually checked |
|---|---|---|
| [Flocq in a Nutshell](https://flocq.gitlabpages.inria.fr/theos.html) | The conceptual route from formats and rounding to exactness, error bounds, and algorithms | Official guide read; it is a conceptual map, not this port's completion report |
| [Pinned `Compute.v`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/examples/Compute.v) | Follow addition from mantissa computation through truncation and rounding to its real interpretation | Compiled against the pinned source with Rocq 9.2; deprecation warnings only |
| [Pinned `Average.v`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/examples/Average.v) | A second-stage algorithm case study: several averaging algorithms and their guarantees | Compiled against the pinned source with Rocq 9.2; a substantial file, not a first five-minute demo |
| [FloatLib's first chapter](https://github.com/lean-dojo/FloatLib/blob/main/site/content/chapters/01-using-the-library.md) | Presentation pattern: one runnable operation, its exact stored result, and the corresponding proof/interface route | Chapter and README inspected; repository not built or independently audited here |
| [Lean's float reference](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/) | Understand the logical model versus native execution and the need for refinement links | Official reference inspected; native execution is not itself a proof of refinement |

The current unpinned FloatLib and Lean documentation links may evolve. The two
Flocq example links deliberately use this audit's exact source commit.
Flocq's `Triangle.v` is another attractive later numerical-analysis demo, but
it uses the Interval tactic; it was inspected, not compiled in this session.

To reproduce the two reference builds in a clean, already-built pinned Flocq
checkout (not the user's modified `Deps/flocq`), run:

```sh
mkdir -p /tmp/floatspec-exemplars
coqc -R src Flocq -o /tmp/floatspec-exemplars/Compute.vo examples/Compute.v
coqc -R src Flocq -o /tmp/floatspec-exemplars/Average.vo examples/Average.v
```

Use the same Rocq version that built that checkout. This Mac used
`/opt/homebrew/bin/coqc` (9.2), not the different project-local compiler.

## A proof-checker example: signed nearest-even

Run `lake env lean FloatSpec/Test/PffRoundingSource.lean`, then read its
`positive_half` and `negative_half` statements alongside
`scripts/fixtures/PffRoundingSource.v`. At radix three, precision two, bound
`(9,0)`, the input `3/2` has lower/upper/nearest records `(1,0)`, `(2,0)`,
`(2,0)`. The negative input has `(-2,0)`, `(-1,0)`, `(-2,0)`. Nearest-even
uses mantissa parity, whereas downward rounding follows numerical order.
Continue through strict-distance, exact, zero and invalid-premise cases.

This is deliberately a different kind of example from the native demo:
both assistants check closed propositions about real-valued definitions.
There is no claim that a runtime computes arbitrary real logarithms.
`scripts/test_pff_rounding_contracts.py` also demonstrates the testing idea:
replace nearest-even with downward rounding, observe rejection, and prove
the mutant's actual different answer.

## A boundary example: source integers are not machine words

Run `lake env lean FloatSpec/Test/NativeModelAdapters.lean`. First read
`signed_nan_distinction`: the raw source decoder preserves a signed NaN
payload, while the logical-model route canonicalizes it. Then read
`wider_integer_distinction`: source decoding of `2^32 + 1` gives the negative
minimum subnormal, but wrapping into UInt32 first gives the positive minimum
subnormal. Finally, `negative_integer_distinction` separates positive and
negative zero at input `-2^63`.

All three are paired with pinned Rocq examples. Their purpose is to make
the domain visible: exact word-sized inputs and arbitrary integer inputs
are different interfaces. The test initially assumed wrapping everywhere;
running both assistants exposed and corrected that oracle mistake.

## A proved statement can say too little

Consider rounding `1/2` to integers. The two closest values are `0` and `1`.
A tie policy returning false chooses `0`; a policy returning true chooses `1`.
Away from the midpoint, both policies must choose the closer value.

Eight ULP exports previously accepted a policy argument but used a separate,
fixed-policy chooser in their conclusions. In particular, the purported
two-policy agreement theorem compared the same fixed value with itself.
That proposition was easy to prove, but did not establish agreement between
the two supplied policies. The corrected theorem mentions `Znearest choice₁`
and `Znearest choice₂` separately and proves their agreement away from ties.

Read `scripts/fixtures/UlpNearestChoiceContracts.lean` linearly, alongside the
matching `.v` file. The first eight clients demand the source-shaped types.
`tie_choices_differ` proves the midpoint distinction about mathematical
rounding. Finally, `executable_tie_decisions` computes the integer rounding
decision: both assistants print `[0, 1]`. Run the Lean side with:

```sh
lake env lean scripts/fixtures/UlpNearestChoiceContracts.lean
```

All ten Lean proofs are free of `sorryAx`. The four live controls in
`scripts/test_ulp_nearest_contracts.py` deliberately erase a policy from the
expected type or choose the wrong policy at the tie, and require both
assistants to reject the mutation. A checked proof and a faithfully stated
source theorem are distinct requirements; this example tests both.

## A source interface can be narrower than its arithmetic

The old indexed Pff carrier requires a radix greater than one. But Flocq's
unindexed multiplication theorem only asks for a positive radix, so radix one
is a valid client. The restored `Pff.Source.Fmult` operates on two plain integer
records without any radix argument; its observer theorem takes the radix and
the exact source premise separately.

The paired `PffBasicSourceContracts.lean` / `.v` fixtures check that exported
shape. They also show why some premise is still needed: at radix zero,
multiply `(1, 1)` by `(1, -1)`. The result record is `(1, 0)`, whose value is
one, but the first operand's value is zero, so the product of values is zero.
Both assistants prove the inequality. The counterexample is stated directly,
without wrapping it in trivial conjunctions.

Likewise, `Fzero (-7)` is `(0, -7)`, not `(0, 0)`. Both represent zero, but
they are different source records. The 61-column Pff bridge observes those
fields independently, and a deliberate shared mutation erasing the exponent
is rejected even when every execution path agrees on it.

Run the Lean fixture after building the source facade:

```sh
lake build FloatSpec.src.Pff.SourceFacade
lake env lean scripts/fixtures/PffBasicSourceContracts.lean
```

## After the demo

Read [the linear guide](READING_GUIDE.md), then
[the three verification loops](THREE_VERIFICATION_LOOPS.md), then
[the review ledger](ASTRA_AUDIT_2026-09-19.md). The demo demonstrates seven
behaviors; the seeded bridge checks larger finite corpora; closed Lean proofs
establish their stated propositions. None is interchangeable with a universal
proof that the entire port matches pinned Flocq. Four explicitly recorded
native/decoder proof obligations remain, and the source-signature audit is
not complete.
