# A runnable introduction, and examples worth learning from

Start here, then read [the linear guide](READING_GUIDE.md). From the repository root:

```sh
lake build
lake env lean --run scripts/fixtures/GuidedDemo.lean
```

The [demo source](../../scripts/fixtures/GuidedDemo.lean) is short enough to read
in execution order. It uses the port's actual integer algorithms, not decimal
approximations as an oracle. Every section has both a `decide +kernel` assertion
and a compiled runtime check that throws on disagreement.

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

## After the demo

Read [the linear guide](READING_GUIDE.md), then
[the three verification loops](THREE_VERIFICATION_LOOPS.md), then
[the review ledger](ASTRA_AUDIT_2026-09-19.md). The demo demonstrates five
behaviors; the seeded bridge checks larger finite corpora; closed Lean proofs
establish their stated propositions. None is interchangeable with a universal
proof that the entire port matches pinned Flocq. Four explicitly recorded
native/decoder proof obligations remain, and the source-signature audit is
not complete.
