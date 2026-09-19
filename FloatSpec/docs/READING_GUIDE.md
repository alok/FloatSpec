# FloatSpec, read from start to finish

FloatSpec is a Lean port of [Flocq](https://gitlab.inria.fr/flocq/flocq), a
mathematical library for floating-point formats and operations. The short
version is: **describe the right values, compute the right answers, prove the
right statements, and check that “right” still means what Flocq means.**
Those are separate jobs. A program can compile while its specification is wrong.

This guide follows those jobs in order. The detailed
[original audit](FLOCQ_CONFORMANCE_AUDIT_2026-09-18.md) and
[independent continuation audit](ASTRA_AUDIT_2026-09-19.md) retain the
declaration-by-declaration findings and historical milestones.

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

The example is explanatory, not an extra executed test receipt. The runnable
boundary corpora exercise real binary32/binary64 halfway cases and all five
rounding modes.

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

A Lean proof establishes **the Lean proposition actually written down**.
It does not tell us that this proposition is the one intended by Flocq.

For example, the old `valid_binary_SF2FF` statement compared validity after
a conversion with a wrapper defined to be that same expression. It was
provable but missed the intended relationship. The repaired theorem compares
full-float validity with an independently defined SingleNaN validity
predicate, under the source's non-NaN premise.

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
That bridge currently checks kernel/Rocq execution, not native directed
rounding. The direct decoder and integer-width packing families also avoid
using `Float.Model.ofBits` as a substitute for the port's own decoder.

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

All 36 Flocq source-module names have corresponding Lean files or umbrella
modules. The old extraction plan lists 2,548 source declarations, with
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
Eleven modules currently enforce strict public-definition classification.
The compiler-backed validator checks all 56 registered anchors, including
combined attributes and later attribute commands. These links are metadata,
not a proof that bodies or theorem signatures correspond.

Adjacent `Source:` URLs can be opened by editors that recognize URLs.
The attribute's path string itself does not yet have a special click action;
that remains low-priority editor integration.

The useful next step is always concrete: select one source declaration,
compare its type and branches, run a boundary case through both systems,
check its hypotheses, and then inspect its proof. That is the unit of
progress the audit is tracking.
