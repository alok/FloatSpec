# Understanding the executable dyadic comparison backend

This module continues Claude's exponent-alignment implementation and proofs.
The integration retains that work, but corrects its original claim: it is an
**arbitrary dyadic-value API**, not Flocq's raw-record comparison API.

Read [ComputableCompare.lean](../src/IEEE754/ComputableCompare.lean) beside this
guide. The source-facing operations remain in
[PrimFloat.lean](../src/IEEE754/PrimFloat.lean), imported by the normal aggregate.
The dyadic helper now requires an explicit `ComputableCompare` import. Its
reason to exist is exact comparison of arbitrary dyadic encodings, with a
closed bridge to the raw API when canonical-format invariants hold.

## 1. Start with the counterexample

Two payloads can encode the same real number differently:

```text
a = finite(false, 3, -1)  means 3 × 2⁻¹ = 1.5
b = finite(false, 6, -2)  means 6 × 2⁻² = 1.5
```

The APIs answer different questions:

| API | Result on a, b | Meaning |
|---|---|---|
| ComputableCompare.SFeqbC | true | Their represented values are equal. |
| ComputableCompare.SFcompareC | some .eq | Neither value is smaller. |
| FaithfulPrimFloat.SFeqb | false | Their raw finite representations differ. |
| FaithfulPrimFloat.SFcompare | some .gt | The source raw comparator orders these payloads by exponent first. |

The last row is observed in actual pinned Rocq and proved by Lean kernel
reduction in [ComputableCompareExecution.lean](../Test/ComputableCompareExecution.lean).
For the pinned-source probe and its scope, see
[the comparison review](CLAUDE_COMPARISON_REVIEW_2026-09-20.md).

Canonical float invariants are what allow representation-level operations to
serve as numerical operations. They cannot silently be assumed for the raw
`StandardFloat` datatype, whose finite constructor accepts arbitrary natural
mantissas and integer exponents.

The old unrestricted `*C_eq` statements against `FaithfulPrimFloat` are
therefore not retained. The corrected `*C_eq_value` statements explicitly name
the local value specification. No new proof holes are needed for this change.

## 2. Why exponent alignment computes

A finite payload denotes a dyadic rational:

```text
(-1)^sign × mantissa × 2^exponent.
```

First absorb the sign into an integer mantissa. To compare `n₁ × β^e₁` with
`n₂ × β^e₂`, align to the smaller exponent. If `e₁ ≤ e₂`, compare:

```text
n₁            with            n₂ × β^(e₂ - e₁).
```

The exponent difference is nonnegative. Thus only integer multiplication,
natural powers and integer comparison are needed. Alignment downward avoids
division and any divisibility condition.

The retained `dyadicLt` and `dyadicEq` implement exactly this split.
They are executable. For a valid radix, `dyadicLt_iff` and `dyadicEq_iff`
prove their agreement with the real values described by `F2R`.

The proof has two steps:

1. `F2R_change_exp` changes a representation to a smaller exponent without
   changing its value.
2. `lt_F2R_iff` or `eq_F2R` reduces comparison at a common exponent to
   comparison of the integer mantissas.

These are mathematical correctness theorems about the value API. They do not
establish unconditional equality to the raw source comparator.

## 3. Handle exceptional values before using the real observer

`SF2R` maps infinity and NaN to zero because they have no ordinary real value.
Therefore a comparison must not feed every constructor straight through `SF2R`.

Both the executable value backend and its local `ValueSpec` explicitly handle:

- NaN: unordered, unequal even to itself.
- Negative and positive infinity: below and above finite values.
- Two infinities: compare their signs.
- Signed zero and finite payloads: compare their dyadic values.

The executable implementation uses `dyadicLt` or `dyadicEq` in the final
case. The local mathematical specification uses comparison of `SF2R` values.
The `SFltbC_eq_value` and `SFeqbC_eq_value` proofs split on the constructors,
then apply the dyadic correctness theorems.

Non-strict order is less-than or equality. Three-way comparison tests the two
strict orders and otherwise returns equality, while preserving NaN's unordered
outcome.

## 4. The canonical bridge, and why its input type matters

`SFcompareC_eq_raw_of_canonical` proves equality with `FaithfulPrimFloat.SFcompare`
for any two `BinarySingleNaNFloat prec emax` inputs of the same format. The
finite constructor carries positivity and canonical-format bounds; arbitrary
`StandardFloat` records do not. Signed zero, infinities and NaN are included.
The three Boolean operations have corresponding closed bridge theorems.

The proof first uses the existing value theorem, then the source-shaped
`BinarySingleNaN.Bcompare_correct` for finite inputs. Constructor cases handle
the exceptional values. There are no new proof holes. This is a universal
theorem between two Lean implementations, not a universal cross-language theorem.

The `eqbC`, `ltbC`, `lebC` and `compareC` wrappers first project a
`PrimitiveFloat` to a `StandardFloat`. The corresponding `B*C` wrappers
project a `PrimBinaryFloat`.

These two input types **do** carry canonical validity. In particular,
`PrimitiveFloat.valid` supplies the proof; `B2SF_Prim2B` connects its projection
to the generic canonical carrier. All eight wrappers now have `*C_eq_raw`
theorems in addition to `*C_eq_value`. The earlier explanation that treated
these typed projections as unconstrained was overly conservative and is corrected.

Public definitions in this module carry `flocq_local` explanations and the
source-classification linter is enabled. A local helper classification is an
honest boundary, not a missing source theorem disguised as a correspondence.

## 5. What noncomputable does, and what it does not do

Lean separates logical definitions from executable code generation.
`noncomputable` suppresses compilation of a definition; it does not itself
introduce an axiom or a proof hole. A marked integer definition can still
reduce in the kernel.

There are three different cases in FloatSpec:

| Case | Example | Interpretation |
|---|---|---|
| Arbitrary-real mathematics | logarithmic `mag`, real floor, real-valued rounding | Specification, not a native floating-point algorithm. |
| Unnecessary marker on integer code | `Zquotient m n := m.tdiv n` | Genuine execution-capability gap; the body already computes. |
| Classical decision inside an integer algorithm | some legacy divisibility code | An executable decision procedure must replace the classical one before native execution is available. |

A read-only September 20 probe established:

```text
Rocq vm_compute: Zquotient (-7) 3  --> -2
Lean #eval:     Zquotient (-7) 3  --> rejected as noncomputable
Lean #reduce:   Zquotient (-7) 3  --> Int.negSucc 1 (that is, -2)
Lean #eval:     Int.tdiv (-7) 3   --> -2
Lean #print axioms Zquotient     --> no axioms
```

No `Zquotient` annotation or body was changed for that original explanation.
The follow-up implementation on September 21 removes its unnecessary marker:
`#eval Zquotient (-7) 3` now runs and returns `-2`, with the same body and type.
`Pdiv`, `oZ` and `oZ1` are executable for the same reason. This closes those
specific execution gaps; the real-valued specifications remain mathematical.
A later change replaced the `Pdiv`, `Zquotient` and `ZdividesP` bodies with
transcriptions of Coq's. Closed theorems equate them with the September 21
bodies, and `@[csimp]` keeps `Pdiv`'s compiled code on natural division.

`maxDiv` needed one more step. Its old definition used classical choice to
decide integer divisibility despite an existing constructive `ZdividesP`.
It now uses that checker. A closed Lean theorem proves equality with the old
definition for every radix, value and bound; paired execution probes also run
the actual pinned Rocq function. This is not replacing a real-number spec with
machine floats, nor pretending that finite tests prove source equivalence.

Run the self-checking examples with:

```sh
lake env lean scripts/fixtures/PffIntegerExecution.lean
```

Conversely, Rocq's `Definition` keyword does not promise executable extraction.
The pinned `Zfloor` and `mag` reference classical real-number infrastructure;
their live `Print Assumptions` reports contain classical axioms. A difference
in surface syntax is not by itself an execution discrepancy.

Using a computable representation of reals can make suitable approximations
executable. It does not automatically provide terminating exact comparison or
equality of arbitrary real values. The dyadic subset is special: its finite
integer representation permits the exact algorithm above.

## 6. Read the evidence in the right order

The module retains the mathematical proofs connecting integer alignment to
real values. Its execution test also checks concrete kernel equalities and
runs 20,000 deterministic pseudorandom payload pairs (seed 526913), testing
trichotomy, reflexivity, order consistency and invariance under radix rescaling.

Those finite checks are regression evidence, not universal source equivalence.
The kernel proofs establish the stated value contracts; the explicit
counterexample prevents confusing that contract with raw source comparison.

The September 21 continuation also runs 3,364 canonical pairs across four
ordinary/degenerate formats and four comparisons per pair. The shared-input
`prim_comparison` profile now observes 26 fields: the original raw/validity/typed
surfaces plus all twelve opt-in dyadic calls on canonical inputs. Seed 864101
passes 1,345 cases in compiled Lean, reduced Lean and pinned Rocq, then generates
1,345 checked kernel equalities. Twenty-four individual output mutations are
detected. Noncanonical raw inputs are observed before the rejecting conversion;
their value comparison is deliberately not substituted for the source answer.

Run from the repository root:

```bash
lake build FloatSpec.Test.ComputableCompareExecution
lake build FloatSpec.Test FloatSpecTests floatspec
uv run scripts/check_proof_debts.py
```

The source-conformance bridges are documented separately in
[THREE_VERIFICATION_LOOPS.md](THREE_VERIFICATION_LOOPS.md). Their source-facing
comparators remain unchanged by this integration.
