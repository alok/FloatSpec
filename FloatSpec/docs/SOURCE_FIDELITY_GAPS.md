# What still separates this from a faithful port

Updated September 21, 2026, against Flocq
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`.

The target is the same domain, result type, branches, and theorem hypotheses
and conclusions. Closed Lean proofs, file coverage, source links and finite
agreement are useful evidence but do not substitute for that comparison.
Three remaining sorries do not mean only three fidelity issues remain.

## Priority 1: finish comparing source contracts

Much of the theorem-by-theorem review is still unreviewed, especially the
surrounding Prop and legacy Pff library. Recent repaired examples show why
this matters: 27 signatures required Valid_exp where the source did not,
and eight nearest-rounding ULP exports accepted but erased tie policies.
One old two-policy equality was merely fixed-value reflexivity.

For each source export, require a paired typed client, compare every premise
and result, then read the underlying definitions. A successful client is still
not a cross-assistant equivalence proof. The focused reviewed slices are in
[SOURCE_CONTRACT_REVIEW.md](SOURCE_CONTRACT_REVIEW.md); the broader review
ledger preserves what was and was not checked.

## Priority 2: complete and privilege the source-shaped interfaces

The indexed Core carrier and unindexed Pff carrier are different interfaces.
The source facade now handles explicit-radix normalization and signed rounding;
legacy normalized Pff helpers intentionally keep their indexed-radix behavior
and are labeled local. They should not be silently presented as source exports.
The facade is not yet the complete Pff surface. The concrete Fzero, is_Fzero
and Fmult gaps identified earlier are now filled, with four exact source-shaped
observer laws and paired clients. Multiplication correctness accepts radix one,
which the indexed valid-radix carrier cannot express. Other source exports must
still be compared individually; analogous indexed operations do not establish
complete unindexed API coverage.

Four further sign laws cover negation, involution, absolute-value
interpretation and nonzero preservation. The source-shaped `Fplus_correct`
and `Fminus_correct` laws are now present with closed Lean proofs and paired
Rocq clients. They need only `0 < radix`, not `1 < radix`, and explicitly
support radix one. Both assistants prove radix-zero counterexamples.
Eight live contract mutations reject missing premises and incorrect signs.
This closes these two interface gaps, not the rest of the unreviewed Pff API.

Pdiv, oZ, oZ1 and Zquotient now execute with unchanged integer/natural bodies
and types. maxDiv uses the existing constructive ZdividesP rather than a
classical decision, with a closed universal equality proof against its old
definition. Paired fixtures and 2172 three-way cases test signed quotients,
zero divisors, full optional records, smallest positives and bounded
divisibility at negative/zero/one radices too. Five shared-program mutations
are rejected independently. Other noncomputable declarations still need
individual review; mathematical real specifications should remain mathematical.

## Priority 3: make provenance coverage a gate everywhere

The latest compiled metadata validates 344 source anchors. Strict public-definition
classification is enabled in fourteen source files plus a section of Binary;
unclassified definitions elsewhere are not yet rejected. The current linter
checks public def/abbrev declarations, not every theorem. Expand classification
while distinguishing source exports, deliberate local adapters, and genuinely
unreviewed declarations. A source link must never be labeled semantic approval.

## Priority 4: strengthen testing without confusing it with proof

Independent exact IEEE expectations now include exceptional return values,
with separate source payload and native canonical-NaN policies. Fresh and
retained-output checks are kept separate. Tests still do not cover every
source theorem or all combinations of arbitrary format parameters; the oracle
does not model hardware exception flags or directed hardware rounding.
Keep invalid/precondition cases, complete output observations, reproducible
inputs and shared-bug mutation tests when expanding the executable surface.

## Priority 5: discharge the explicit native/decoder boundary obligations

The three manifest obligations concern binary64 sign flipping and
next-up/next-down refinement. Runtime agreement is not their proof.
See [proof_debts.json](proof_debts.json). Keep these explicit rather than
letting their names imply established universal refinement.

The former `native_frexp` debt stated Flocq agreement for Lean's
`Float.frExp`. Lean 4.34 declares that function as an
`@[extern "lean_float_frexp"] opaque` constant, so the kernel cannot see its
result and the statement was unprovable without an axiom. It is replaced by
`FaithfulPrimFloat.PrimitiveFloat.nativeFrExp_equiv`, a closed theorem
(axioms: `propext`, `Classical.choice`, `Quot.sound`) with the same
precondition and conclusion about `nativeFrExp`. That function computes the C
`frexp` contract from `Float.toBits`, with explicit subnormal normalization.
The remaining gap is explicit: the opaque runtime `Float.frExp` equals
`nativeFrExp` only on the evidence of execution. That evidence is
[the runtime agreement fixture](../../scripts/fixtures/NativeFrexpAgreement.lean):
200,556 inputs covering every encoding class, plus the native IEEE bridge
against Rocq. The runtime function is checked by execution, not trusted by the
kernel. No theorem mentions `Float.frExp`.

## Build/review usability

macOS Lean 4.34 builds and runs the checked snapshots. Hosted CI
previously failed before source compilation because it requested a pinned rc2
Mathlib cache under final Lean 4.34. The approved workflow repair now skips
that incompatible cache and builds the reviewed sources with stable 4.34.0;
hosted verification is pending. Local success is not a hosted/Linux pass.
Exact source hashes and reviewable fork commits remain the authority for
which snapshot each test exercised.
