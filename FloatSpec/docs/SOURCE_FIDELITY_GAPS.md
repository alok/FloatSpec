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

Pdiv, Zquotient and ZdividesP now transcribe their Coq bodies rather than
reimplement them. Pdiv recurses on Coq's xH/xO/xI through a constructor view
of the predecessor-encoded Positive, with the same option cases and
Z0/Zpos/Zneg comparisons. Zquotient splits on signs and calls Pdiv. ZdividesP
cases on m and tests Zquotient n m * m = n. Pdiv_correct is proved by
induction on p, as in Coq. Closed theorems equate Pdiv with natural `/` and
`%` and Zquotient with `Int.tdiv`; they are not runtime overrides. Compiled
code, kernel reduction and `#reduce` all run the transcriptions, including the
bridge's 127-bit quotients. ZdividesP and maxDiv now report propext,
Classical.choice and Quot.sound rather than only propext, because ZdividesP's
proof fields go through Pdiv_correct and core `Int.tdiv` lemmas. Those axioms
sit in erased proofs; the decisions still execute and reduce in the kernel.
oZ and oZ1 keep their source bodies. maxDiv uses ZdividesP rather than a
classical decision, with a closed universal equality proof against its old
definition. Paired fixtures and 2172 three-way cases test signed quotients,
zero divisors, full optional records, smallest positives and bounded
divisibility at negative/zero/one radices too. Five shared-program mutations
are rejected independently. Other noncomputable declarations still need
individual review; mathematical real specifications should remain mathematical.

## Pff.lean statement shapes after the Hoare cutover (September 23, 2026)

The cutover replaced every Pff.lean Hoare triple with a direct proposition
equivalent to the old reading. A later review compared the Coq-named statements
with Rocq's `Check` output, premise by premise. The findings are now resolved as
follows.

- Premise order and currying follow Rocq for all 531 compared Coq-named
  theorems. That means section hypotheses before the objects they constrain,
  `forall P, RoundedModeP P ->` placed where Rocq puts it, and `forall e` at its
  Rocq position in `discri5`–`discri8`. Callers were permuted to match.
- The Discriminant family (`discri`, `discri1`–`discri16`, `cases`) now has
  exactly Rocq's premises. The extra `Fbounded`/`Fnormal`/`Fcanonic`/underflow
  hypotheses and the Lean-only bundle `discri3_source_context` are gone. The few
  facts the proofs still needed are derived from the rounding hypotheses. For
  example, `Fbounded t` comes from `EvenClosest (p - q) t`, and `0 ≤ p` comes
  from `P_positive`.
- `FmaErr`, `FmaErr_aux`, `ImplyClosest*`, `LSB_Pred`, `RoundedModeMult*`,
  `UlpFlessuGe*`, `digitLess`, `eqExpLess`, `firstNormalPosNormal` and
  `ExactMinusInterval` (now for any radix) no longer take hypotheses that Rocq
  lacks. `errorBoundedMult` holds for any `P` with `RoundedModeP`. The
  closest-only variant used by the local FMA proof is `errorBoundedMult_closest`.
- The primed aliases `Fbounded'`, `Fnormal'`, `Fsubnormal'` and `Fcanonic'`, and
  their duplicated premises, are deleted.
- A redundant `1 < beta` binder is dropped from every Pff.lean theorem whose
  `[ValidRadix beta]` already provides it. There are 32 exceptions: older
  arrow-style statements that were outside the reviewed set still repeat it
  after the colon. Most are local helpers; the rest are `Dekker2_FTS`,
  `ExactMinusIntervalAux`, `ExactMinusIntervalAux1`, `MDekkerAux3` and
  `MDekkerAux4`.
- `MaxUniqueP`/`MinUniqueP` conclude `UniqueP`, and `Fle_Zle` concludes `Fle`.
  `OddEvenDec` is a computational `PSum`, like `floatDec`, matching Rocq's
  sumbool.

Paired typed clients in `scripts/fixtures/PffStatementContracts.{lean,v}` check
`FnormalUnique`, `ImplyClosest`, `errorBoundedMult`, `discri3` and `eqExpLess`
against both checkers. `scripts/test_pff_statement_contracts.py` rejects planted
changes in both checkers: an extra premise, a swapped order, a Closest-only
`errorBoundedMult`, and an extra boundedness premise.

Remaining differences are deliberate. The only one that asks for more than
Rocq does is the indexed arithmetic laws below, which need a valid radix:

- *Radix encoding.* The indexed carrier `FlocqFloat beta` with
  `[ValidRadix beta]` stands for Coq's `float` with `1 < radix`. Theorems that
  keep a separate `radix : Int` link it with `beta = radix`; the radix-2
  sections use `beta = 2` and `radix = 2`. `Closest`, `EvenClosest`, `FNSucc`
  and `FNPred` take an unused `radix : ℝ`, so `ClosestMax`/`ClosestMin(Eq)`
  carry two radix binders. The `RND_*` lemmas take `p : ℤ` with `p.toNat` where
  Rocq uses `p : nat`. The indexed `Fabs`/`Fplus`/`Fminus`/`Fmult_correct` in
  Pff.lean need a valid radix (`1 < beta`), while Rocq needs only `0 < radix`.
  The source facade (`FloatSpec.Pff.Source`) holds the Rocq-shaped versions,
  including radix one.
- *Relaxed premises (stronger Lean statements).* Twenty-eight theorems take
  `precision ≠ 0` where Rocq has `1 < precision`, among them `ClosestUlp`, the
  `Fulp*` lemmas, `MinOrMax*`, `errorBoundedMultMin/Max` and `RoundGeNormal`.
  Some theorems drop Rocq premises altogether:
  - `4 <= precision` in `AddExpGeUnderf*`, `FexpGeUnderf`, `RoundGeNormal`,
    `pGeUnderf` and `qGeUnderf`;
  - the precision and bound premises in `Fcanonic*`, `FcanonicUnique`,
    `Fweight*`, `ClosestFabs`, `Rle*R0`, `RleBoundRound*` and
    `RoundAbsMonotone*`;
  - `Fbounded t`/`Fbounded u` in the `Axpy*` lemmas, and `Fbounded f` in
    `ClosestSuccPred`;
  - the unused `forall P, RoundedModeP P` in `ExactMinusInterval`.

  `t_exact`, `dexact` and `IneqEq` replace the product-rounding premises with
  `0 ≤ F2R p` or `F2R t = F2R p - F2R q`. `yLe2x`/`yLe2x_aux` quantify the
  error over reals instead of floats.
- *Conclusion forms.* `FulpPred`/`FulpSuc` state the expanded
  `FPred (Fnormalize …)`/`FSucc (Fnormalize …)` rather than `FNPred`/`FNSucc`,
  because of the phantom real radix above. A few equalities are oriented
  differently from Rocq (`MinMax`, `MinOrMax3*`, the `Axpy` perturbation
  bounds). These are equivalent readings.

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

## Priority 5 (done): discharge the explicit native/decoder boundary obligations

All four manifest obligations are discharged. Binary64 sign flipping
(`Binary64.ofBits_flipSign`) and the native next-up/next-down refinement to
`Bsucc`/`Bpred` are kernel-checked theorems over all binary64 inputs, and the
native frExp obligation is replaced as described below. Runtime agreement was
not their proof. [proof_debts.json](proof_debts.json) is now empty; any new
obligation must be listed there explicitly rather than letting a name imply
established universal refinement.

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
