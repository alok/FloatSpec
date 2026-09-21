# Focused source-contract review

This ledger records manual statement/body comparison against Flocq commit
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`. It does not certify all proofs or
all declarations in the named modules. See the
[running audit](ASTRA_AUDIT_2026-09-19.md) for execution receipts and the
[reading guide](READING_GUIDE.md) for the mathematical story.

## Dependency-ordered review

### Port-completion slice: direct rounding-predicate API

The user reaffirmed that finishing the faithful port, rather than growing an
audit report, is the main goal. This slice supplies 25 ordinary propositions
from pinned `Core/Round_pred.v:89–539`: directed monotonicity/uniqueness,
negation, endpoint exclusion, representable-input fixed points, truncation
bounds, and the first nearest-rounding laws. Twenty direct exports were
missing; five existing source-named exports still returned Boolean/Hoare
contracts. Those five now return the actual propositions. Caller search found
no uses of their former interfaces; compatibility `*_spec` wrappers remain.
This is an API-fidelity repair, not a newly discovered arithmetic wrong answer:
the underlying mathematics already had proofs inside the legacy wrappers.

All 25 preserve arbitrary real formats and the source's precise premises.
No valid-radix, representability-of-zero, totality, or tie-policy premise is
silently added. In particular:

- `Rnd_ZR_abs` assumes a total truncation function, and derives zero membership
  from its value at zero. It does not ask the caller for an extra `F 0`.
- `Rnd_ZR_pt_monotone` really does require `F 0`. For the two-point format
  `{−1, 1}`, truncation sends `−1/2` to `1` and `1/2` to `−1`, reversing order.
- `Rnd_N_pt_monotone` assumes `x < y`, not `x ≤ y`. At the midpoint zero of
  that same format, both `−1` and `1` are nearest, so arbitrary nearest
  selections need not preserve equality of inputs.
- `Rnd_N_pt_unique` preserves the unequal-distance premise `x - d ≠ u - x`.
  The midpoint example also refutes unconditional nearest uniqueness.

`RoundPredSourceContracts.lean/.v` check the 25 exact interfaces and prove
these three negative results in both assistants. Eight live mutations remove
necessary premises or weaken strict input order; both compilers reject them.
The mutation control must compile first, and tool/import/warning failures are
errors, not detected semantic mutants. The tests run in the aggregate harness;
hosted CI runs the Lean half and explicitly skips the unavailable live Rocq half.

The follow-up completes the module's public interface: 33 more direct laws
and a repaired `Rnd_NG_pt_opp_inv`, all with closed proofs. It covers nearest
sign/absolute-value laws, generic policy uniqueness, ties away from/toward
zero, general rounding sign laws and format transfer. Existing function
liftings, dependent witness constructors, totality statements and predicate
bodies were also compared to the pinned source and checked with typed clients.

Important distinctions checked in `RoundPredTieContracts.lean/.v`:

- The auxiliary `Rnd_NG_pt_unique_prop` accepts `Type`-valued policies in
  Rocq; Lean's `Sort u` generalizes this without restriction. Actual rounding
  relations use `Prop`-valued policies. Both interfaces have explicit clients.
- An always-false generic tie predicate is permitted at an exactly
  representable point: uniqueness supplies the other disjunct. Requiring the
  tie predicate unconditionally would strengthen the source incorrectly.
- Both ties-away and ties-toward-zero uniqueness require `F 0`. In format
  `{−1, 1}`, the two midpoint candidates have equal absolute values, so either
  policy accepts both. Both assistants prove this counterexample.
- `satisfies_any` has the source's three proof fields and supports dependent
  elimination. Its four generated Rocq schemes are explicitly classified as
  adapted proof infrastructure using Lean's recursor, not four missing APIs.
- `satisfies_any_imp_NG` gives totality, not nonstrict monotonicity. The source's
  explicit zero-membership argument to `satisfies_any_imp_N0` is retained even
  though the format assumption can also supply it.

All 78 top-level sites, the constructor and four generated schemes now have
explicit manifest dispositions. The paired fixtures check their interfaces;
20 live mutations across the two fixtures are rejected. The first 36
contiguous source-order dispositions remain unchanged. This review covers
these mathematical contracts and defining bodies, not every proof term or
the unreviewed imports. In particular, Lean's classical witness selection is
not the same proof term as Rocq's completeness construction. No new proof
debt is introduced, and no numerical operation body changed.

The review now also has a [dependency-ordered queue](SOURCE_REVIEW_QUEUE.md),
generated from actual `coqdep` and matching-digest `.glob` metadata. Its manual
manifest is conservative: older entries in this prose ledger are not silently
reclassified merely because a matching Lean name exists.

### First ordered slice: version and Zaux prelude

The first eight source sites are reviewed: pinned `Flocq_version` (40202),
the imported aliases `cond_Zopp` and `iter_pos`, the two integer propositions
`Zopp_le_cancel` and `Zgt_not_eq`, and the Boolean proof-infrastructure trio
`eq_dep_elim`, `eqbool_dep`, `eqbool_irrelevance`.

The first two propositions retain their exact hypotheses and conclusions.
`eqbool_dep` retains its true/false branches; Lean's `Sort u` family generalizes
the source `Type` family without restricting it. The generated Coq equality
eliminator is classified as adapted proof infrastructure, not a missing numeric
API: Lean's existing proof irrelevance proves the same `eqbool_irrelevance` law.
The paired typed fixtures check the precise source specializations.

`iter_pos` now follows the actual Corelib binary-positive recursion imported by
Flocq, instead of converting to a natural count before recursing. The closed
`iter_pos_nat` theorem proves the same semantics as the former implementation
for every function, positive count and initial value; its only listed axiom is
`propext`. There is no new `sorry`, and no performance claim based merely on
the source-shaped recursion. Seven anchors include the two simple source
notation aliases. Their external Corelib bodies were inspected in Rocq 9.2.

`ZauxPreludeContracts.lean/.v` execute fixed boundary examples. The new shared
profile tests positive binary-constructor boundaries, signed values, zero and
negative affine multipliers, and rejects nonpositive counts before transport.
Its independent oracle uses a closed geometric-sum formula rather than copying
the recursive algorithm. Seed 864211 passes 1244 compiled/reduced Lean versus
Rocq cases, 1244 independent assertions and 1244 generated kernel equalities.
Two shared-program mutations still agree across the assistants but are rejected
by that independent oracle. The next queue entry is `Zeven_ex`, not a claim
that the rest of Zaux or earlier prose-ledger slices have been re-audited.

### Second ordered slice: parity, integer powers and radix

The next twenty source sites, from `Zeven_ex` through `Zpower_gt_id`, now have
explicit dispositions. Paired typed clients cover the full hypotheses and
conclusions. The direct Lean statements already matched this source slice;
no mathematical theorem was weakened or numerical operation changed.
Eighteen new pinned anchors make the correspondence navigable.

The representation adaptations are explicit. Source `Z.even` corresponds to
decidable Lean `Even`. Source `radix` stores an integer with proof that
`Z.leb 2 value = true`; Lean `Radix` stores the same integer domain with proof
`2 ≤ value`. The fixtures check both directions of this proof presentation,
and the manifest fingerprints the constructor and both field types as well
as the record. Lean uses `.val` explicitly where Rocq uses a coercion.

Crucially, `Zpower` is **integer** power, not real reciprocal power: negative
exponents return zero. Hence `Zpower 2 (-2) = Zpower 2 (-1) = 0`, and the strict
monotonicity law needs a nonnegative upper exponent. Both assistants prove
this counterexample; mutations reject removing that premise, removing an
exponent premise from the addition law, admitting radix zero, or replacing
the negative-exponent answer by the absolute-exponent answer.

Thirty-eight unused named `*_check`/`*_spec` declarations were removed from
the reviewed prelude and this slice, after checking for repository callers.
Some were tautologies about an unrelated check result; the removed inversion
wrapper even used a `natAbs` premise unlike the source. The real direct
theorems and their existing proofs remain. This cleanup removes a misleading
parallel API; it does not claim every removed helper was mathematically false.

At the end of this slice the queue reached `Zmod_mod_mult`, with 28 dispositions.
Finite runtime agreement does not establish universal cross-assistant equivalence.

### Third ordered slice: division and remainder

The next eight contracts, `Zmod_mod_mult` through `ZOdiv_plus`, preserve the
source's exact domains. The operator translation matters:

| Convention | Rocq operations | Lean operations |
|---|---|---|
| Quotient truncated toward zero | `Z.quot`, `Z.rem` | `Int.tdiv`, `Int.tmod` |
| Quotient rounded down | `Z.div`, `Z.modulo` | `Int.fdiv`, `Int.fmod` |
| Nonnegative Euclidean remainder | Not a universal alias for the floor pair | Default integer `/`, `%` |

Lean's floor and Euclidean pairs agree for **nonnegative divisors**, including
zero's total-function convention; two universal Lean clients check that bridge.
The two reviewed source floor/modulo laws stay inside that domain. They do not
license a global replacement of `Z.div` with Lean `/`: for `7` and `-3`, the
floor answer is quotient `-3`, remainder `-2`, whereas Lean's default gives
quotient `-2`, remainder `1`.

The six truncating laws use explicit `tdiv`/`tmod`. The source permits divisor
zero in the unrestricted identities, and the fixtures retain it. The small-
absolute-value laws translate source `Z.abs` to integer-cast `natAbs`; paired
typed clients use ordinary `|a|` to check that presentation. Quotient addition
retains the genuine `0 ≤ a*b` premise: with `a=-2`, `b=1`, `c=2`, its left side
is zero and its purported premise-free right side is minus one. Both assistants
prove that counterexample; the Lean proof lists no axioms.

Sixteen more unused check/spec wrappers were removed after checking callers.
The obsolete `ZOdiv_plus_check` computed default Euclidean division while its
name/docstring suggested truncation; the actual direct `ZOdiv_plus` theorem was
already correct and remains unchanged. The remaining checked statements are
the source laws themselves, not tautologies about a parallel check function.
The paired fixtures also execute 1377 signed input triples per assistant.

The queue now has 36 dispositions (35 reviewed contracts and one adapted proof
infrastructure entry), leaving 2680 sites unreviewed in this conservative ledger.
The next entry is `Zsame_sign_trans`; earlier prose-ledger reviews are still
separate. The fresh `div_eucl` bridge checks 811 actual floor-division calls
against Rocq and generates 811 kernel equalities; it does not execute a theorem
as a numerical function or certify every division-mode identity universally.

## Unindexed Pff negation and absolute value (earlier slice)

The source facade now also exports `Fopp_correct`, `Fopp_Fopp`, `Fabs_correct`
and `Fabs_Fzero`, matching the compiled Rocq types at Pff.v lines 1506, 1512,
1567 and 1593. Negation correctness takes an unrestricted integer radix;
double negation and nonzero preservation do not mention radix at all.
Absolute-value interpretation retains the source `0 < radix` premise,
including radix one. A paired closed counterexample at radix -2 shows why
dropping the premise entirely would be false. The existing executable
negation and absolute-value bodies are unchanged.

Paired typed clients and four live mutations reject an identity-negation
conclusion and a premise-free absolute-value law in both assistants. Their
source shapes are not silently strengthened to the Core carrier's `1 < radix`.
The four production proofs are closed and introduce no debt.

## Exact remainder contracts

Four exports in `Prop/Div_sqrt_error.v` are now paired with typed Lean/Rocq
clients and pinned anchors: `format_REM_aux` (638), `format_REM` (772),
`format_REM_ZR` (837), and `format_REM_N` (858). Their existing definitions,
theorem types and closed proofs are unchanged. The auxiliary theorem requires
nonnegative dividend and positive divisor; the general theorem covers both
signs and mathematical total division by zero. The small-quotient premise
`|x/y| < 1/2 → rnd(x/y) = 0` is genuine, not removable clutter.

Both assistants prove a counterexample to dropping that premise: in two-bit
binary FLX, `1` and `8` are representable but upward quotient rounding produces
the nonrepresentable remainder `-7`. Truncation and either nearest tie policy
satisfy the premise; their source specializations need no nonzero-divisor
assumption. Exponent validity and monotonicity remain explicit.

The paired `ExponentValidityBoundary` fixture now proves monotonicity is
necessary even for truncation: in its valid alternating-precision format,
`7/4` and `1` are representable but their truncation remainder `3/4` is not.
Thus validity cannot replace monotonicity here. The ULP witness now states the
negation of nonnegative-input monotonicity directly; the simple ordering
conditions are discharged inside the proof, not appended to its conclusion.

An exhaustive three-bit bounded-format grid checks 12,100 inputs in kernel
Lean, compiled Lean and pinned Rocq. Of these, 11,582 meet the pointwise
small-quotient condition; 518 do not, with 380 actually inexact remainders.
The grid includes 220 mathematical zero-divisor cases. The quotient modes
are explicit integer test models, not proved executable refinements of the
real-valued `Ztrunc`/`Znearest` definitions. The actual `binary_round` exports
are executed and every constructor field checked against an independent exact
finite-grid oracle. This finite experiment is separate from the closed real
counterexample and from the four theorem contracts.

## Nearest-even concrete-point interface

`round_NE_pt` now exposes the same direct proposition as the pinned
`Core/Round_NE.v:521`: the specific value returned by nearest-even rounding
satisfies `Rnd_NE_pt`. Its former Boolean/Hoare theorem survives under the
explicit adapter name `round_NE_pt_check_spec`; the new theorem extracts the
existing closed proof. Both production Pff callers now consume the proposition
directly. No rounding algorithm, predicate or hypothesis was changed.

The paired `RoundNEPointContracts` fixtures distinguish seven compiled exports:
negation has no exponent assumptions, absolute value requires `Valid_exp`,
and the positive/all-input point theorems require `Valid_exp` and `Exists_NE`.
The point theorems have pinned anchors at lines 339 and 521. The totality,
monotonicity and combined rounding contracts at lines 263, 306 and 331 now
also return ordinary propositions, retaining `Valid_exp` and `Exists_NE`
without an extra `Monotone_exp` assumption. The old interfaces remain under
explicit `*_spec` compatibility names, and local consumers use the direct laws.
The redundant standalone `beta > 1` argument is supplied by `ValidRadix`,
the port's representation of the source structured-radix invariant.

All seven Lean axiom lists contain only the standard axioms. Eight live
mutation controls check concrete-result versus existence distinctions,
required format/parity premises and totality versus the combined monotonicity
contract. Baselines compile first in both assistants. No numerical body changed;
this is an API alignment, not a universal cross-assistant equivalence claim.

## ULP nearest rounding: eight erased policy parameters

Eight midpoint and neighbor exports accepted tie policies but stated their
results with the fixed ties-up chooser. The two-policy agreement theorem even
compared that same fixed value to itself. The repaired direct propositions
mention the actual supplied choices through roundR/round_to_generic and
Znearest. All eight proofs are closed; four obsolete private helpers are removed.

The paired UlpNearestChoiceContracts fixtures consume the source-shaped types,
prove the mathematical half-integer distinction, and execute the integer
decision `[0, 1]`. Four live mutations reject an erased second policy and the
wrong midpoint answer in both assistants. The local fixed-policy chooser's
body/type remains unchanged and is explicitly classified as local.

## Generic rounding and ULP: 27 unnecessary validity assumptions

A compiled-type survey of 266 same-named exports in Generic_fmt, Ulp,
Round_NE and Float_prop found 27 selected Lean signatures carrying
`Valid_exp` where the pinned Rocq type does not. Sixteen are in Generic_fmt
(nearest symmetry and small values, bounded rounding, mantissa recovery and
directed-rounding alternatives); eleven are in Ulp (negligible-exponent
witnesses, neighbor/spacing inequalities and the floor/ceiling gap).

The repaired types remove that assumption, including supporting helper
premises. Three bounded-rounding proofs now use the exact magnitude
determined by the given binade, rather than a weaker bound plus exponent
validity. The floor/ceiling-gap proof reconstructs representability from an
integer scaled mantissa, rather than invoking global rounding correctness.
No arithmetic definition body changed and no proof was admitted.
`succ_le_plus_ulp` still takes its genuine `Monotone_exp` hypothesis.

The paired `CorePremiseBoundary` fixtures freeze all 27 expected client
types, and 27 compiler-premise guards reject reintroducing `Valid_exp`.
Every client compiles in its assistant and all Lean axiom lists exclude
`sorryAx`. This is a focused extra-premise audit: it does not certify all
266 surveyed declarations or compare their entire mathematical meaning.
The separate `ExponentValidityBoundary` counterexample demonstrates why
exponent validity and monotonicity cannot be conflated.

## Logical-model adapters and the integer bit-decoder domain

`binary32OfModel` and `binary64OfModel` now execute after removal of two
unnecessary `noncomputable` markers; their bodies and types are unchanged.
They are explicitly Lean-model adapters, not standalone Flocq exports.
The model canonicalizes NaNs before source decoding. Raw source decoding
still preserves NaN sign and payload.

The first independent oracle incorrectly assumed every integer input wrapped
modulo the word width. Both actual assistants rejected that assumption:
pinned `Bits.v:77` uses `2^(mw+ew) <= x` for the sign, not the wrapped sign
bit. Mantissa/exponent fields use quotient/modulo. At binary32, source decode
then encode of `2^32 + 1` yields `0x80000001`; a UInt32-model route yields
`1`. At binary64, source decoding `-2^63` yields positive zero while the
UInt64-model route yields negative zero. These are out-of-bounded-word-domain
behaviors of two different interfaces, not port bugs. Paired closed fixtures
preserve both distinctions and the signed signaling-NaN distinction.

The five-column adapter bridge compares compiled Lean, kernel Lean and
pinned Rocq with explicit route-specific wrapping/canonicalization policies,
then bootstraps Lean kernel equalities. Independent arithmetic classification
checks every column; there is no native float FFI in this profile. The
1,140-case run includes 827 out-of-range inputs and 445 observations where
the two model routes differ. All seven harness tests pass, including live
mutations of all five columns at both widths and rejection of the original
wrong wrapping oracle. No universal model-adapter equivalence is claimed.

## Pff operational radix and native integer execution

Pinned Pff exports an unindexed integer record. Its normalized neighbors
and parity predicates consume their explicit integer radix. The older Lean
wrappers instead accept an ignored real-valued argument and operate at the
Core carrier's type radix. At bound `(9,10)`, precision two, and explicit
radix three, the source successor of `(1,0)` is `(4,-1)`, the predecessor of
`(2,0)` is `(5,-1)`, and normalized one is odd. A Core-base-two wrapper
returns `(3,-1)`, `(8,-1)`, and even, respectively. The bound is valid for
base three, not base two; these are interface distinctions, not violations
of a source theorem's valid-format premises.

`Pff.Source` now supplies `Feven`, `Fodd`, `FSucc`, `FPred`, `FNSucc`,
`FNPred`, `FNeven`, and `FNodd` with the source's single explicit radix.
The old normalized APIs remain compatibility adapters, explicitly marked
local. Two closed theorems commute raw successor/predecessor with carrier
conversion for every explicit operational radix and valid Core index;
there is no unproved global normalization bridge hidden in this result.

The complete source facade opts into the source-definition linter; 33 newly
added pinned anchors cover its previously unclassified surface. Four carrier
conversions and the Rocq logarithm boundary are explicitly local. A link is
provenance, not certification of the linked implementation or theorem.

Fifteen root definitions and three existing source-facade definitions lose
only unnecessary `noncomputable` markers. The permanent `PffExecution`
fixture invokes all eighteen in compiled code and checks the expected
results by kernel reduction. The 56-column differential profile separately
observes the explicit-radix and legacy indexed APIs, preserves nonpositive
radices and invalid later-theorem preconditions, and checks exact-rational
invariants under stated premises. See the running ledger for completed-run
counts; the surrounding Pff theorem library remains unreviewed.

## Pff auxiliary bounds and local helpers

Three newly executable source exports have pinned anchors in
`Pff2FlocqAux.v`: `make_bound` (156), `bsingle` (193), and `bdouble` (201).
The constructor takes a valid radix but any signed precision and exponent
bound. At negative precision, source integer exponentiation followed by
positive-carrier conversion gives mantissa bound one, not radix-to-absolute-
precision. Both signs of the exponent bound produce the same nonnegative
`dExp`; the lower permitted exponent is its negation. The paired fixture
pins these conventions and both predefined formats.

The indexed `PFnormalize` remains a **local adapter**, converting integer
precision through `natAbs`. Its cross-test reference explicitly applies
`Z.abs_nat` before calling Pff's natural-precision normalizer. This is not a
claim that the adapter and the source have identical signatures. The older
lowercase `pff_normalize` is only identity; its documentation and local
classification now say so. A kernel-checked counterexample distinguishes
it from normalization of `(1,0)` to `(4,-2)`.

Seven definitions lose only unnecessary execution markers: the three source
bounds, `PFnormalize`, and the local numerical `pff_compare`, `pff_max`,
`pff_min`. The last three have no separately claimed Flocq export; they are
tested independently against exact rational values, including equal-valued
unequal representations and the documented left-biased result on ties.
All algorithm bodies and type signatures are unchanged. The broader
auxiliary theorem library has not thereby been source-audited.

## Pff logarithm: total extensions are observable

Pinned `Pff/Pff.v:27157` uses Rocq Stdlib's `Rpower.ln`, whose definition is
zero for nonpositive inputs. Lean's `Real.log` instead satisfies
`log (-x) = log x`. Directly substituting the latter changed the total
source-facing `RND_Min_Pos`, which exports no radix-positivity premise.

With bound `(vNum=4,dExp=0)`, radix minus two, precision two, and real input
two, pinned Rocq proves the result is `(-4,-1)`; the old Lean formula yields
`(2,0)`. Both records denote the same real value, but their raw source results
are different. The corrected source facade uses an explicit `rocqLn` helper.
Paired closed fixtures check inputs two and minus two. A closed universal
Lean theorem preserves the entire previous result at every positive radix,
including precision zero and real inputs below the normal threshold.
All four printed regression-theorem axiom lists exclude `sorryAx`.

The helper is classified as a Rocq Stdlib boundary, not a Flocq-owned
declaration; `RND_Min_Pos` has its own pinned Flocq anchor. This correction
does not certify the separate, indexed legacy rounding API or all Pff
theorems. Nonpositive radices remain outside ordinary floating-point
correctness hypotheses even though the source definition is total there.

## Executable primitive entry points: keep the three interfaces separate

The remaining 33 definitions and four arithmetic instances in
`FaithfulPrimFloat` now compile without `noncomputable` markers. The diff
changes only those markers: bodies, binders, result types, validity evidence,
and correctness theorems are unchanged. A baseline client file fails at all
37 names before the change and the permanent paired fixture executes all 37
afterward. This is an execution repair, not a newly proved source equivalence.

Seven raw helpers correspond to binary64-specialized Rocq Corelib
`SpecFloat` algorithms. Fifteen primitive entry points correspond to Corelib
native operations or its `FloatOps` wrappers. Eleven proof-carrying helpers
correspond to binary64 specializations of pinned Flocq `BinarySingleNaN`;
four Lean arithmetic instances supply local notation. These are distinct
interfaces, not 37 separately owned Flocq declarations. Existing source
classification is not upgraded merely by making a body executable.

The three new bridge families observe each interface separately. Raw finite
inputs retain the source's positive mantissa domain. Primitive inputs are
produced by the corrected total numeric `SF2Prim`, and proof-carrying inputs
are projected from those converted values. The raw group is evaluated first,
without a rejecting adapter or normalization that could hide its behavior.

A paired closed example squares raw `(3,-1)`: Corelib's raw multiplication
returns noncanonical `(9,-2)`; converting first and multiplying primitive
values returns canonical `(5066549580791808,-51)`. Both denote 2.25.
This does not violate raw multiplication's validity theorem: its premise
requires canonical inputs. The fixture also checks all three decomposition
exponents, rather than accepting a correct fraction with a wrong exponent.

Forty deliberate replacements independently corrupt every one of the 33
API observations, four notation instances, and three decomposition exponents.
Each is detected in both Lean execution paths while unrelated columns stay
equal. A separate test restores a noncomputable client and requires
compilation failure. Heavy primitive families now use batches of at most 25;
the saved 200-case timeout remains an error, and all its inputs pass when
explicitly replayed in smaller batches. Counts and the running/completed
distinction for the broad seeded grid are recorded in the audit ledger.

## Predicate witnesses: the proof belongs in the result type

Pinned `Core/Round_pred.v:51,78` exports `round_val_of_pred` and
`round_fun_of_pred` with both a `round_pred rnd` input and a dependent pair
result. The old Lean API omitted the input, returned a bare real/function,
and chose zero when no witness existed. It proved a conditional property,
but did not expose the source's proof-carrying interface.

The repaired constructors return `{f : ℝ // rnd x f}` and
`{f : ℝ → ℝ // ∀ x, rnd x (f x)}`. The two local specification adapters
project the carried proofs. Paired compiled clients check those shapes,
identity examples, and the impossibility of supplying the empty relation.
Two additional closed Lean theorems universally preserve the former selected
value/function on valid inputs. No arithmetic body was made executable:
these are genuinely noncomputable mathematical witnesses using classical
choice. Five printed regression-theorem axiom lists contain no `sorryAx`.

The same result-sort mismatch was subsequently found in `Raux.LPO_min`,
`LPO`, and `LPO_Z` (pinned lines 2271, 2384, 2396). Rocq exports a `sumor`
whose positive branch is a dependent pair and whose negative branch proves
universal nonexistence. The old Lean declarations were propositions about
`Option` results; all three actual source-shaped baseline clients failed
because a `Prop` was supplied where a `Type` was required.

The new noncomputable definitions use `PSum` to carry the exact alternatives.
The minimal-natural branch retains `P n ∧ ∀ i < n, ¬ P i`, not a silently
rewritten weaker condition. Natural LPO projects that witness; integer LPO
follows the source's nonnegative search followed by negated-natural search.
The optional compatibility definitions keep their bodies/types unchanged;
their old theorem names move to the explicit `_choice_spec` names. There
were no repository callers of the old theorem names to migrate.

Paired `LpoSourceContracts` fixtures consume all three exact result shapes,
extract witnesses and their proofs, and cover a negative-only integer
predicate and the empty predicate. Two closed Lean projection equalities
preserve the old natural optional results for every predicate. No equality
with the old arbitrary integer choice is asserted. Live controls reject all
three old property-only results in Lean and an erased optional result in
Rocq. These are source-interface checks, not native predicate-decision tests
or universal cross-assistant witness-identity proofs.

## FLX unit laws: unrestricted precision is intentional

Pinned `Core/FLX.v:240,246` states `ulp_FLX_1` and `succ_FLX_1` for
every integer precision. Lean now does too, without its former positive
precision instance or pure-value Hoare wrapper. Both proofs remain closed,
and the two production callers consume ordinary equalities. The redundant
radix inequality follows from the existing `ValidRadix` carrier.

Paired Lean/Rocq clients prove that at base two and precision zero the ULP
at one is two and the defined successor is three; at precision minus one
they are four and five. These are laws of total definitions, not assertions
about adjacent values in a valid floating-point format. Positive precision
is still required by `negligible_exp_FLX` and the ULP-at-zero theorem.
Four new guards reject both the named precision class and the legacy
positivity `Fact` on the unrestricted laws. This repair brought the combined
premise guard count to **90**; later checkpoints extend that total.

## Parity and symmetry: do not import stronger rounding-correctness premises

Compiled pinned `Core/Round_NE.v` and `Prop/Round_odd.v` distinguish
these interfaces (all still have a valid radix):

| Source interface | Exponent assumptions in the compiled source |
|---|---|
| `DN_UP_parity_pos_prop`, `DN_UP_parity_prop` (47, 57) | None; these form propositions, not proofs that the propositions hold. |
| `DN_UP_parity_aux` (66) | None; assumes positive-case parity and derives signed parity. |
| `round_NE_opp` (482) | None; a symmetry of the concrete rounding function. |
| `round_NE_abs` (502) | `Valid_exp`, but no `Exists_NE`. |
| `round_odd_opp` (221 in `Round_odd.v`) | None. |

The former Lean interfaces added `Valid_exp` to the two propositions,
both `Valid_exp` and `Exists_NE` to the parity implication and nearest-even
negation law, `Exists_NE` to the absolute-value law, and `Valid_exp` to
round-to-odd negation. The six public signatures now match the source premise
boundaries. One private symmetry helper is similarly unrestricted.
Every existing proof body is preserved and closed; numerical definitions
are unchanged. Six pinned source anchors record the inspected exports.

Source-shaped clients failed in Lean before and compile after, while the
paired Rocq clients compile. Both provers additionally establish that binary
FLX precision one fails the source's `Exists_NE` class, yet its concrete
nearest-even rounder commutes with negation. Thus the old assumption excluded
a real positive-precision case. This does not identify the class with a
necessary-and-sufficient condition for nearest-even totality.
The actual parity-existence and nearest-even-correctness theorems keep their
source `Valid_exp` / `Exists_NE` assumptions; no blanket removal is made.

The compiled-premise guard now supports multiple named parameters, with
deliberate instance and explicit-premise leaks plus a selective control.
Eight new guards bring the production total to **98**, alongside seven
negative tests and two guard self-tests. Ten source/client theorem axiom
lists exclude `sorryAx`; fresh compiled trust retains four named debts.
This is an interface repair and bounded source audit, not a review of every
supporting nearest-even or round-to-odd proof.

## Total primitive conversion: wrapping and two rounding stages

`FaithfulPrimFloat.SF2Prim` previously treated all noncanonical encodings as
NaN. That is the rejecting `SF2B'` adapter's contract, not the total numeric
conversion in [Rocq Corelib FloatOps.v:50](https://github.com/rocq-prover/rocq/blob/adfbf1855c348766beb4b790dcc8ebc02f908f63/theories/Corelib/Floats/FloatOps.v#L50).
The source converts the positive mantissa through uint63, rounds that integer
to binary64, scales with the source's clamped `Z.ldexp`, then applies the sign.
The current valid-input roundtrip theorems do not constrain the other inputs.

The repaired definition retains its valid-input identity branch and executes
those stages for other finite encodings. The identity shortcut follows
Rocq Corelib's stated valid-input roundtrip axiom for native primitives
(`FloatAxioms.Prim2SF_SF2Prim`); this is not a claim that the two prover
implementations have a universal equivalence theorem. Existing Lean roundtrip
proofs remain unchanged and closed. The new helper constructs validity from
the existing proof-carrying rounding operations, without a new admission.
Lean's Nat finite carrier also admits zero; the source-positive differential
corpus deliberately excludes that extra local value.

The concrete cases distinguish three plausible but incorrect implementations:
rejecting `(3,-1)` gives NaN instead of `1.5`; forgetting uint63 wrapping
converts `(2^63,0)` to a large value instead of positive zero; replacing two
rounding stages with one converts `(2^53+5,-1077)` to mantissa
`1125899906842625` instead of `1125899906842624`, both at exponent `-1074`.
The bridge separately observes input validity, converted result, its
proof-carrying projection, output validity, and the rejecting adapter.
Thus the sentinel cannot hide this numeric conversion discrepancy.

## FLT format relationships: eleven unrestricted precision contracts

Compiled pinned `Core/FLT.v` omits positive precision from eleven exports:
`cexp_FLT_FLX` (130), `generic_format_FLT_FLX` (179),
`generic_format_FLX_FLT` (193), `round_FLT_FLX` (207),
`cexp_FLT_FIX` (217), `generic_format_FIX_FLT` (234), `ulp_FLT_le` (324),
`ulp_FLT_exact_shift` (366), `succ_FLT_exact_shift_pos` (381),
`succ_FLT_exact_shift` (394), and `pred_FLT_exact_shift` (419).
Their Lean counterparts inherited `Prec_gt_0 prec` from their sections.
All eleven now omit that premise. Ten former Hoare wrappers become ordinary
propositions; the rounding equality was already direct. Existing callers in
the addition, multiplication, and division/square-root error modules migrate
with them. The redundant explicit radix inequality is obtained from
`ValidRadix`; none of the numerical definitions changes.

The existing proofs remain closed. One private positive-predecessor helper
previously called a lemma covering nonnegative inputs, including zero, whose
proof requires validity of the exponent function. Its actual inputs are
strictly positive. Unfolding that branch directly avoids importing a stronger
premise through an unnecessarily general helper. The successor theorem for
positive inputs has the source's weaker magnitude/shift bounds, without the
extra `+1` used by the signed successor and predecessor statements; a copied
source comment previously blurred this distinction and is corrected.

The neighboring reverse inclusion `generic_format_FLT_FIX`,
`FLT_format_generic`, `ulp_FLT_gt`, and `ulp_FLT_pred_pos` retain the source's
positive-precision premise. This is intentional, not incomplete cleanup.
Paired Lean/Rocq proofs show that at base two, precision zero, and minimum
exponent zero, `1` satisfies the reverse inclusion's size bound and belongs
to FIX, but does not belong to FLT. The revised forward statements and this
counterexample compile in `SourcePremiseContracts.lean/.v`. Eleven additional
production guards bring the selected compiled-premise total to **86**.
These clients check this interface boundary, not whole-module equivalence.

## Raw primitive comparison: preserve the source's encoding order

`FaithfulPrimFloat.SFcompare` now follows Rocq 9.2 Corelib's constructor,
sign, exponent, and mantissa cases. `SFeqb`, `SFltb`, and `SFleb`
inspect that result. The previous implementation compared the real
interpretations, which differs on noncanonical positive-mantissa encodings:
`(3,-1)` and `(6,-2)` are equal as reals but the raw source comparison is
greater-than. This is a total raw contract mismatch, not a demonstrated
failure on valid binary64 operands.

The exact source is
[Corelib SpecFloat.v:163–213](https://github.com/rocq-prover/rocq/blob/adfbf1855c348766beb4b790dcc8ebc02f908f63/theories/Corelib/Floats/SpecFloat.v#L163),
at the peeled Rocq 9.2.0 release commit, not a declaration owned by the
pinned Flocq checkout. The Lean declarations carry explicit external links
and a `flocq_local` classification explaining that provenance.
Rocq's finite mantissa is positive; Lean's raw Nat carrier additionally admits
zero. Shared tests require a positive mantissa rather than claiming a source
equivalent for the extra constructor values.

All twelve existing entry points are executable at their original names:
the four raw operations, four `PrimitiveFloat` wrappers, and four
`PrimBinaryFloat` wrappers. No parallel `*C` API is necessary. Wrapper
bodies and signatures are unchanged. A closed structural theorem
`SFcompare_B2SF` connects raw comparison to the generic proof-carrying
comparator. The native model's matching proof is now structural too; its
public binary32/64 statements are unchanged. No new proof debt is introduced.

The paired `PrimitiveComparison` fixtures use literal expected results and
separately prove the equal-real/unequal-encoding example. The bridge observes
raw results before validation, retains each validity flag, and calls the two
validated API surfaces separately. Its Rocq primitive group genuinely executes
the native primitive, while its other groups run integer definitions.
Twelve deliberate output mutations each alter exactly one independently
observed API column.

## Executable normalization: source interfaces versus compatibility carriers

Pinned `Binary.v:1019` and `BinarySingleNaN.v:1751` export normalizers with
positive precision and `prec < emax`. Both take a mode, signed integer
mantissa, integer exponent, and zero sign. Compiled Lean and Rocq types match
these premises for the source-facing entry points. The full-payload Lean
implementation constructs the proof-carrying result from the same signed
rounding branches; the source wraps its SingleNaN result with the non-NaN
conversion. A source anchor identifies this correspondence without claiming
that an anchor proves equivalence.

The remaining `noncomputable` markers on `Binary.binary_normalize`, the root
raw compatibility `binary_normalize`, and
`binaryRoundAuxToBinarySingleNaNFloat` prevented ordinary compiled clients.
Their bodies and types use only integer computation and proof-carrying
construction; removing those markers makes the clients execute. The latter
two are explicitly classified `flocq_local`: the raw compatibility carrier
does not have the source's proof-carrying result type, and the validity adapter
has no separate source declaration. It would be misleading to give either an
exact source-interface label merely because it participates in the algorithm.

The `normalize` bridge family observes all three normalizers separately,
and the existing raw IEEE-rounding family now separately observes the local
validity adapter. Its premise is validity of the computed result, not validity
of every format parameter. Both a valid NaN and a rejected finite encoding are
possible; a separate flag prevents the rejection sentinel from hiding that
difference. The paired literal fixtures cover both cases and a malformed
format that nevertheless produces a valid zero. Earlier raw-rounding receipts
covered sixteen columns; the extended family requires twenty-one.

## FTZ inclusion: preserve each direction's actual premises

Compiled pinned Rocq `FLXN_format_FTZ` (FTZ.v:71) and `generic_format_FTZ`
(line 80) have no positive-precision premise. Both Lean exports inherited
`Fact (0 < prec)` from their sections. The normalized inclusion is merely a
projection of the FTZ witness, and the existing generic inclusion proof also
works without that fact. The two exports and the private forward helper now
omit it, preserving the mathematical proof bodies. The generic export calls
the existing forward helper directly instead of obtaining it through an
equivalence that also includes the more restricted reverse direction.

The source's reverse inclusion, FTZ-from-normalized inclusion, and
`satisfies_any` theorem retain positive precision; no blanket removal is made.
Paired typed clients fail in Lean before and pass after the repair, while the
Rocq clients compile. Paired universal zero examples work at every integer
precision. The regression guard now also recognizes `Fact (0 < prec)`, with
a deliberate leaking declaration demonstrating rejection. Two new source
guards bring the total to 75. This is a source-type repair, not an arithmetic
algorithm change or a claim about hardware formats with nonpositive precision.

The FTZ docstrings also now distinguish the actual witness predicate from its
generic-format characterization. The small-magnitude exponent branch is
`emin + prec - 1`, not simply `emin`; an integer rounding policy is a separate
argument. The implementation already used the correct expression.

## Square root: bracket correctness does not require a valid format

Compiled pinned `Calc/Sqrt.v:179` permits any exponent function in
`Fsqrt_correct`. The Lean export had an extra `Valid_exp fexp` premise. That
instance is now removed, with the existing proof unchanged except for its
call to the magnitude lemma. `mag_sqrt_F2R` (line 53) now derives the radix
inequality from the existing `ValidRadix` carrier rather than asking for a
second explicit proof. Its expression `(Zdigits beta m + e + 1) / 2` matches
Rocq's signed `Z.div2`, including negative odd exponents. Three theorem anchors
record the inspected source; the two previously failing Lean clients now
pass, as do paired Rocq clients and a new compiler premise guard (73 total).

This does not justify discarding square root's other hypotheses. The core
theorem (line 73) still requires a positive mantissa and `2 * target ≤ inputExponent`.
The paired `CalcBrackets` fixtures check 8,640 division brackets and 2,496
square-root brackets against independent integer inequalities. They also
prove a counterexample outside the exponent premise: `Fsqrt_core 2 9 0 1`
returns exact zero, which does not bracket the real square root three.
The high-level `Fsqrt` routine chooses its exponent to enforce this premise,
even for an arbitrary exponent function. It constructs a bracket; format
closure and rounded-result properties are separate contracts.

## Division: computed bounds and direct result contracts

Pinned `Calc/Div.v:48` bounds the quotient magnitude using the explicit integer
`(Zdigits beta m1 + e1) - (Zdigits beta m2 + e2)`. The former Lean public
`mag_div_F2R` was a Hoare triple over a dummy computation, ignored the returned
integer, and instead stated abstract magnitude-difference bounds. Those bounds
are mathematically related under the positive-mantissa hypotheses, but they
were not the source's stated interface. Its two callers had to perform the
missing digit-count rewrites themselves.

The public theorem now gives the source's integer bounds directly; the unused
dummy projection is removed. `Fdiv_core_correct` (source line 70) is likewise
an ordinary proposition about the returned mantissa and location. Both derive
radix validity from the existing `ValidRadix` carrier rather than requiring
an additional explicit proof argument. The two magnitude clients and the
core-correctness client migrate together, with all proofs closed and no
numerical algorithm changes. The source-absent left-branch proof helper still
uses its existing local Hoare interface; this is not a blanket migration.

Two typed Lean clients failed before the correction and now pass. Their
paired pinned Rocq clients also compile. Complete Lean diagnostics are clean
for both changed source files and the test module. The 6,216-job macOS build,
201 source-anchor check, and 13,588-declaration compiled trust audit pass with
the same four named debts. A fresh 1,994-case division/format-calculation grid
and ten-case all-mode IEEE replay agree in all three execution paths and
generate passing kernel equalities. Detailed receipts are in the audit ledger.
This repair improves interface fidelity; it is not a numerical counterexample
or a proof of whole-module source equivalence.

## Raw rounding, structural laws, and multiplication-error bounds

Compiled pinned Rocq permits arbitrary exponent functions in `Generic_fmt.round`
and its structural zero, exactness, extensionality, and negation laws. The Lean
`round_to_generic` wrapper and 16 associated laws/compatibility helpers had
acquired an extra `Valid_exp` instance. The formula itself does not need that
instance; all 17 binders are now removed with proof bodies unchanged.
Public source counterparts have pinned links; the two purely Lean compatibility
helpers are explicitly classified as local.

This is deliberately not a blanket change. Source `round_ZR_abs`, `round_AW_abs`,
`round_abs_abs`, and monotonicity/format-closure contracts retain their validity
premises. Being able to apply the raw formula does not establish that an
arbitrary exponent function defines a well-behaved floating-point format.
The new paired examples prove that `fexp(e) = e + 1` is invalid and nevertheless
apply the source zero-rounding theorem to it.

The `Calc.Round` zero adapter also no longer requires `Valid_exp`. Its public
contract is now the ordinary equality `round beta fexp mode 0 = 0`, with its
three callers migrated together. Its `Mode` carrier already supplies the
only needed fact, that integer rounding maps zero to zero.

Pinned `Prop.Mult_error.v:274` and `Pff/Pff2Flocq.v:1277` additionally omit
`Prec_gt_0` on `mult_error_FLT_ge_bpow` and its nearest-even specialization.
Those two Lean signatures now match that boundary, preserving the format,
product-size, nonzero-error, and valid-integer-rounder hypotheses where the
source requires them. Existing proofs remain closed. The other seven reviewed
`Mult_error` signatures and four reviewed Sterbenz signatures did not reveal
additional premise/conclusion mismatches in this inspection.

Twenty new compiler guards bring the total to **72**. All 20 failed before
the correction; the paired pinned Rocq clients compiled. Typed Lean consumers
also exercise the corrected interfaces without the extra instances. Build
and execution receipts for this slice are recorded in the running audit.
This remains a selected source-contract review, not whole-module certification.

## Canonical exponents and real comparison names

Four further Generic_fmt exports now omit a source-absent `Valid_exp`
instance: `lt_cexp_pos`, `lt_cexp`, `cexp_le_bpow`, and `cexp_ge_bpow`.
Pinned Generic_fmt.v lines 1560–1600 use only monotonicity of the exponent
function. The existing Lean proofs remain closed after removing validity;
the one fully explicit downstream application was updated with the signature.
Four new elaborated-type guards bring the premise-guard total to 41.
Paired Lean/Rocq typed consumers enforce the actual source hypotheses. A Lean
control both proves that `e ↦ e + 1` is not a valid rounding exponent and
uses its monotonicity with the corrected theorem.

Five Raux source names previously denoted numeric wrappers solely for
documentation links: `Rcompare_Lt`, `Rcompare_Eq`, `Rcompare_Gt`,
`Rcompare_not_Lt`, and `Rcompare_not_Gt`. They now denote the corresponding
ordinary propositions, with closed proofs and paired typed consumers.
The same repair now covers `Rcompare_IZR` (Raux.v:468): its public name
denotes equality between real-cast comparison and integer comparison codes,
not a bare integer result. The old triple uses `Rcompare_IZR_check` and its
proof delegates to the closed proposition. The pre-repair typed Lean client
failed where the paired Rocq client succeeded; both pass after the repair.
The legacy `Raux.Rcompare` representation still encodes Lt/Eq/Gt as -1/0/1;
this change does **not** claim a whole-Raux migration to `Ordering`.
The old `_spec` triples remain compatibility interfaces. A source link
identifies the source theorem but does not conceal this representation
adaptation.

Verification at source SHA-256
`f090bf1b61a88787880f7f091255bc7307fa803b0c2d645edadaa18587d1bcd1`:
the full macOS Lean 4.34.0 build passed 6,215 jobs; paired Rocq consumers and
the previously failing Lean consumers pass. Fresh complete LSP diagnostics
are clean for Raux, Generic_fmt, LeanFloat, and SourcePremiseContracts.
The test module's first editor session reported stale failed dependencies;
it became clean only after the successful build and a server restart.
The compiled validator checks 135 source anchors, and the trust audit checks
13,574 declarations in 58 modules with the same four manifest debts.

## Generic IEEE comparison: type, execution, and premise boundary

The previous `Binary.Bcompare` returned `Option Int` and compared mathematical
reals, while pinned `Binary.v:773` exports `option comparison`. The SingleNaN
facade returned `Option Ordering` but was likewise noncomputable. A typed Lean
consumer failed where the equivalent Rocq consumer compiled.

Both public exports now return `Option Ordering` and use the pinned
constructor/sign/exponent/mantissa comparison algorithm. Their real-value and
operand-reversal theorems have closed proofs. None gains a positive-precision
or `prec < emax` premise: paired typed consumers and four additional compiler
guards enforce that boundary, bringing the total to 45. The old raw-carrier
integer encoding remains only under the explicitly named compatibility API.

Binary32/64 comparison delegates to the generic source algorithm, matching
the source alias. The former independent fixed-width implementation was
removed; current generic/fixed-width agreement is therefore a wiring check.
Native Float/Float32 and pinned Rocq remain independent execution checks.
The new generic corpus includes raw invalid carriers and degenerate formats.

At source SHA-256
`ef0fbd7b679679ce0bccc073d2b732fd31741f101f7067887c3b4b69e10fbb1a`,
the full macOS Lean 4.34.0 build passed 6,215 jobs. Fresh complete LSP error
diagnostics were empty for BinarySingleNaN, its source facade, Bits,
SourcePremiseContracts, and BitOrderExecution. The paired Rocq consumers and
independent ordering fixture compiled. The validator checks 142 source
anchors; the compiled trust audit checks 13,591 declarations in 58 modules
with the same four manifest debts and no new project axioms or runtime
overrides. These checks do not certify every declaration in the modules.

The public-API differential run passed 3,567 cases and 3,567 generated kernel
equalities (seed 668019, 100 random samples per family), including generic
comparison and both fixed-width order families. Artifacts are retained at
`/private/tmp/floatspec-comparison-public-20260920`. All 29 core harness tests
passed, including the new live operand-swap mutation. The initial standalone
Rocq fixture command used a different output basename, then omitted explicit
arguments to source definitions; those setup failures were corrected before
the passing paired-consumer run and are not counted as semantic mismatches.

## SingleNaN Boolean comparison execution

Pinned `BinarySingleNaN.v:628,652,666` defines `Beqb`, `Bltb`, and `Bleb`
through `SpecFloat.SFeqb`, `SFltb`, and `SFleb`. Inspecting the compiled Rocq
definitions confirms they inspect `SFcompare`: equality accepts only `Eq`,
strict order only `Lt`, and non-strict order `Lt` or `Eq`; `None` yields false
for all three. The old Lean definitions had correct finite real-value
contracts but were noncomputable. A compiled signed-zero equality client
reproduced this execution gap before the change.

The root definitions and `BinarySingleNaN` aliases now use the already proved
integer `Bcompare`, with no additional precision premise. The three finite
correctness proofs and `Beqb_refl` remain closed and depend only on standard
Lean/mathlib axioms, not `sorryAx`. The definitions were moved after their
comparator dependency; public names and theorem signatures are preserved.
Six new source anchors cover the implementations and source-facing aliases.
Pinned `Binary.v` does not export an analogous trio of full-payload Boolean
names; this patch does not invent those source declarations.

At source fingerprint
`53593e9a2aedc6a490a35f735d00a35033837eaaa9eae3bbe1384c7a9f620212`,
4,210 ten-format comparison rows agree in compiled Lean, kernel reduction,
and pinned Rocq (seed `702061`, 300 supplemental samples per format). All
4,210 Rocq observations also check as individual Lean kernel equalities.
Eight paired boundary assertions, 600,000 native Boolean comparisons, and
34 harness tests including real mutations pass. This is targeted source/body
review and finite execution evidence, not whole-library semantic certification.

## Elaborated premises, not just displayed theorem text

### Full-payload injectivity and canonical mantissas

Pinned `Binary.v:321,392,473` exports `canonical_canonical_mantissa`,
`B2R_inj`, and `B2R_Bsign_inj` without `Prec_gt_0` or `Prec_lt_emax`.
Rocq's compiled types confirm the absence; the corresponding SingleNaN Lean
interfaces already match. Full-payload typed Lean clients reproduced the
failure with no positive-precision instance. The root compatibility helper
had retained both section instances and propagated them into the full-payload
proofs. Removing that helper's unused instances allows the unchanged proof
bodies to close under the source hypotheses.

The fix covers three source-facing Binary exports, the root `B2R_inj`
implementation, and its canonical-mantissa helper. Finite-strictness remains
required for the first injectivity statement; finiteness plus sign equality
remains required for the signed version. No value/body semantics changed and
no proof debt was added. Five additional compiler guards bring the total to
50; three paired typed Lean/Rocq consumers enforce the full no-extra-premises
signatures. The first draft of the new canonical consumer accidentally used
the internal `FLT_exp` arguments in source order; the typechecker rejected
it. The corrected consumer uses internal precision/minimum-exponent order.

All five affected proofs have no `sorryAx`. The full macOS Lean 4.34.0 build
passes 6,216 jobs; complete LSP diagnostics are clean for both edited source
modules and SourcePremiseContracts. The compiled trust audit remains at
13,594 declarations in 58 modules with four manifest debts. The source-link
validator now checks 153 anchors. The formerly failing standalone injectivity
client and the paired Rocq consumers pass.

### Earlier Prop and exponent-function premise repairs

An additional compiler-assisted review found **31 unwanted premises across
26 public exports**. These problems predate the 23-commit Sol audit range:
the old `round_repr_same_exp` comment claimed its `Valid_exp` premise was
absent, but Lean's elaborated type still contained it. A consumer without
that instance failed while the corresponding pinned Rocq consumer compiled.
The old regression used only `#check`, which established name availability
but did not enforce the intended type.

| Module | Source exports corrected | Premise correction |
|---|---|---|
| Plus_error | `round_repr_same_exp`, three nonzero/zero-sum lemmas, `ex_shift`, `round_plus_F2R`, `round_plus_ge_ulp`, both operand error bounds | Remove leaked `Valid_exp`, `Monotone_exp`, or `Exp_not_FTZ` instances where absent from Rocq's exported type. |
| Mult_error | The three `mult_bpow_*` lemmas | No positive-precision premise in these source exports. |
| Div_sqrt_error | `generic_format_plus_prec`, `sqrt_error_N_FLX_aux1` | Likewise allow arbitrary integer precision. |
| Relative | Four conversion lemmas and `u_ro_pos` | Conversions do not need `Valid_exp`; nonnegativity of unit roundoff does not need positive precision. |
| Round_odd | `Rnd_odd_pt_opp_inv`, `generic_format_fexpe_fexp`, `d_le_m`, `m_le_u`, `m_eq_0`, `Fm`, `Zm` | Remove only the source-absent validity instances, including target-format validity on `Fm`/`Zm`. |

The patches use `omit` to prevent accidental section-instance inclusion.
`round_repr_same_exp` now has a short direct arithmetic proof; its redundant
old proof wrapper was removed. The affected proof bodies otherwise remain
closed without new sorries. The local nearest-point helper and two midpoint
helpers were adjusted with their callers.

`Test/SourcePremiseContracts.lean` contains 31 compiler-backed guards and six
fully typed consumers for these Prop repairs, plus the IEEE checks below.
Each guard inspects the elaborated type and resolves
predicate aliases; a missing parameter is an error. Deliberate negative tests
cover implicit instances, explicit premises, aliases, and misspelled names.
All 31 guards and all six consumers failed against the pre-fix snapshot;
they pass after the corrections. The paired Rocq fixture checks the six
consumer types against the actual pinned exports.

This is not blanket removal of every unused instance. We inspected the
compiled Rocq types as well: `relative_error`, `relative_error_N`, `d_ge_0`,
`DN_odd_d_aux`, and `UP_odd_d_aux` retain their source `Valid_exp` premise.
The `ValidRadix` carrier invariant also remains. The guard checks the selected
premise boundary, not every possible alteration of the rest of a theorem.

## Integer truncation and nearby-integer rounding

The compiled Rocq exports distinguish the algorithm from its correctness
premises. `Binary.Btrunc` and `BinarySingleNaN.Btrunc` require no precision
instance at all; their value theorems require `prec < emax`. The `Bnearbyint`
algorithm and its correctness theorem likewise require `prec < emax`, but
not the additional `0 < prec` instance previously present on the Lean Binary
exports. That extra premise is now removed, with six additional elaborated-
type guards and typed consumers that omit it. The paired Rocq consumers
compile against the exact pinned declarations.

The previous public truncation definitions used real-valued `Ztrunc`, so they
could not execute. Both now use the source finite-case integer algorithm at
`BinarySingleNaN.v:2680`, via a shared `Binary.BtruncSingle` implementation.
Zeros and nonfinite values return zero, just as in the source. Closed proofs
establish its real-value theorem under the source `Prec_lt_emax` premise;
the full-float wrapper uses the already-proved SingleNaN value conversion.
Nearby-integer bodies are unchanged; their unnecessary noncomputable markers
are removed. The old definitions and extra premise already exist in upstream
`158263e9`, predating the 23 Sol commits.

The paired `IntegerRounding.lean` / `.v` oracle independently chooses integer
answers using signed division by eight and exact distance/parity. Both
assistants check 5,125 cases and idempotence; Lean proves the complete finite
grid in its kernel. Deliberately forcing nearest-away fails under nearest-even
at `-500/8`. The separate bit-level bridge retains signed zero, NaN payloads,
unbounded integer outputs, and explicit native-comparison restrictions.

## Generic successor, predecessor, and ulp

Compared the actual branches of `BinarySingleNaN.v:3099,3242,3412` and the
payload-preserving lifts in `Binary.v:1368,1392,1421`. Successor sends either
zero to the minimum positive subnormal, keeps positive infinity, sends
negative infinity to the negative maximum finite value, and preserves NaN.
Positive finite values round `(m+1,e)` upward; negative finite values round
`(2*m-1,e-1)` toward zero. Predecessor is sign reversal around successor.
Ulp returns positive minimum subnormal at zero, positive infinity at either
infinity, preserves NaN, and rounds the unit mantissa at a finite input's
exponent. The Lean finite ulp branch uses `binary_round` where the source
uses normalization of positive one; the normalization's zero/sign branches
therefore do not apply.

Eight unnecessary `noncomputable` markers are removed without changing
bodies or types. The SingleNaN and full-payload interfaces are both exercised
by the expanded bridge; the full-payload paths retain exact NaN bits. Their
existing real-valued correctness theorem statements were not changed by this
execution-enabling slice. This branch comparison and finite execution do not
constitute universal source-equivalence proofs.

## SingleNaN normalization, decomposition, and alternate neighbors

Twelve compiled signatures were compared between the source facade and
pinned Rocq: `binary_normalize`, `Bone`, `Bldexp`, `Bfrexp`,
`Bfrexp_correct`, `is_nan_Bfrexp`, `Bulp'`, `Bulp'_correct`,
`Bpred_pos'`, `Bpred_pos'_correct`, `Bsucc'`, and `Bsucc'_correct`.
Their inspected premises and conclusions match, accounting for the named
rounding-mode and carrier representations. In particular, **do not remove**
these source restrictions:

- `Bfrexp` needs positive precision, but not `prec < emax`; its exact
  decomposition theorem is about strictly finite inputs. The normalized
  fraction and magnitude conclusion additionally needs `2 < emax`.
- `Bulp'_correct` and `Bsucc'_correct` require `2 < emax` and a finite input.
- `Bpred_pos'_correct` requires `2 < emax` and a positive real value.

The implementations' case splits and exponent calculations were read against
`BinarySingleNaN.v` lines 1751, 2723, 2857, 3042, 3173, 3453, and 3661.
The normalization facade delegates through the existing full-payload
normalizer; its signed integer and signed-zero inputs are retained.
The alternate positive predecessor's `2 * mantissa = 2^precision` branch
uses the exponent of the preceding binade, just as in the source. The
alternate successor handles zero and both infinities separately and uses
that positive predecessor only after negating a negative finite input.

The paired `SingleNaNHelpers` fixture includes literal boundaries and two
domain counterexamples: alternate ulp at infinity differs from primary ulp;
positive-only predecessor at negative one differs from ordinary predecessor.
It also demonstrates why the normalized-fraction claim fails when `emax = 2`.
The 46-field `single_helpers` bridge independently calls every newly
executable helper. Its **bundle** uses the common `0 < prec < emax` domain;
that test restriction must not be mistaken for the weaker type of `Bfrexp`
itself. A subsequent separate `single_frexp` family passes 4,169 cases over
40 parameter pairs, including 3,455 with `prec >= emax`. Paired independent
integer-law fixtures cover 6,772 raw finite encodings in seven formats.
These add finite evidence in the wider type domain, not exhaustive coverage
of every positive-precision parameterization.

This slice removes eleven unnecessary execution markers without changing
algorithm bodies, types, or proof bodies. The signed-shift aliases refer to
Rocq Stdlib `SpecFloat.shr_fexp`, exposed by Flocq notation, not a standalone
Flocq declaration. Compiled type snapshots are retained as
`/private/tmp/SingleHelperContracts-lean.out` and `-rocq.out`.
These inspections and finite execution are not a universal proof of source
equivalence or a review of every supporting lemma in the large IEEE module.

## Double rounding: definitions and main exports

The six exponent-condition definitions in `Prop/Double_rounding.lean` were
compared clause by clause with the pinned source: multiplication (source
line 613), addition (848), radix-at-least-three addition (1808), square root
(2574), radix-at-least-four square root (3008), and division (3730).
Their quantifiers, strict/non-strict endpoints, offsets, and conjunctions
match the source forms read. The `round_round_eq`, `midp`, and `midp'`
definitions match source lines 36, 67, and 70, respectively.

The generic main exports for multiplication, addition, square root, and
division were also read, together with their FLX/FLT/FTZ specializations.
The essential conditions are preserved:

| Family | Selected source conditions retained |
|---|---|
| Multiplication | Product-format exponent bounds; twice-precision bound; FLT/FTZ minimum-exponent bounds. |
| Addition | Four exponent-function clauses; `2 * prec + 1 <= prec'`; FLT `emin' <= emin`; FTZ `emin' + prec' <= emin + 1`. |
| Square root | Three exponent clauses; `2 * prec + 2 <= prec'`; the disjunction of FLT minimum-exponent bounds; FTZ's two-sided exponent condition. |
| Division | Five exponent clauses; even radix; nonzero denominator; `2 * prec <= prec'`; the distinct FLT and FTZ exponent bounds. |

Parameter order is deliberately not assumed identical: namespaced Lean
`FLT_exp`/`FTZ_exp` take precision before minimum exponent, whereas the root
compatibility abbreviations and Rocq use minimum exponent before precision.
The inspected applications account for this difference.

The Lean radix premise `1 < beta` is supplied separately from `ValidRadix`;
Rocq bundles it in `radix`. Precision hypotheses declared in Rocq sections
must be checked against the **compiled** statement: unused section variables
are omitted by Rocq. The September 20 compiled recheck corrects the earlier
claim of stronger multiplication specializations: both assistants' FLX and
FLT exports omit positivity premises; both FTZ exports retain positivity of
the first precision only. Those statements match; they are not Lean-only
generalizations. The Lean `round_round_sqrt_FTZ` does prove its statement for every valid radix,
where the source export takes an unused `4 <= beta` premise. These are
documented generalizations, not discovered counterexamples. No premise was
removed during this review. The additional compiled check also confirms the
three public square-root exponent-hypothesis helpers require only the first
precision's positivity, and both same-place midpoint lemmas require validity
only of the first exponent function. The stronger `_from_..._payload`
helpers are compatibility endpoints, not the source exports. Receipt:
`/private/tmp/DoubleRoundCompiledContracts-v2.out`.

A further paired compilation on September 20 checks all nine displayed
definition bodies by reflexivity and source-shaped clients for
`round_round_mult_aux`, `round_round_mult`, `round_round_plus`,
`round_round_minus`, `round_round_sqrt`, and `round_round_div`.
The multiplication clients need no `Valid_exp`; the remaining four retain
validity of both exponent functions. Square root introduces no extra
nonnegative-input premise, and division retains even radix and nonzero
denominator. All six Lean client axiom lists exclude `sorryAx`.
Receipts are `/private/tmp/DoubleRoundingSourceClients20260920-lean-v2.out`
and `-rocq-v3.out`. Earlier scratch drafts failed on import/name/coercion
syntax and are not passes. This reinforces the bounded interface review
above; it is not an additional whole-module proof review.

These nine body guards and six typed clients are now permanent:
`FloatSpec/Test/DoubleRoundingContracts.lean` and
`scripts/fixtures/DoubleRoundingContracts.v`, both in the combined runner.
A paired closed counterexample uses exponent functions `e - 1` and `e - 3`:
the radix-at-least-four square-root hypothesis holds, while the ordinary
square-root hypothesis fails. Thus the `-1` versus `-2` offset is not merely
notation. Live controls reject an off-by-one body guard in both assistants
and an unnecessarily strengthened multiplication client in Lean. All six
typed clients and the counterexample have axiom lists excluding `sorryAx`.

The [paired double-rounding witness](../../scripts/fixtures/DoubleRoundingWitness.lean)
executes `binary_round` directly and has a closed Lean kernel equality and
Rocq `vm_compute` proof: `73/64` rounds directly to three-bit `1.25`, but
rounding through four-bit `1.125` gives three-bit `1`. Both signs are checked.
This explains why unconditional double-rounding equality would be wrong.
It does not execute the noncomputable real-valued theorem or exhaust the
conditional theorem families.

Not covered here: the hundreds of internal helper statements/proofs in this
large module, the radix-specialized theorem exports beyond the inspected
condition definitions, or universal equivalence of the two assistants' real
number constructions.

## SingleNaN validity boundary

The proof-carrying `BinarySingleNaN.valid_binary_B2SF` facade uses the real
`validBinarySingleNaNStandardFloat` predicate and agrees with source
`IEEE754/BinarySingleNaN.v:113`. The root-namespaced namesake has now been
corrected to take the proof-carrying carrier and establish that same real
validity predicate. The root `binary_fit_aux_correct` likewise now combines
the existing private validity proof with its finite/overflow semantic proof,
instead of exporting the always-true compatibility predicate as its first
conjunct. Both proofs are closed; explicit typed consumers prevent regression
to the weaker signatures.

The paired `SingleNaNValidity.lean` / `SingleNaNValidity.v` fixtures check
five finite representations at precision 3 and maximum exponent 4. The
representation `(mantissa=1, exponent=0)` is rejected as noncanonical even
though it denotes the real number one; `(4,-2)` is accepted. Minimum
subnormal and overflow boundaries are checked. Lean's Nat-based raw carrier
also rejects mantissa zero, which Rocq's `positive` field cannot construct.
The Lean fixture consumes the proof-carrying source theorem explicitly.

This is a validity-contract check, not a claim that every historical raw
`B754` or `Binary754` wrapper has been migrated to the source carrier.

The next differential slice caught two further raw-carrier errors. The old
root `SF2B'` used the range-only `bounded` helper, so it accepted `(1,0)`
instead of returning NaN as the source total converter does. The separate
`validB754` predicate used `m < 2^(prec-1)`, rejecting canonical `(4,-2)` at
precision three while accepting some noncanonical mantissas. Both errors
predate upstream `158263e9`, hence also predate the 23 Sol commits.

The converter and its roundtrip-domain predicate now require positivity
and `specFloat_bounded`; `validB754` uses the actual validity test on the raw
carrier's standard-float view. The four original counterexamples pass in
compiled Lean, kernel reduction, and pinned Rocq after failing in both Lean
paths before the patch. Seed `860213` yields **1,180 cases**: the old snapshot
has **240 mismatches**, and the repaired snapshot has none, with all 1,180
generated kernel equalities checked. This includes raw validation/conversion
with nonpositive precision or `emax <= prec`; those are total-function
observations, not applications of arithmetic theorems outside their domains.

The permanent paired fixture records canonical/noncanonical one and minimum
subnormal/overflow boundaries. Lean additionally checks that zero Nat
mantissas are rejected and proves agreement of the raw and proof-carrying
total converters for every `StandardFloat`. The bridge rejects zero mantissas
as a shared input because Rocq's `positive` constructor cannot represent one.

## Relative-error statements and executable boundary

The definition `u_ro` and its four positivity/size lemmas were checked against
`Prop/Relative.v:500-524`. In particular, the source lemma named `u_ro_pos`
states nonnegativity, not strict positivity; the Lean inequality is not a
weakening of that source statement. The FLX nearest relative bounds and their
existential/reversed forms, and the FLT nearest bounds and mixed relative /
absolute-error exports at source lines 729-958, retain the inspected factors,
quantifiers, normal-magnitude hypotheses, and `eps * eta = 0` side condition.
This is statement review of those exports, not all proofs in `Relative.lean`.

The paired `RelativeErrorGrid.lean` / `.v` fixtures check 4,092 cases: three-bit
precision, both signs, both nearest tie policies, and 1,023 dyadic magnitudes
below overflow. Results and errors are converted to exact integer units of
`2^-8`. At normal magnitude the check is `8 * abs(error) <= abs(input)`;
below it, `abs(error) <= 8` units, i.e. half the minimum subnormal step.
The Lean grid is proved by kernel reduction and the Rocq grid by `vm_compute`.
Both also prove that `2^-8` rounds to zero, invalidating an unconditional
`1/8` relative-error claim. The first Rocq attempt used an inapplicable
`discriminate` tactic for the arithmetic negation; `lia` closed the actual
proposition in the passing rerun. No failed attempt is counted as a pass.

## Legacy StandardFloat validity closure

`valid_binary_SF` no longer returns `true` unconditionally. It checks positive
mantissa, canonical exponent, and the upper exponent bound for finite inputs;
zeros, infinities, and the single NaN remain valid. This matches the independent
source-facing predicate for every precision/exponent parameter and every local
constructor, as checked by a closed constructor-case theorem in the fixture.
Positivity compensates for Lean's Nat mantissa versus Rocq's positive carrier.

Two explicitly experimental payload adapters now require actual input validity
instead of mere range bounds. Their existing normalization/rounding assumptions
remain explicit; these adapters are not upgraded into source theorems. A later
addition proof had passed validity using `rfl` at two observer calls. It now
uses the actual validity theorem of `binary_round`, with no new sorry.

## ULP witness construction and choice independence

`Core.Ulp.negligible_exp` now follows `Core/Ulp.v:45` by projecting
`Raux.LPO_Z`, including its nonnegative-first witness construction. The
source bodies of `ulp`, `pred_pos`, `succ` and `pred` were compared at
lines 93, 391, 397 and 403 and retained. Their source anchors and paired
definition-body guards are permanent.

A closed Lean theorem compares against exact private copies of the previous
choice and ULP definitions: every ULP result is preserved under
`ValidRadix` and `Valid_exp`, for every real input, including zero.
The paired invalid identity-exponent example admits witnesses zero and one
with different powers; this rules out assuming unconditional choice
independence. No equality of old/new witness integers is claimed.
The fixed-point caller now reasons through the witness predicate rather
than the old implementation body. No proof debt was added.

The follow-up compared actual exported Rocq types, not merely source section
contexts. Twelve ULP exports have no `Valid_exp` premise:
`succ_opp`, `pred_opp`, `ulp_opp`, `ulp_abs`, `succ_eq_pos`, `ulp_ge_0`,
`pred_eq_pos`, `ulp_le_id`, `ulp_le_abs`, `ulp_canonical`, `ulp_bpow`
and `pred_bpow`. The two `Generic_fmt.generic_format_abs` directions also
have no such premise. Lean now matches that premise boundary, including its
`pred_eq_pos_flocq` compatibility wrapper. The existing proofs remain closed;
the total definition bodies are unchanged. The legacy Hoare presentation and
redundant radix facts in some wrappers remain explicit adaptation details.

Seven further compiled source types omit exponent validity:
`pred_pos_lt_id`, `succ_gt_id`, `pred_lt_id`, `succ_ge_id`, `pred_le_id`,
`succ_0`, and `pred_0` (`Ulp.v:742–803,1550–1559`). The Lean exports now
omit that accidental section instance too, along with five private helpers.
Their proof bodies are unchanged and remain closed. Seven additional paired
clients and compiled-type guards preserve this boundary, including zero.
The nonzero premise on the strict laws remains necessary; the non-strict
laws include zero. This change does not remove validity from representability
or choice-independence theorems that genuinely require it.

`fexp_negligible_exp_eq` at pinned `Ulp.v:76` is purely an integer law:
it needs `Valid_exp`, but no radix. Its unused Lean radix parameter/instance
are removed and all repository callers migrated. Fifteen paired typed
clients and 15 added compiled-type guards protect these reviewed boundaries.

## Pff source-facing signed rounding family

`Source.RND_Max_Pos`, `RND_Min`, `RND_Max` and `RND_EvenClosest` now match
the inspected definition bodies at pinned `Pff/Pff.v:27523`, `27588`,
`27611` and `27641`. Every path uses the explicit integer radix and the
unindexed source record. Upper rounding retains the exact lower record or
uses its **raw** successor. Signed downward/upward wrappers exchange the
positive rules under negation. Nearest-even compares distances and checks
the lower record's mantissa parity; it does not substitute normalized parity
under another radix. The old indexed interfaces remain explicitly local
compatibility APIs, not source exports.

Paired permanent `PffRoundingSource` fixtures close ten equalities in each
assistant. The negative-radix observation retains the repaired logarithm
convention. At bound `(1,0)`, radix two, precision zero, input two, the three
raw results are `(0,2)`, `(1,3)`, `(0,2)`; this is total source behavior
outside normal rounding-correctness premises, not a valid-format guarantee.
Both assistants reject nearest-even replaced by downward rounding at `3/2`
and positively prove the resulting different record. No universal correctness
or normalized-carrier equivalence theorem is added or claimed here.

## Basic unindexed Pff operations

The source facade now exports `Fzero : Int → float`, `is_Fzero : float → Prop`
and `Fmult : float → float → float`. No radix parameter or valid-radix typeclass
is added to these operations. Source anchors: `Pff.v:1151`, `1153`, `1628`.

Actual Rocq `Check @...` output confirms the observer contracts:

| Law | Radix premise |
|---|---|
| `FzeroisReallyZero` | none |
| `is_Fzero_rep1` | none |
| `is_Fzero_rep2` | `1 < radix` |
| `Fmult_correct` | `0 < radix` |

The Lean facade retains exactly these premises; all four proofs are closed.
The paired `PffBasicSourceContracts` clients check the types and explicitly
instantiate multiplication at radix one. A proved radix-zero counterexample
shows why unrestricted multiplication of observed values would be wrong.
Executable observations retain zero's chosen exponent and both product fields.
The bridge's exact oracle checks those fields even on nonpositive radices,
where a value-level theorem may not apply. No existing noncomputable marker
was removed in this slice.

## Independent finite arithmetic laws and selection oracle

### Validity does not imply exponent monotonicity

The paired `ExponentValidityBoundary` fixtures define the same alternating
exponent function in both assistants: even `e` maps to `e-1`, odd `e` to `e-3`.
It satisfies the literal `Valid_exp` conditions at pinned `Generic_fmt.v:38`,
but violates `Monotone_exp` (`Generic_fmt.v:1546`) already at `0 <= 1`.
All powers of two remain representable. Closed Lean and Rocq statements
establish `ulp(1/2) = 1/2` and `ulp(1) = 1/4`, hence a strict decrease.

This independently demonstrates that the `Monotone_exp` premise on pinned
`Ulp.v:333` (`ulp_le_pos`) and `:354` (`ulp_le`) is substantive. The current Lean
types preserve it. The fixture adds no source API or proof debt, and does not
execute classical real operations natively. The six Lean axiom lists contain
only the ordinary `propext`, `Classical.choice`, and `Quot.sound` dependencies.
Rocq's corresponding assumptions are printed rather than silently elided.

### Enumerated arithmetic and rounding

`ExactArithmeticLaws.lean` / `.v` enumerate the 55 finite mathematical values
of the three-bit, maximum-exponent-four format independently of the rounder.
Both assistants check 275 exact-input cases, 1,055 Sterbenz subtraction cases
in all five modes, and 5,714 nearest-addition-error representability cases.
The ratio premise matters: `1 - 1/16` is inexact in this format even though
both operands are representable. The fixtures prove this counterexample.

`RoundingOracle.lean` / `.v` choose a result by enumerating those representable
values, filtering by rounding direction, and minimizing exact integer distance.
Nearest-even parity is taken from the canonical mantissa, not the scaled
integer value. This selection oracle does not use the implementation's shift,
digit-count, exponent-selection, or rounding-decision helpers.

Both assistants execute **35,845** cases: every multiple of `2^-8` between
`-14` and `14`, in all five modes. Lean additionally proves 95 boundary cases
by kernel reduction; Rocq closes its full finite grid with `vm_compute`.
This finite-value oracle excludes overflow, NaNs, infinities, and signed-zero
identity; the separate IEEE bridges cover those observations.

A deliberate mutation forcing nearest-away in the runtime path fails in both
assistants. Lean reports numerator `-3328` (the value `-13`), actual `-14`
versus expected nearest-even `-12`. The first mutation exposed a misleading
diagnostic that recomputed the unmutated observation; the runner now records
the actual and expected values once and reports those same values. This is a
harness mutation witness, not a discovered mismatch in the port's rounder.
