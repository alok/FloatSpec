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

## Wake-up summary — September 21, 2026

For tonight's SF Lean meetup, use the
[short walkthrough](MEETUP_WALKTHROUGH_2026-09-21.md). Claude has independently
cross-checked an earlier production head: read the
[audit and point-by-point response](CLAUDE_AUDIT_RESPONSE_2026-09-21.md), keeping
the review scope separate from later changes and current CI results.

CI now installs Rocq and builds pinned Flocq as well as Lean. Required live
tests cannot silently skip a missing reference. The initial hosted run passed
the 174 live tests but timed out in an oversized differential grid; the bounded
follow-up is locally verified and still needs its own hosted result. The
required suite has since grown to all 24 reference-gated modules (238 tests),
CI now compiles every Lean and Rocq fixture by glob, and it replays every
source, test and fixture declaration through the kernel; these changes, too,
need their own hosted result. See
[the three-loop guide](THREE_VERIFICATION_LOOPS.md) for exact coverage and artifacts.

**The port builds and runs on macOS with Lean 4.34.0, but is not yet a fully
source-audited port.** All 35 built Flocq module names have Lean counterparts.
That is file coverage, not a percentage of faithful definitions or theorems.
No named native/decoder proof obligations remain; the unreviewed source
surface is a separate and larger issue.

The continuation is now on `main` in `~/floatspec` (the same directory as
`~/FloatSpec` on this Mac), pushed to
[your fork](https://github.com/alok/FloatSpec/tree/main).
It includes Hantao's upstream work, the audited continuation, and Claude's
three comparison commits in its ancestry. Your fork is the default remote;
BAIF remains `upstream`. Your modified `Deps/flocq` is untouched.

For code understanding, run `lake exe floatspec_demo`, then read sections
1–6 below. Use the [exemplar guide](DEMO_EXEMPLARS.md) for smaller examples.
For a visual companion, the separately published
[Flocq Atlas](https://flocq-atlas.aloksingh.chatgpt.site) offers dependency
navigation and side-by-side source. It is a static snapshot (currently based
on Lean commit `ae042adf`), not a live verification result; use this repository's
review ledger for the latest explicit review state.

The important recent changes are:

- **The public rounding-predicate interface is now filled in.** Across two
  slices, 53 Flocq laws gained direct Lean exports, and six misleadingly
  source-named Hoare exports now return the actual mathematical propositions.
  The old proofs were mostly present but hidden behind noncomputable Boolean
  checks; this repair makes the source API usable without that detour. Start at
  [the direct rounding laws](../src/Core/Round_pred.lean), then read
  [the paired contract examples](../../scripts/fixtures/RoundPredSourceContracts.lean).
  Then read [tie policies and totality](../../scripts/fixtures/RoundPredTieContracts.lean).
  Both assistants prove why nearest rounding needs strict input order without
  a tie rule, and why truncation monotonicity and the two zero-directed tie
  policies need zero in the format. All 78 top-level source contracts in this
  module now have paired typed clients and explicit reviews; its constructor
  and four generated eliminators are accounted for separately. There are
  122 total review dispositions, including the three nearest-even laws below.
  This does not certify unreviewed imports or
  the other modules, nor identify Rocq and Lean proof terms.

- **A systematic source-order queue.** [Read the dependency-ordered queue](SOURCE_REVIEW_QUEUE.md)
  from the top. It uses actual module dependencies, then compiled declaration
  positions inside each source file. There are 2,716 declaration sites across
  35 modules, including aliases and generated proof infrastructure—not 2,716
  missing APIs. Existing Lean names are only candidates. The first 36 sites
  have explicit review dispositions, through Zaux's division/remainder laws;
  `iter_pos` now uses Flocq's binary-positive recursion, with a closed proof
  preserving its previous semantics. The next entry is `Zsame_sign_trans`.
  Fifty-four unused check/spec wrappers have been removed from this reviewed
  slice, leaving the actual direct propositions and proofs. Negative integer
  powers return zero, not reciprocals: the tests explain why that matters.
  Division tests also distinguish floor, truncating and Euclidean operations:
  default Lean `/` is not a universal translation of Rocq `Z.div`.

- **Contracts that mention the actual rounding policy.** Eight ULP exports
  accepted a tie policy but referred to a fixed-policy result. One two-policy
  equality was merely reflexivity. Those statements now preserve the policies,
  with paired Lean/Rocq clients and mutation controls. `round_NE_pt` now states
  correctness of the actual rounded value directly, with both Pff callers migrated.
  Nearest-even totality and monotonicity now also have direct source-facing
  propositions, retaining the format-validity and parity conditions. The combined
  law supplies both properties, not merely existence of some rounded result.
  [This short composed example](../../scripts/fixtures/RoundNEPointContracts.lean)
  derives monotonicity of the actual rounded-value function from those APIs.
- **The correct hypotheses.** Recent repairs removed 27 unnecessary
  exponent-validity assumptions, while a paired counterexample shows that
  exponent monotonicity really is needed for a different ULP law.
  The remainder audit preserves a different genuine premise: tiny quotients
  must round to zero. With two-bit precision, rounding `1/8` upward gives
  remainder `1 - 8 = -7`, which is not representable. Both assistants prove
  this counterexample; an exhaustive small-format bridge tests its boundary.
  A second paired proof shows monotone exponents are needed even for truncation:
  the alternating-precision format represents `1.75` and `1`, but not their
  remainder `0.75`.
- **Independent expected answers.** IEEE bridges now check exact rational/grid
  expectations, including infinities, zero divisors, signed zero, negative
  square roots and source NaN-payload priority. Deliberately shared wrong
  programs are rejected even when their prover outputs agree.
- **Preserving Claude's useful work without preserving a wrong source claim.**
  The exponent-alignment backend compares arbitrary dyadic values. It is
  now opt-in, with twelve `*_eq_value` contracts and twelve closed bridges to
  raw comparison on canonical inputs. The raw API remains the default import.
  `PrimitiveFloat` already carries the needed validity proof; arbitrary raw
  records do not. See the [worked comparison guide](COMPUTABLE_COMPARE_GUIDE.md).
- **Restoring the unindexed Pff interface.** The latest addition supplies `Fzero`,
  `is_Fzero`, `Fmult` and four source-shaped laws. Multiplication correctness
  accepts radix one; zero's forward observer laws need no radix restriction.
  The new bridge observes complete records, not only real values.
  Four further closed laws now cover negation, double negation, absolute-value
  interpretation and nonzero preservation. Negation is unrestricted; absolute
  value needs a positive radix, as a paired negative-radix counterexample shows.
  The missing addition/subtraction observer laws are now also proved with the
  exact positive-radix premise, including radix one. Paired radix-zero
  counterexamples explain why dropping that premise is invalid.

Current verification is deliberately separated by source snapshot:

| Snapshot | Completed evidence |
|---|---|
| Nearest-even totality/monotonicity API, `cd22873c` | Full 6,225-job macOS Lean 4.34 build; seven paired source clients, a composed monotonicity example in both assistants, and eight rejected contract mutations. Compiled trust: 13,778 declarations / 59 modules / four unchanged debts; 456 anchors and 122 explicit reviews. Numerical definitions unchanged; fresh runtime bridge receipts belong to the preceding snapshots below, not this theorem-only follow-up. |
| Complete rounding-predicate interface, `8aa8e9e3` | Full 6,225-job macOS Lean 4.34 build; remaining 34 direct laws and all other public source contracts checked against pinned Rocq. Paired tie-uniqueness counterexamples and 20 rejected contract mutations across both fixtures. Fresh 3,260 three-way cases and kernel equalities (140 rounding decisions, 3,120 nearby-integer cases), seed 865307. Compiled trust: 13,774 declarations / 59 modules / four unchanged debts; 453 anchors. Numerical bodies unchanged; source-module interfaces reviewed, not a universal cross-system certificate. |
| Direct rounding-predicate API, `8b16a912` | Full 6,225-job macOS Lean 4.34 build; 25 direct contracts checked against pinned Rocq; three paired counterexamples and eight rejected premise mutations. Fresh 3,539 three-way rounding cases and kernel equalities (279 rounding decisions, 3,260 nearby-integer cases), seed 865103. Compiled trust: 13,720 declarations / 59 modules / four unchanged debts; 402 anchors. This is an API repair; numerical operation bodies are unchanged. |
| Zaux division/remainder review, `949e91ee` | Full 6,225-job macOS build; 13,695 compiled source declarations / 59 modules, four debts, 377 anchors. Eight more source contracts and six rejected mutations; 1,377 signed-input triples in each assistant. Fresh 811 floor-division cases/kernel equalities (seed 864503), including 33 zero and 386 negative divisors; saved outputs also checked against an independent Python floor oracle. The mathematical theorems remain unchanged. |
| Zaux parity/power/radix review, `f2fb5d00` | Full 6,225-job macOS build; 13,713 compiled source declarations / 59 modules, four debts, 369 anchors. Twenty more source sites dispositioned with paired exact clients, including the Boolean/proposition radix bridge. Eight contract mutations rejected; 228 three-way cases and generated kernel equalities, seed 864307. Two live runner mutations detected; numerical bodies unchanged. |
| Source-ordered Zaux prelude, `55f57d90` | Full 6,225-job build; 13,753 compiled source declarations / 59 modules, four debts, 351 anchors. First eight source sites dispositioned; direct-declaration review drift checks. Paired exact contracts; 1,244 three-way cases/kernel equalities with an independent closed-form oracle, seed 864211; two shared-program mutations detected. |
| Canonical comparison bridge, `7c2c0450` | Full 6,225-job build; 13,743 compiled source declarations / 59 modules, four existing debts and 344 source anchors. Twelve closed canonical/raw bridge theorems, 3,364 canonical pairs and the existing 20,000 dyadic pairs. Fresh 1,345 three-way cases/kernel equalities (26 observed fields each), seed 864101, and 24 detected output mutations. |
| Executable Pff integers/divisibility, `b2e86f63` | Four marker-only changes and constructive `maxDiv`; a universal Lean equality proof against its old classical definition. Paired standalone fixtures and 4,096 native positive-division checks. Fresh 2,172 three-way cases/kernel equalities and 6,198 independent assertions, seed 863307; eight harness tests including five shared-program mutations. |
| Pff addition/subtraction contracts, `1fb9f135` | Full 6,226-job build; closed proofs with paired exact source types and radix-zero counterexamples; eight live contract mutations. Fresh 72-input three-way replay/kernel equalities and 1,272 independent assertions, seed 863101. Numerical bodies unchanged. |
| Current Pff sign laws, `d0ab66b2` | Full 6,226-job build; 13,687 compiled source declarations / 59 modules; four manifest-only debts; 336 validated source anchors. Four paired source laws and four live mutations; fresh 72-input three-way replay with generated kernel equalities, seed 862619. Only four closed theorem exports were added to the previous production snapshot; operation bodies are unchanged. |
| Remainder audit, `3c5a913d` | Full build; 12,100 three-way cases/kernel equalities and 84,182 independent assertions, seed 862513. Eight contract controls plus six bridge tests pass; eleven paired exponent-boundary propositions plus the zigzag exponent definition explain the necessary hypotheses. Final standalone sweep re-executed 14 Lean modules, 26 Lean fixtures, 38 Rocq fixtures and all seven demo examples on this snapshot. |
| Direct nearest-even API, `b9b5abb6` | Full build; four paired typed exports and four live mutation controls. Arithmetic bodies are unchanged from the Pff snapshot below. |
| Pff addition, `21a75295` | Full build; paired basic Pff clients; all 20 expanded Pff harness tests. Fresh bridge: 3,072 cases/kernel equalities and 65,846 independent assertions, seed 862307. |
| Integrated comparison API, `4b714ddb` | Full build and seven demos; 20,000 executable dyadic pairs; 24 paired raw-comparison fixture cases; 1,237 fresh raw-comparison bridge cases and kernel equalities, seed 862149. |
| Pre-integration IEEE snapshot, `687aa7a8` | 1,104 native plus 470 all-mode cases, all 1,574 generated kernel equalities, and 111,282 independent expected-field checks; seeds 862081 and 862073. |
| Frozen full aggregate, `5d241916` | Complete three-loop run: 60,639 differential executions/kernel equalities across thirteen reports, and 168 harness tests. Its older IEEE profiles predate the expanded independent exceptional oracle. |
| Earlier broad snapshot, `32ec11b5` | Complete three-loop run: 55,162 differential executions/kernel equalities and 119 bridge-harness tests. |

The frozen `5d241916` aggregate completed successfully at 21:43 UTC; it is
not an execution of current main. Historical stress groups, exact fingerprints, seeds, failures and
replay artifacts are retained in the [verification receipt](VERIFICATION_RECEIPT_2026-09-20.json)
and [audit ledger](ASTRA_AUDIT_2026-09-19.md); these snapshots are not interchangeable.

**About `noncomputable`:** arbitrary-real specifications and executable
integer algorithms are different layers in both provers. Some legacy integer
helpers are unnecessarily marked, which is a real execution-capability gap.
The September 20 probe found `Zquotient (-7) 3` returned −2 in Rocq and under
Lean's `#reduce`, while Lean's `#eval` rejected its marker. That specific gap
is now fixed: `Zquotient`, `Pdiv`, `oZ` and `oZ1` execute with their source
types. `Pdiv`, `Zquotient` and `ZdividesP` now transcribe the Coq bodies, and
`#eval` and `lean --run` run those transcriptions; closed theorems equate the first two
with natural division and `Int.tdiv`. `maxDiv` now decides divisibility with
`ZdividesP` instead of `Classical.propDecidable`, with a universal Lean proof
that its answer is unchanged. `#print axioms maxDiv` lists `Classical.choice`
only through erased proofs; the decision executes. Arbitrary-real
specifications remain as
they were. Read
[the explanation and concrete probes](COMPUTABLE_COMPARE_GUIDE.md#5-what-noncomputable-does-and-what-it-does-not-do).
The original explanatory answer was read-only; these are subsequent tested fixes.

**The CI repair has a complete green hosted Linux run on Lean 4.34.0.**
[Run 35553327541](https://github.com/alok/FloatSpec/actions/runs/35553327541)
at `ca7eb4f7` passed the build, standalone regressions, trust checks, generated
status and source hygiene on September 21 at 02:37 UTC. The original binary-
cache incompatibility and subsequent missing-ripgrep failure are both resolved.
Search/tool failures now fail explicitly; five injected-failure tests cover
those paths. The reviewed rc2 dependency sources remain pinned under stable
Lean 4.34.0. Hosted CI runs Lean and non-live harness tests; the live pinned-Rocq
and differential receipts above are separate local verification.

The power/division audit commits (`a0fd6e45`, `aeae41fa`) and documentation
head `20abab5e` now also have their own successful hosted runs, verified on
September 21 at 17:37 UTC. The [current-base run 35554897660](https://github.com/alok/FloatSpec/actions/runs/35554897660)
is green. The first rounding-interface slice `60096e0c` also passed its full
[hosted run 35635101867](https://github.com/alok/FloatSpec/actions/runs/35635101867),
observed on September 21 at 18:26 UTC. Later slices still need their own hosted
results; do not transfer an older green run to a newer revision. The
[continuation plan](FIXUP_PLAN_2026-09-21.md) keeps that boundary explicit.

For the remaining fidelity work, read [SOURCE_FIDELITY_GAPS.md](SOURCE_FIDELITY_GAPS.md).
Finite agreement, closed proofs, source links and correct source correspondence
are distinct claims.

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

Input domains matter before decoding too. Flocq accepts arbitrary integers;
Lean's UInt32/UInt64 wrappers first reduce modulo the word size. At `2^32 + 1`,
the source decoder sees its sign threshold exceeded and returns the negative
minimum subnormal; wrapping first leaves the word one, the positive minimum
subnormal. Neither is a bug in that interface. The paired
[model-adapter examples](../Test/NativeModelAdapters.lean) also separate signed
zero, raw NaN payloads and the logical model's deliberate NaN canonicalization.
The first test oracle had wrongly assumed every route wrapped; cross-testing
both assistants exposed the oracle mistake.

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

The same distinction applies to classical existence. `LPO_min`, `LPO` and
`LPO_Z` return either a witness with its membership proof or a proof that no
witness exists. The integer constructor searches the nonnegative side before
the negated-natural side. These are classical constructions, not programs
that decide arbitrary predicates. The old optional choices remain explicit
compatibility helpers. [Paired typed clients](../Test/LpoSourceContracts.lean)
check the return shapes, a negative-only predicate and an empty predicate.

For a concrete executable Pff example, run
`lake env lean --run scripts/fixtures/PffWalkthrough.lean`. Pff's source-facing
neighbors use one explicit integer radix and an unindexed mantissa/exponent
record. With base three, the normalized successor of one is `(4,-1)`, or four
thirds. The old wrapper indexed by base two gives `(3,-1)` even if its extra
argument says three, because that argument is ignored. Both interfaces are
now separately classified. The real-valued Pff rounders remain mathematical:
at base three and the demonstrated bound, `1.5` rounds down to one, up to two,
and nearest-even to two; `-1.5` rounds down to minus two, up to minus one,
and nearest-even to minus two. The paired
[rounding fixtures](../Test/PffRoundingSource.lean) prove these exact records.

Even a total logarithm convention matters outside normal radix assumptions.
Rocq uses `ln x = 0` for `x ≤ 0`; Lean's `Real.log` uses the absolute value
there. The repaired Pff formula follows Rocq, and a closed theorem preserves
every result at positive radix. A negative-radix counterexample distinguishes
records that denote the same real number. Equality of represented reals alone
would have hidden that source mismatch.

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

At zero, ULP is selected through a negligible-exponent witness. The repaired
definition follows Flocq's `LPO_Z` construction, rather than choosing an
arbitrary integer directly. Does changing a witness change the spacing? For
**valid** exponent functions, no: a closed Lean theorem proves the entire ULP
function unchanged, including zero. Without validity, two admissible witnesses
can yield different powers: the identity exponent function admits both zero
and one, producing binary spacings one and two. The
[ULP choice fixture](../Test/UlpSourceChoice.lean) proves the preservation law,
the invalidity of that example, and the differing powers. This is why witness
construction and choice independence are reviewed separately.

That does **not** mean every ULP law needs exponent validity. Negation and
absolute value preserve the magnitude used by ULP; their symmetry laws work
for any exponent function. So do the reviewed positive-branch, positivity,
canonical-value and radix-power formulas under their stated value premises.
Fourteen source laws had inherited unnecessary validity assumptions, and the
pure integer witness-equality lemma even required an irrelevant radix.
Those assumptions are now removed, with 15 paired typed clients and compiler
guards. The stronger witness-independence proof above retains validity.

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

No explicit proof debts remain in `proof_debts.json`. `Binary64.ofBits_flipSign`
proves, for every `UInt64`, that XOR with the sign mask decodes to `Bopp` of
the decoded value. Native next-up and next-down (`nativeNextUp_equiv`,
`nativeNextDown_equiv` in `PrimFloat.lean`) are proved against `Bsucc` and
`Bpred` for every primitive float. The former native `frExp` debt named Lean's
`@[extern]` `opaque` `Float.frExp`, which the kernel cannot evaluate. It is now
the closed theorem `nativeFrExp_equiv`, proved for a bit-level `nativeFrExp`.
Agreement between that function and the runtime `Float.frExp` is checked by
execution in `scripts/fixtures/NativeFrexpAgreement.lean`, not trusted by the
kernel. All four use only the standard axioms.
A theorem using `sorry` remains unproved even if its statement compiles.
The lexical debt gate and compiler-level dependency audit keep the manifest
honest: any new hole must be named there, and no source declaration may
silently depend on one. Neither gate judges whether every mathematical statement is right.

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

The core bridge now runs each input on Lean's IR interpreter (`lean --run`,
lean-ir), on Lean's elaborator reducer (`#reduce`, lean-meta) and on Rocq's
`vm_compute`. Neither Lean path is the kernel or native code; the kernel checks
the generated `decide +kernel` equalities described below (lean-kernel). See
[execution path names](THREE_VERIFICATION_LOOPS.md#execution-path-names). It includes ordinary inputs and explicitly labeled inputs
outside theorem preconditions, such as negative shifts or zero divisors.
Agreement on those inputs is a total-function observation, not permission
to apply a theorem without its hypotheses.

Native binary64 bridges also execute real runtime `Float` operations.
They compare unary operations and nearest-even arithmetic with both the
Lean logical model and Rocq. Signed zero is retained. NaNs are deliberately
canonicalized in these native comparisons. Native `frExp` agreement has a
nonzero-finite precondition; exceptional exponent observations are retained
and reported separately. The proved `nativeFrExp_equiv` covers the bit-level
`nativeFrExp`. Its link to the opaque runtime `Float.frExp` is the separate
runtime agreement fixture.

A separate IEEE source-API bridge covers binary32/binary64 in all five
rounding modes, including fused multiply-add and exact NaN payloads.
That bridge checks integer-only Lean on lean-ir and lean-meta, and Rocq,
not native hardware directed rounding. Enabling the lean-ir path required
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
These are the IEEE integer algorithms; `Core.Ulp.ulp` on arbitrary real
numbers is still a noncomputable mathematical definition.

Rocq's output becomes the expected value of generated Lean equality
statements, and Lean checks each with `decide +kernel`. The core bridge does
this for every case whose `#reduce` row agrees with Rocq's; the IEEE mode,
scale, integer and native bridges still do it only for batches that agree
throughout.
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
Fourteen source files enable strict public-definition classification; a targeted
section of `Binary.lean` additionally enables the same check.
The compiler-backed validator checks all 319 registered anchors, including
combined attributes and later attribute commands. These links are metadata,
not a proof that bodies or theorem signatures correspond.

Adjacent `Source:` URLs can be opened by editors that recognize URLs.
The attribute's path string itself does not yet have a special click action;
that remains low-priority editor integration.

The useful next step is always concrete: select one source declaration,
compare its type and branches, run a boundary case through both systems,
check its hypotheses, and then inspect its proof. That is the unit of
progress the audit is tracking.
