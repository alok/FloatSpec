# Focused source-contract review

This ledger records manual statement/body comparison against Flocq commit
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`. It does not certify all proofs or
all declarations in the named modules. See the
[running audit](ASTRA_AUDIT_2026-09-19.md) for execution receipts and the
[reading guide](READING_GUIDE.md) for the mathematical story.

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
must be considered along with displayed theorem statements. The Lean
multiplication specializations prove slightly stronger statements by not
requiring all of the source section's positivity instances. The Lean
`round_round_sqrt_FTZ` also proves its statement for every valid radix,
where the source export takes an unused `4 <= beta` premise. These are
documented generalizations, not discovered counterexamples. No premise was
removed during this review.

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

## Independent finite arithmetic laws and selection oracle

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
