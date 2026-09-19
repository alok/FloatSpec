# Focused source-contract review

This ledger records manual statement/body comparison against Flocq commit
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`. It does not certify all proofs or
all declarations in the named modules. See the
[running audit](ASTRA_AUDIT_2026-09-19.md) for execution receipts and the
[reading guide](READING_GUIDE.md) for the mathematical story.

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
fully typed consumers. Each guard inspects the elaborated type and resolves
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
`IEEE754/BinarySingleNaN.v:113`. Its raw-carrier, root-namespaced namesake
still uses the always-true compatibility predicate: that older theorem
does not establish Flocq validity. The root `binary_fit_aux_correct` also
still has that weaker first conjunct at the point of this inspection.
The latter has an existing stronger private validity lemma available, so
strengthening its source-facing statement is queued after the running
fixed-snapshot suite finishes.

The paired `SingleNaNValidity.lean` / `SingleNaNValidity.v` fixtures check
five finite representations at precision 3 and maximum exponent 4. The
representation `(mantissa=1, exponent=0)` is rejected as noncanonical even
though it denotes the real number one; `(4,-2)` is accepted. Minimum
subnormal and overflow boundaries are checked. Lean's Nat-based raw carrier
also rejects mantissa zero, which Rocq's `positive` field cannot construct.
The Lean fixture consumes the proof-carrying source theorem explicitly.

This is a validity-contract check, not a claim that every historical raw
`B754` or `Binary754` wrapper has been migrated to the source carrier.

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
