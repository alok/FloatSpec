# Focused source-contract review

This ledger records manual statement/body comparison against Flocq commit
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`. It does not certify all proofs or
all declarations in the named modules. See the
[running audit](ASTRA_AUDIT_2026-09-19.md) for execution receipts and the
[reading guide](READING_GUIDE.md) for the mathematical story.

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
