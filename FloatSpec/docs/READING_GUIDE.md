# FloatSpec, read from start to finish

FloatSpec is a Lean port of [Flocq](https://gitlab.inria.fr/flocq/flocq), a
mathematical library for floating-point formats. Its first job is to describe
which values and operations are valid; its second is to prove statements about
them. A definition can compile while its claimed correspondence to Flocq is
wrong, so these are separate milestones.

## 1. The source and the target

The source for this audit is the Flocq commit
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`, recorded as this
repository's `Deps/flocq` gitlink. `FloatSpec/src` mirrors its `Core`, `Calc`,
`Prop`, `IEEE754`, and `Pff` areas. Each of the 36 Flocq source-module names
has a corresponding Lean file or umbrella module. This says where to look; it
does **not** say that every definition or theorem is equivalent.

The old declaration pairing plan lists 2,548 extracted Flocq declarations.
It paired 2,472 automatically and separately classified the other 76. Its
5,951 comparison jobs include more than one check per source declaration;
only 27 jobs received valid reviewed verdicts in its recorded batch. The
current branch has targeted repairs and tests, but no fresh whole-library
semantic score. Read “not reviewed” as unknown, not as correct or incorrect.

## 2. A floating-point value has more than a real value

A finite value has a sign, significand, and exponent. There are also positive
and negative zero, infinities, and NaNs with payloads. Mapping a value to a
real number forgets several of those distinctions. Therefore a theorem about
`toReal` cannot establish a theorem about all 64 raw bits.

The source-shaped, proof-carrying types are in
[`IEEE754/Binary.lean`](../src/IEEE754/Binary.lean) and
[`IEEE754/BinarySingleNaN.lean`](../src/IEEE754/BinarySingleNaN.lean). Older
`Binary754` compatibility code permits values that the Flocq carrier excludes.
Prefer the source-shaped interfaces when checking correspondence. The
`valid_binary` predicate now checks finite bounds and NaN payload width, but
does not itself turn the permissive carrier into a proof-carrying one.

## 3. Follow one source definition

Start at Flocq's
[`valid_binary`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/IEEE754/Binary.v#L166),
then read the Lean [`valid_binary`](../src/IEEE754/Binary.lean) definition.
The source's finite and NaN constructors explain the Lean branches. The
`@[flocq_source]` attribute stores the pinned path, line, and Coq name. The
adjacent `Source:` URL is clickable in editors that recognize URLs; the path
string inside the attribute is not yet a special go-to-source action.

`linter.coqSource` checks that an opted-in public definition has either a
pinned `@[flocq_source]` reference or an explicit `@[flocq_local "reason"]`
classification. [`Core/Defs.lean`](../src/Core/Defs.lean) is now an entire
strict-gated module: its eleven source-shaped definitions link to pinned
`Defs.v` lines, and its eight public Lean-only helpers state why they have no
direct Coq declaration. The module treats an unclassified definition warning
as a build error. The six public definitions in
[`BitsSourceFacade.lean`](../src/IEEE754/BitsSourceFacade.lean) and
`Binary.valid_binary` are also linked, though those modules do not yet have
whole-file strict coverage. Ordinary `Source:` URL comments beside the
`Defs.lean` attributes can be opened from an editor; the attribute string
itself is not yet a special go-to-source action. The paired conformance command
checks all 26 annotated path/line/name anchors against the pinned Flocq
checkout. A correct anchor does not establish that the Lean type, body, or
proof matches Coq; those require source review and paired tests or proofs.

[`Core/FLX.lean`](../src/Core/FLX.lean) is the second strict-gated module.
Its three source-shaped definitions have pinned links; six public Lean-only
definitions or aliases have explicit reasons. This includes the three
`*_check` definitions, which are arithmetic regressions rather than Flocq
format-membership declarations. [`Core/FTZ.lean`](../src/Core/FTZ.lean) is
the third strict-gated module: three source-shaped definitions link to Flocq,
and four Lean-only checks are classified. [`Core/FLT.lean`](../src/Core/FLT.lean)
is the fourth strict-gated module: `FLT_exp` and `FLT_format` have pinned links;
seven Lean-only checks, payloads, or aliases are classified. Instances and
theorem statements are not covered by these definition-only gates.

## 4. What the checks establish

`lake build` typechecks the present Lean statements. The paired
`scripts/test_flocq_conformance.sh` checks source anchors, builds the pinned
Flocq source, and checks small examples on each side; it catches selected
counterexamples, not all inputs. `scripts/check_proof_debts.py` rejects
unregistered `sorry` and trust
escapes. Its five registered debts are in `proof_debts.json`: sign-bit
negation, native `frExp`, native next-up, native next-down, and the new FTZ
format equivalence. A theorem with
`sorry` is an explicitly unproved claim even when the build passes.

Most current Hoare triples wrap pure `Id` computations. This project does not
invoke `mvcgen` or `mspec`; their lookup annotations, direct tactic imports,
and the Hoare-style linter have been removed. A direct mathematical proposition
is usually easier to compare with Coq. The surviving triples have callers, so
removing them is a gradual interface migration, not a prerequisite for
understanding the source definition.

[`Core/FIX.lean`](../src/Core/FIX.lean) is a concrete completed slice: its
format conversions, ulp, and rounding theorem now state direct propositions;
two IEEE callers were updated accordingly. Its former Boolean checks proved
truncation identities rather than FIX-format membership, so they were removed
and replaced by direct zero-membership and negation-closure facts. Other
modules still contain legacy triples; this one example does not certify them.
Lean's `FIX_format` remains a definition in terms of `generic_format`, whereas
Coq introduces it inductively and then proves equivalence. The direct Lean
conversion theorems are therefore simpler, but that representation choice
still needs source-level review.

The next slice is [`Core/FLX.lean`](../src/Core/FLX.lean). Flocq states
[`FLX_format_generic`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLX.v#L69)
and [`generic_format_FLX`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLX.v#L95)
as implications between mathematical predicates. The Lean theorems now have
that same *shape*, instead of wrapping the predicates in `Id` Hoare triples.
`FLX_format_generic` still needs positive precision, as in the Flocq section;
the reverse theorem does not. This checks the interface, not every detail of
the predicate implementations or proof correspondence.

The same file has a second predicate, `FLXN_format`, which records a
*normal* mantissa for nonzero values. Its two conversions now follow the
source's direct-implication form:
[`generic_format_FLXN`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLX.v#L142)
goes from the normal witness to the generic format, and
[`FLXN_format_generic`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLX.v#L156)
reconstructs the witness under positive precision. Both existing proofs
typecheck; this still does not establish a theorem-by-theorem equivalence
audit of all of `FLX.lean`.

The FTZ format shows why the distinction matters. Pinned Flocq
[`FTZ_format`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FTZ.v#L36)
requires a float witness with a normalized mantissa and a minimum exponent.
The old Lean definition was simply `generic_format` at `FTZ_exp`, which made
its two conversion theorems reflexive and hid those representation conditions.
Lean now states the source-shaped witness contract; the conversion theorems
have direct implication types. Their common equivalence proof is a named
`sorry` in [`proof_debts.json`](proof_debts.json). The explicit zero-witness
regression is proved without that debt. The downstream double-rounding
theorems still typecheck by using the conversion, but therefore inherit the
unproved equivalence until the proof is supplied. The direct projection
`FLXN_format_FTZ` is proved from the structural witness without that debt.

For gradual underflow, [`Core/FLT.lean`](../src/Core/FLT.lean) keeps an explicit
bounded-mantissa, minimum-exponent witness, matching pinned Flocq
[`FLT_format`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLT.v#L36).
Its two source-named conversions now state direct implications. The
format-to-generic direction needs no positive-precision assumption, matching
the source proof's discharge of that section context; the reverse direction
retains positive precision. Both existing Lean proofs and downstream callers
typecheck without adding a proof debt. This is a reviewed contract slice, not
a whole-file theorem-equivalence verdict.

On this Mac, the checked-in Lean `v4.34.0` toolchain makes plain `lake build`
work. Mathlib and CSLib remain at the reviewed rc2 source pins; a future
dependency upgrade is separate work from fixing the local compiler crash.

## 5. Where to go next

Read the [focused audit](FLOCQ_CONFORMANCE_AUDIT_2026-09-18.md) for concrete
mistakes found, paired observations, and boundaries. Then take one
`@[flocq_source]` definition at a time: compare the Coq and Lean type, inspect
each constructor or branch, test a boundary case on both sides, and only then
judge its proof. That sequence is the remaining work more accurately than a
single percent-complete number.
