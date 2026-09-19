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

`linter.coqSource` can be enabled in a source-facing Lean module to warn when
a public definition lacks this attribute. It is currently enabled for the six
public definitions in [`BitsSourceFacade.lean`](../src/IEEE754/BitsSourceFacade.lean)
and locally for `valid_binary`. A link proves neither that the Coq name exists
at that line nor that the Lean body is equivalent; those require source review
and paired tests or proofs.

## 4. What the checks establish

`lake build` typechecks the present Lean statements. The paired
`scripts/test_flocq_conformance.sh` builds the pinned Flocq source and checks
small examples on each side; it catches selected counterexamples, not all
inputs. `scripts/check_proof_debts.py` rejects unregistered `sorry` and trust
escapes. Its four registered debts are in `proof_debts.json`: sign-bit
negation, native `frExp`, native next-up, and native next-down. A theorem with
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
