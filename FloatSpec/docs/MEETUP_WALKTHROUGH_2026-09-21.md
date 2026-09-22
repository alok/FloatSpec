# A five-minute FloatSpec walkthrough

This is a proposed explanation for the SF Lean meetup, not a record that Alok
has already presented or personally verified every proof. The implementation
and audit have been heavily AI-assisted. The useful feedback is on the actual
contracts and evidence, not the size of the generated codebase.

## 1. State the problem

“I am continuing a Lean port of Flocq. A proof assistant checks the proposition
we gave it; that is not enough if we accidentally changed the source's intended
proposition. The project needs both valid Lean proofs and faithful contracts.”

The reference is Flocq commit `7aab8f55`. Mathematical reals describe meanings;
integer/bit-based operations supply executable implementations. This is why a
real-valued specification can legitimately be noncomputable while an integer
algorithm should still run.

## 2. Run one actual example

From the repository root:

```sh
lake exe floatspec_demo
```

The [seven-example guide](DEMO_EXEMPLARS.md) explains the printed values and
points to their kernel assertions. Pick one rounding boundary and describe the
input, exact mathematical value, representable neighbors and tie policy. Do
not call a native runtime check a kernel proof.

## 3. Show why assumptions matter

Open [the exponent-boundary example](../../scripts/fixtures/ExponentValidityBoundary.lean).
A valid format can have decreasing ULP: the example deliberately makes the
spacing at one finer than the spacing at one-half. Thus format validity alone
cannot justify monotonic ULP; the theorem needs the monotone-exponent premise.

The trivial order conjuncts in the counterexample are deliberate: they certify
that the proposed monotonicity theorem's input conditions hold. The last
conjunct then contradicts its conclusion. They are not extra assumptions needed
to prove the numerical inequality.

## 4. Use a real source-facing theorem

Open [the nearest-even clients](../../scripts/fixtures/RoundNEPointContracts.lean),
especially `rounded_values_monotone`. The short proof combines the source's
pointwise correctness law with its monotonicity law to show that the actual
rounded-value function is monotone. Keep `Valid_exp` and `Exists_NE`: they are
meaningful source hypotheses, not annoyances to erase during porting.

```sh
lake env lean scripts/fixtures/RoundNEPointContracts.lean
```

Compare the adjacent `.v` fixture, which asks Rocq for the same types. Mutation
tests intentionally delete a required premise or weaken a conclusion and check
that both assistants reject the resulting client.

## 5. State what remains, and ask for feedback

Compilation, kernel validity, finite cross-language agreement and universal
source equivalence are four different claims. Four named native/decoder proof
debts remain. Most of the source inventory is not yet explicitly reviewed;
file coverage and source links are not a completion percentage. Claude's
[independent audit](CLAUDE_AUDIT_2026-09-21.md) examined roughly 150 anchored
declarations at an earlier head, not the entire port.

Useful questions for the room:

- Is there a better way to keep compiled cross-language theorem signatures
  aligned as the port evolves?
- For source-faithful raw records and faster canonical representations, which
  equivalence boundary should the public API expose?
- Which missing source slice would make this most useful to another Lean user?

End with one uncertainty you can explain. A prepared guide or green CI does not
substitute for a personal walkthrough.
