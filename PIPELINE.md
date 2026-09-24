# FloatSpec proof-writing pipeline

Start with the [linear reading guide](FloatSpec/docs/READING_GUIDE.md) if the
representation layers are unfamiliar. The order below separates a correct
definition, a faithful statement, and its proof. A green build alone does not
establish all three.

## 1. Pin the source claim

Find the declaration at the repository's pinned `Deps/flocq` commit. Read its
type, section variables, constructors, and exceptional cases. Record a
`@[flocq_source "src/Module.v" LINE "coq_name"]` reference on a public
source-facing definition where the opt-in linter is enabled. The link is an
index, not proof of equivalence.

## 2. Check the Lean definition first

Keep mathematical definitions pure. Check exact powers of the radix, zero,
negative inputs, NaNs, infinities, and signed zero where relevant. For an
executable boundary, test one nontrivial ordinary input and a separating edge
case on both Coq and Lean. Do not repair a proof of a wrong definition.

## 3. State a direct proposition

Prefer a theorem whose hypotheses and conclusion match Coq. In particular,
retain the source's nonzero, positivity, boundedness, and precision premises.
Use `decide` when comparing a `Bool` result to a decidable proposition:

```lean
def sameSign (x y : Int) : Bool := decide (x < 0 ↔ y < 0)

theorem sameSign_spec (x y : Int) :
    sameSign x y = true ↔ (x < 0 ↔ y < 0) := by
  simp [sameSign]
```

For difficult proofs, a named `sorry` with a concrete strategy in
`FloatSpec/docs/proof_debts.json` is an explicit debt, not a result. CI rejects
unregistered holes and trust escapes.

## 4. Preserve legacy callers deliberately

Older files have many `Std.Do` Hoare triples over pure `Id` values. No product
proof invokes `mvcgen` or `mspec`, and new pure theorems should not gain their
`@[spec]` attribute. When changing an old triple, first prove or state the
direct proposition, then migrate its callers, then remove the triple. Until
that migration, `simp [wp, PostCond.noThrow, pure]` reduces an `Id` triple to
the underlying proposition. Removing all triples at once would break many
downstream proofs without improving the source contract.

## 5. Verify one change at a time

After each definition or theorem change, check the edited module with Lean
diagnostics or `lake build FloatSpec.src.<Module>`. After a caller migration,
run `lake build`; before committing, also run `lake build FloatSpec.Test`,
`lake build FloatSpecTests floatspec`, and the trust gates. Use
`scripts/test_flocq_conformance.sh` when a changed contract has a paired Rocq
observation. Lean and Mathlib are both pinned to stable `v4.34.0`; run
`lake exe cache get` once per checkout so `lake build` compiles only FloatSpec.

For arithmetic proofs, prefer named helper lemmas and `calc` chains over a
large `simp` set. Search nearby theorems and Mathlib before proving a new
fact. Keep the source statement stable while working on its proof unless the
task specifically calls for a contract correction.
