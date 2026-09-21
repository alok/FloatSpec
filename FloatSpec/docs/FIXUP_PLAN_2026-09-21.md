# Fixup execution plan

Resume on the user's ordinary main checkout after explicit approval to repair
CI using stable Lean 4.34.0. Preserve the pinned dependency source revisions,
the user's modified Deps/flocq, and Hantao/Claude ancestry. Finite agreement,
Lean theorem validity, and source equivalence remain separate claims.

## Scope

- In: hosted build recovery, two missing unindexed Pff observer contracts,
  native execution of clearly integer-only helpers, targeted three-loop tests,
  reproducible receipts, and the linear reading guide.
- Out: replacing mathematical reals by machine floats, changing the source pin,
  claiming whole-library equivalence, or hiding native proof obligations.

## Ordered work

1. Awaiting hosted result — repair CI on stable 4.34.0. Disable only the incompatible
   Mathlib binary cache; build all targets inside lean-action so its compatible
   GitHub cache saves completed artifacts. Preserve trust/hygiene gates and
   execute the recent standalone contract fixtures. Validate workflow syntax,
   push, inspect the real hosted build, and fix any subsequent failures.
   Pushed as `40a336d7`; local 6226-job build, actionlint and YAML assertions pass.
   GitHub run `35548504304` passed the Linux build and standalone regressions,
   saved a compatible cache, then failed on missing ripgrep in the trust scan.
   Install ripgrep explicitly and reject search/tool errors (five new injected
   failure tests pass). Full hosted success remains pending the follow-up run.
2. Complete — add source-shaped `Pff.Source.Fplus_correct` and `Fminus_correct`.
   Confirm compiled Rocq types, retain positive radix including one, check
   caller compatibility, and test zero/negative-radix exclusions explicitly.
   Both closed proofs, paired typed clients/counterexamples, eight live mutations,
   full build and the 72-case replay (seed 863101) pass. No numerical body changed.
3. Complete — enable native execution for selected integer-only definitions.
   Start with `Zquotient`, `Pdiv`, `oZ`, and `oZ1`; preserve their existing
   bodies/types where possible. Treat classical divisibility in `maxDiv` as
   a separate decision-procedure issue, not an annotation-only fix.
   The user then explicitly encouraged bolder fixes. The selected extension is
   constructive `maxDiv` using the existing source-shaped `ZdividesP`, with a
   closed equality proof against the old classical definition and cross-tests
   at negative/zero/one radices as well as ordinary radices.
4. Complete — execute each changed slice in Lean and pinned Rocq, compare the
   actual exported operations with replayable inputs, bootstrap Lean kernel
   equalities, and reject deliberately wrong implementations with mutations.
   Do not edit/build imported sources during a frozen bridge run.
   Seed 863307 passes 2172 cases and kernel equalities with 6198 independent
   assertions; eight harness tests include five live shared-program mutations.
   The initial ungrouped run was deliberately interrupted and remains an error.
5. Complete locally — full macOS build (6226 jobs), compiled trust (13692 source
   declarations / 59 modules / four debts), 344 pinned anchors and generated
   status checks pass. Hosted status is still pending as recorded in step 1.
6. Complete — update the reading guide, fidelity ledger and Linear CFS-3; commit
   only verified coherent slices, write the repository's post-commit logs, and
   push to the user's origin/main.
   Pushed as `c3972539`; post-commit log recorded.
7. Complete — use source dependency and declaration order for the audit.
   Build a reproducible queue from pinned `coqdep` and compiled declaration
   metadata; distinguish an existing candidate from a reviewed contract.
   Make raw comparison the default import, retain the dyadic helper only as an
   explicit opt-in with closed canonical bridges, and run the boundary cases.
   Prefer compiler-backed execution checks to a keyword ban on `classical`:
   proof-only classical reasoning and mathematical-real specifications are
   legitimate; executable integer algorithms must actually compile and run.
   The generated queue covers 2716 declaration sites / 35 modules. Its first
   eight sites are dispositioned; source-shaped binary-positive iteration
   preserves its old semantics by a closed proof. The 1244-case prelude bridge,
   exact contracts, shared-program mutants, full build and trust gates pass.
8. **In progress — continue the source-ordered Zaux audit.**
   The next twenty sites, `Zeven_ex` through `Zpower_gt_id`, are now reviewed.
   Paired typed clients and eight contract mutations pass; 228 three-way power
   cases/kernel equalities, full build, trust and source anchors pass. Thirty-eight
   unused check/spec wrappers are removed without changing the mathematical
   propositions or numerical bodies. Next: `Zmod_mod_mult` and division/remainder,
   while checking the real hosted CI result (follow-up run `35553327541`).
   Do not turn candidate-name counts into equivalence claims. Publish coherent
   verified slices and keep the linear reading guide current.

## Constraints and open obligations

No new deadline was specified for this continuation. Difficult proofs may be
deferred only as named manifest debts, as requested; do not weaken contracts
to obtain a green build. The existing four native/decoder obligations and the
broad unreviewed source surface remain open independently of this fixup plan.
Screenpipe memory lookup was attempted on resume but its backend was stopped;
live repository state and checked-in ledgers provide the current context.
