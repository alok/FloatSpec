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

1. Complete — repair CI on stable 4.34.0. Disable only the incompatible
   Mathlib binary cache; build all targets inside lean-action so its compatible
   GitHub cache saves completed artifacts. Preserve trust/hygiene gates and
   execute the recent standalone contract fixtures. Validate workflow syntax,
   push, inspect the real hosted build, and fix any subsequent failures.
   Pushed as `40a336d7`; local 6226-job build, actionlint and YAML assertions pass.
   GitHub run `35548504304` passed the Linux build and standalone regressions,
   saved a compatible cache, then failed on missing ripgrep in the trust scan.
   Install ripgrep explicitly and reject search/tool errors (five new injected
   failure tests pass). Follow-up run `35553327541` at `ca7eb4f7` is fully green:
   build, regressions, trust, generated status and hygiene passed at 02:37 UTC.
   Later source-audit commits have their own still-pending hosted runs.
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
   status checks pass. The CI-repair revision now also passes hosted checks;
   later audit revisions are recorded separately in step 1.
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
8. Queued — continue the source-ordered Zaux audit.
   The next twenty sites, `Zeven_ex` through `Zpower_gt_id`, are now reviewed.
   Paired typed clients and eight contract mutations pass; 228 three-way power
   cases/kernel equalities, full build, trust and source anchors pass. Thirty-eight
   unused check/spec wrappers are removed without changing the mathematical
   propositions or numerical bodies. A further eight division/remainder contracts
   now pass exact typed clients, six mutants, paired 1377-input grids and an
   811-case differential/kernel replay (seed 864503). Sixteen more unused wrappers
   are removed; floor/truncating/Euclidean domains are explicit. The queue has
   36 dispositions. Next: `Zsame_sign_trans`; inspect the latest audit revisions'
   hosted checks separately from the now-green CI-repair revision.
   Do not turn candidate-name counts into equivalence claims. Publish coherent
   verified slices and keep the linear reading guide current.
9. Complete locally — directed and basic nearest source-facing APIs in Round_pred.
   The user explicitly reaffirmed that finishing the port is the main goal.
   Prioritize usable Flocq contracts over further wrapper cleanup or review
   counts. Restore the direct directed-rounding laws currently available only
   through Boolean/Hoare encodings, preserving the exact source hypotheses.
   Then fill the nearest-rounding interface. Check paired exact clients and
   genuine boundary counterexamples in Lean and Rocq, build all targets,
   retain source links, update the reading guide, and push verified slices.
   Latest hosted runs for `a0fd6e45`, `aeae41fa`, and `20abab5e` are now green.
   Twenty direct exports added, five Hoare-returning source names repaired;
   25 paired exact clients, three paired counterexamples, eight rejected
   mutations, full 6225-job build and 3539 differential/kernel cases pass.
   Snapshot `8b16a912`, seed 865103. No new debt; four existing debts remain.
10. Complete locally — finish the remaining Round_pred source interface.
    Nearest sign/absolute-value laws, generic tie uniqueness, ties away/toward
    zero, format equivalence and totality must expose the actual source
    propositions. Preserve exact premises; reuse closed proofs where faithful,
    and test changed interfaces in both assistants before pushing each slice.
    The remaining 34 direct laws and all other public contracts pass paired
    clients; 20 contract mutants, full 6225-job build and 3260 three-way/kernel
    cases pass (seed 865307, snapshot `8aa8e9e3`). All 83 module source sites
    have explicit dispositions, including four adapted generated eliminators.
    Four existing debts remain unchanged; no arithmetic body changed.
11. Complete locally — nearest-even totality and monotonicity source contracts.
    The complete Round_pred interface is pushed as `a3a84b81`. Inspecting its
    underlying Defs bodies found no discrepancy in the rounding predicates;
    that inspection alone does not reclassify the full foundation as reviewed.
    The next concrete API gap is Round_NE's totality, monotonicity and combined
    rounding contract. Replace those three source-named Hoare interfaces with
    direct propositions, retain the exact Valid_exp/Exists_NE premises, migrate
    callers and check paired clients/mutations and the full build before push.
    Transitive source equivalence remains a separate open task.
    All three direct contracts and their callers pass complete LSP diagnostics;
    seven paired source clients, a composed rounded-value monotonicity example,
    eight live mutations and the final 6225-job macOS build pass. Source snapshot
    `cd22873c`; 13778 compiled declarations / 59 modules / four unchanged debts.
    The first rounding slice's hosted run `35635101867` is fully green.
12. Queued — continue substantive source-API completion. The next
    bounded target is the remaining nearest-even definition/parity layer and
    its source aliases, then the next dependency-ordered contract gap. Keep
    actual missing APIs separate from generated names, retain exact premises,
    publish verified slices on main and track each revision's own CI result.
13. **In progress — respond to Claude's cross-check and require hosted Rocq.**
    Preserve the original independent audit, distinguish accepted findings from
    scope clarifications, fix review-fingerprint regression coverage and missing
    submodule metadata, and label stale documentation. Install Rocq and build
    pinned Flocq in CI; missing prerequisites or skipped live tests must fail.
    Execute the same workflow locally, persist differential evidence in hosted
    artifacts, then push and inspect the real run. Update the reading guide and
    CFS-3 for tonight's meetup without marking a presentation as delivered.
    Setup was pushed in `b501cb14`. Its hosted run installed Rocq, built the pin
    and passed all 174 required live tests with zero skips, then timed out in
    the 35,594-case grid. The follow-up keeps the full suite but bounds the
    per-push bridge to 4,309 core cases plus 292 saved IEEE counterexamples;
    both complete locally with kernel checks. A fresh 6225-job macOS build and
    compiled test-scope audit (311 declarations / 35 modules / zero debt) pass.
    Source scope still has four registered debts. Follow-up hosted confirmation
    remains open. Keep the family-facing Linear update brief and link details.

## Constraints and open obligations

No new deadline was specified for this continuation. Difficult proofs may be
deferred only as named manifest debts, as requested; do not weaken contracts
to obtain a green build. The existing four native/decoder obligations and the
broad unreviewed source surface remain open independently of this fixup plan.
Screenpipe memory lookup was attempted on resume but its backend was stopped;
live repository state and checked-in ledgers provide the current context.
