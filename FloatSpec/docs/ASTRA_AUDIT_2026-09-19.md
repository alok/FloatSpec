# Independent continuation audit — 19 September 2026

This is a running evidence record, not a declaration that the port is correct.
Read [the linear guide](READING_GUIDE.md) first for the mathematical structure.

## Baselines and preservation

The review starts from `d4c44d9b3ae217211bff53fc4f06da3d91424e60`, on a new
`codex/astra-flocq-audit` branch. It includes the 23 Codex commits from upstream
`158263e983ec3925e02b10f5b312498bf414e0f1` through `10bd939f`, plus Claude's
subsequent FTZ equivalence proof. Upstream `main` was checked live and still
pointed to that baseline. The modified nested `Deps/flocq` checkout is preserved.

The reference is the parent repository's Flocq gitlink,
`7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`, not the nested checkout's current
HEAD. Executions use a separate detached reference checkout.

## Confirmed checks and findings

1. **Fresh macOS baseline build passed:** Lean 4.34.0, arm64,
   `lake build FloatSpec.Test FloatSpecTests floatspec` (6,207 jobs).
2. **The Claude FTZ proof is genuinely closed:** fresh LSP diagnostics passed;
   `#print axioms FloatSpec.Core.FTZ.FTZ_format_iff_generic` reported only
   `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`. The structural
   format predicate was compared with pinned `Core/FTZ.v:36`; it retains the
   nonzero normalized-mantissa and minimum-exponent requirements. This does
   not audit all downstream theorem statements. Four native/bit bridge debts
   remain in the manifest.
3. **Source-link gate bypass reproduced and repaired:** a mutual block with a
   classified first definition and unclassified second definition passed the
   old strict linter. The scanner selected only its first declaration. It now
   visits every written definition, checks privacy only in its modifiers, and
   handles root-qualified names. Executed positive and negative fixtures cover
   mutual members, a private first member, abbreviations, and qualified names.
   Link classification remains metadata, not semantic equivalence.
   The post-fix aggregate build passed again (6,207 jobs), and the existing
   paired Flocq examples passed with the configured Homebrew Rocq 9.2 compiler.
   The shell's other `coqc` is Rocq 9.1 and cannot load that checkout's `.vo`
   files; the bridge must resolve the compiler from `config.status`.
4. **The old paired tests are not a differential harness:** they execute small
   hand-written Lean and Rocq example sets independently. A generated shared
   input corpus and machine comparison are being added; do not treat the old
   test name as evidence of randomized or exhaustive cross-testing.

## Execution priorities

Maintain three separate loops: independent Lean tests, independent pinned
Flocq/Rocq tests, and a differential bridge that sends identical inputs to both.
Record concrete cases and seeds; promote disagreements to permanent regression
examples. Keep valid theorem domains distinct from total-function behavior
outside those domains. Test the bridge with intentional mismatches so a parser
or skipped command cannot silently produce a green result.

## Still unreviewed

The bulk of the theorem-by-theorem port and prior changes remain unreviewed.
Next work includes executable arithmetic/rounding cross-tests, the trust and
source-anchor scanner boundaries, and source-signature checks informed by any
counterexamples. Passing compilation, finite agreement, and a proof of a Lean
statement are three different claims; none alone proves whole-library Flocq
equivalence.
