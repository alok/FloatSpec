# Review of the concurrent computable-comparison branch

Reviewed September 20, 2026. This is an independent review of local commits
`ff02ad28`, `f5d01e1d`, and `8b81a532` on
`claude-daemon/20260920_030005_computable_sf_compare`. Their common ancestor
with the audit branch is `f95c7407`. This review originally kept them separate;
the September 20 main-checkout integration now retains their value backend
with the contract corrections below. The modified `Deps/flocq` stays untouched.

## Finding: a valid equivalence proof can preserve the wrong specification

The new `ComputableCompare` backend aligns dyadic exponents and compares the
resulting integers. That is an appropriate algorithm for comparing the real
values of arbitrary dyadic records. Its `*_eq` theorems relate it to the older
real-valued Lean comparison definitions. That internal equivalence does not
establish equivalence to the actual raw Rocq API.

The source raw comparator, `Corelib.SpecFloat.SFcompare` imported by pinned
Flocq, compares same-sign finite records by exponent first, then mantissa.
Its numerical-order interpretation relies on canonical representation.
The current [source-facing Lean definition](../src/IEEE754/PrimFloat.lean)
retains that total raw behavior and is already executable.

The exact counterexample is:

| Observation | Result |
|---|---|
| First encoding | positive `3 × 2^-1` |
| Second encoding | positive `6 × 2^-2` |
| Real values | both `1.5` |
| New concurrent `SFcompareC` | `some .eq` |
| Current source-facing `SFcompare` | `some .gt` |
| Actual Rocq `SpecFloat.SFcompare` | `Some Gt` |

Both mantissas are positive, so this does not exploit Lean's extra zero-mantissa
carrier values. The inputs are noncanonical binary64 records; a raw API's
total behavior still differs even where its value theorem does not apply.
The concurrent equality test likewise returns `true`, whereas Rocq's raw
equality returns `false` for these encodings.

## What was run

The exact backend definitions and their dyadic-value lemmas were copied from
the `f5d01e1d` Git object into a temporary standalone Lean probe, without
changing their bodies. The old-spec equivalence and derived-wrapper section
were deliberately excluded because the current audit branch has repaired
those underlying source definitions. The probe then:

- proves by `decide +kernel` that the copied backend returns equality;
- proves that the current source API returns greater-than;
- proves that those results differ;
- executes both calls, printing `(some (Ordering.eq), some (Ordering.gt))`.

A separate Rocq fixture calls the actual imported `SpecFloat.SFcompare`, closes
the `Some Gt` equality with `vm_compute`, and prints `Some Gt`. It uses the
clean Flocq pin `7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`, built by Rocq 9.2.
The probe paths are `/private/tmp/ClaudeCompareSourceBoundary20260920.lean`
and `.v`; they are local evidence, not committed runtime dependencies.

The permanent paired [Lean](../../scripts/fixtures/PrimitiveComparison.lean)
and [Rocq](../../scripts/fixtures/PrimitiveComparison.v) regression already
contains this input. Run its Lean side with:

```sh
lake env lean scripts/fixtures/PrimitiveComparison.lean
```

It observes twelve entry points and validity separately; it does not let a
later validating conversion hide the raw discrepancy.

## Integration decision

Do not substitute these arbitrary-dyadic comparison backends for the source
raw APIs. The integrated module preserves the executable helpers and their
dyadic-value proofs. Its twelve public correspondence theorems are now named
`*_eq_value` and explicitly target the local `ValueSpec`. All twenty public
definitions carry local-helper classifications, and the module enables the
source-classification linter. The raw source comparator remains unchanged.

The companion [guide](COMPUTABLE_COMPARE_GUIDE.md) is corrected: its earlier
claim that Rocq's raw `SFeqb` compares through reals was false for the inspected
source. It also now distinguishes kernel reduction from native compilation
and unnecessary markers from genuinely classical data construction.

Integration checks: the full macOS Lean 4.34 build passes (6,226 jobs), both
edited Lean files have complete clean LSP diagnostics, and the retained
20,000-pair executable test passes. The 24-case paired raw-comparison fixtures
pass in Lean and pinned Rocq. The compiled trust gate covers 13,667 source
declarations in 59 modules and still finds only the four manifest debts.
Source hash: `4b714ddb87364ecf504600c50bc1421d89b61b91080f5926d742f2e1d5d30795`.

This review establishes a concrete raw-interface mismatch. It does not claim
that the concurrent dyadic-order proofs are invalid, nor that every derived
wrapper is wrong on canonical inputs. Those broader statements were not proved.
