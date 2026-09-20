# Review of the concurrent computable-comparison branch

Reviewed September 20, 2026. This is an independent review of local commits
`ff02ad28`, `f5d01e1d`, and `8b81a532` on
`claude-daemon/20260920_030005_computable_sf_compare`. They are **not merged**
into this audit branch. The original checkout and its modified `Deps/flocq`
remain untouched. Their common ancestor with the audit branch is `f95c7407`.

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
raw APIs. The arithmetic helpers could be useful under names that explicitly
say they compare *dyadic values*, or behind a theorem with the necessary
canonical-input hypotheses. That would be a distinct API and requires its
own review. The current audit branch does not need this replacement to make
the source comparator executable.

The companion `COMPUTABLE_COMPARE_GUIDE.md` also needs correction before
reuse: its claim that Rocq's raw `SFeqb` compares through reals is false for
the inspected source, and `@[flocq_source]` validates reference metadata,
not literal or semantic correspondence. The general technique of proving
an executable implementation equal to a mathematical specification remains
useful; first verify that the specification is the intended one.

This review establishes a concrete raw-interface mismatch. It does not claim
that the concurrent dyadic-order proofs are invalid, nor that every derived
wrapper is wrong on canonical inputs. Those broader statements were not proved.
