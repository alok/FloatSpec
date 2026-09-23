# flocqsmith campaigns, 2026-09-23

**Result: no disagreement.** Two pre-registered campaigns ran 2,360
generated BinarySingleNaN programs on the three Lean paths (`lean-meta`
`#reduce`, `lean-ir` `lean --run`, `lean-kernel` `decide +kernel`). Every
case on every path returned `match` against Rocq 9.1.0 `vm_compute` on pinned
Flocq `7aab8f55`. There were no mismatches, no `lean-meta`/`lean-ir`
disagreements, and no infrastructure or harness verdicts, so there was
nothing to cluster or shrink and no minimal replay was committed.

The same generator revision, on fresh seeds, detected all 13 planted Lean-side
defects on all three paths in both campaigns. The exemplar lane test passed
(29 tests, none skipped). Every lane was re-judged offline from its retained
raw prover output (`verify-campaign`: verified).

This is finite differential evidence for one world (BinarySingleNaN, radix 2,
ten formats). It is not a proof of equivalence. Section 7 lists what it does
not cover.

## 1. How to reproduce

The runner (`d181320f`) takes a committed descriptor. It refuses a descriptor
that is uncommitted or edited, and it refuses a dirty tree, unless
`--allow-dirty` is passed. That flag is recorded in the report, and neither
campaign used it.

```sh
export FLOCQ_AUDIT_DIR=/private/tmp/flocq-audit-rocq91-20260921   # pinned, built Flocq 7aab8f55
uv run scripts/run_flocqsmith.py campaign \
    scripts/fixtures/flocqsmith/campaign_2026-09-23.descriptor.json \
    --flocq-dir "$FLOCQ_AUDIT_DIR" --out OUT1
uv run scripts/run_flocqsmith.py campaign \
    scripts/fixtures/flocqsmith/campaign_2026-09-23-extended.descriptor.json \
    --flocq-dir "$FLOCQ_AUDIT_DIR" --out OUT2
uv run scripts/run_flocqsmith.py verify-campaign OUT1   # offline: digests + every verdict re-judged
```

For each campaign the runner:

1. runs the lanes one at a time, with at most two prover processes;
2. re-judges each lane offline;
3. measures coverage over cases judged on every path, so an infrastructure
   failure never counts as coverage;
4. clusters disagreements by root signature (op, value type, differing
   fields, mode, format, set of paths), and infrastructure failures
   separately by (path, verdict, stage);
5. shrinks up to three members per cluster;
6. runs the exemplar lane test if the descriptor asks for it;
7. publishes `campaign.json` and `complete.json` by one atomic rename.

A campaign reports `passed` only if all of the following hold:

- every lane passed;
- every lane verified;
- coverage has no gap;
- there are no disagreement clusters and no infrastructure clusters;
- the exemplar lane passed.

A dry run of the pipeline checked the clustering and shrinking paths first. In
it, the baseline was swapped for the `enc_sign_flip` planted defect, so every
case mismatched. It produced four clusters, and all four shrinks kept their
verdict and reduced to one statement.

## 2. Identities

| | |
|---|---|
| Reference | Flocq `7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f`, clean `src`, at `/private/tmp/flocq-audit-rocq91-20260921` |
| Rocq | The Rocq Prover 9.1.0 (`_opam/bin/coqc`, sha256 `00d32d468a62b465…`) |
| Lean | 4.34.0, commit `293d5d0c`, arm64-apple-darwin (sha256 `1b370cfcbf44e80d…`) |
| Lean source fingerprint | `cd22873cb11cf2d8…` (unchanged during both runs) |
| Generator revision | `bbe722a75cc047bd…` (both campaigns) |
| Campaign 1 | HEAD `a26c90a6`, clean; descriptor blob `2d24d4db` (sha256 `2bf7cb95…`); `campaign.json` sha256 `eaf280fb…` |
| Campaign 2 | HEAD `c6c91837`, clean; descriptor blob `320a86e7` (sha256 `4f6de583…`); `campaign.json` sha256 `2a8bb04d…` |

The committed reports are
`scripts/fixtures/flocqsmith/campaign_2026-09-23.report.json` and
`scripts/fixtures/flocqsmith/campaign_2026-09-23-extended.report.json`. Each
names every lane's `report.json` and `complete.json` digest. The raw evidence
is not committed. It holds every generated `.v` and `.lean` file, every raw
prover stream and every case record: 25 MB for campaign 1 and 104 MB for
campaign 2. It is kept in the session scratchpad
(`…/scratchpad/camp/c20260923{,ext}`) and can be regenerated with the
commands above.

## 3. Campaign 1: the pre-registered plan

Descriptor: `scripts/fixtures/flocqsmith/campaign_2026-09-23.descriptor.json`,
committed in `a26c90a6` before the run. Report committed in `402b5fad`. It took
322 s in total, including the exemplar lane.

Observed bindings compared on each path: 8,245 over 400 programs.

### Verdict totals (baseline cases, all lanes)

| Path | `match` |
|---|---:|
| `lean-meta` | 400 |
| `lean-ir` | 400 |
| `lean-kernel` | 400 |

### Lanes

| Lane | Kind | Seed | N | Sizes | Status | Judged (meta/ir/kernel) | Mismatch | Infra | Harness | verify | Seconds |
|---|---|---:|---:|---|---|---|---:|---:|---:|---|---:|
| `mixed-a` | run | 2026092301 | 80 | 4-12 | `passed` | 80/80/80 | 0 | 0 | 0 | `verified` (80 re-judged) | 22 |
| `mixed-b` | run | 2026092302 | 80 | 4-12 | `passed` | 80/80/80 | 0 | 0 | 0 | `verified` (80 re-judged) | 22 |
| `mixed-long` | run | 2026092303 | 60 | 10-20 | `passed` | 60/60/60 | 0 | 0 | 0 | `verified` (60 re-judged) | 31 |
| `wide` | run | 2026092304 | 60 | 4-10 | `passed` | 60/60/60 | 0 | 0 | 0 | `verified` (60 re-judged) | 22 |
| `tiny` | run | 2026092305 | 80 | 8-20 | `passed` | 80/80/80 | 0 | 0 | 0 | `verified` (80 re-judged) | 26 |
| `controls` | controls | 2026092306 | 40 | 4-12 | `controls-ok` | 40/40/40 | 0 | 0 | 0 | `verified` (348 re-judged) | 142 |

### Coverage (400 of 400 generated programs judged on every path)

| Format | Programs | add-sub-fma | mult | div-sqrt | sign-erase | succ-pred-ulp | scale | integer-rounding | constants | construct-round | compare | classify |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `t1_2` | 24 | 134 | 37 | 25 | 19 | 65 | 13 | 11 | 40 | 159 | 32 | 27 |
| `t2_3` | 34 | 160 | 33 | 34 | 20 | 74 | 27 | 27 | 32 | 249 | 24 | 42 |
| `t3_4` | 44 | 166 | 110 | 56 | 25 | 74 | 56 | 42 | 17 | 327 | 38 | 42 |
| `t4_8` | 55 | 269 | 77 | 70 | 24 | 96 | 48 | 30 | 35 | 384 | 34 | 45 |
| `t5_7` | 32 | 149 | 55 | 48 | 20 | 51 | 28 | 29 | 21 | 240 | 23 | 32 |
| `t8_16` | 48 | 173 | 77 | 64 | 29 | 86 | 48 | 31 | 22 | 307 | 25 | 43 |
| `b16` | 58 | 251 | 66 | 65 | 34 | 105 | 33 | 19 | 25 | 392 | 46 | 60 |
| `bf16` | 42 | 135 | 44 | 51 | 18 | 54 | 36 | 31 | 23 | 238 | 33 | 37 |
| `b32` | 35 | 59 | 51 | 43 | 11 | 85 | 17 | 24 | 16 | 211 | 24 | 37 |
| `b64` | 28 | 31 | 32 | 32 | 14 | 43 | 19 | 19 | 14 | 165 | 18 | 36 |

- **forms**: `branch` 86, `case4` 251, `corner` 288, `fold` 225, `op` 400, `select` 247
- **modes**: `DN` 764, `NA` 816, `NE` 744, `UP` 749, `ZR` 728
- **corners**: `cancel` 162, `equal_pair` 46, `fma_error` 134, `half_int` 144, `max_succ` 41, `overflow_edge` 168, `sticky_gap` 92, `tie_mult` 110, `tie_plus` 238, `tiny` 124
- **ops**: all 36 table ops; fewest: `is_nan` 53, `is_finite_strict` 59, `Bfrexp.1` 60, `Bnormfr_mantissa` 61, `B2SF` 63, `Bulp` 65
- **gaps**: none
- **empty (format, op) cells**: 1 of 360: `t5_7/Bulp`

### Numeric tags (reference side, all lanes)

`exact` 892, `exact_zero_sum` 237, `exact_zero_sum:DN` 59, `exact_zero_sum:NA` 45, `exact_zero_sum:NE` 41, `exact_zero_sum:UP` 47, `exact_zero_sum:ZR` 45, `inexact` 598, `nan_result` 347, `negative_zero_result` 112, `overflow_range` 248, `subnormal_range` 206, `tie` 430, `tie:DN` 83, `tie:NA` 94, `tie:NE` 107, `tie:UP` 71, `tie:ZR` 75

### Positive controls

| Control | Exposed | Detected | Rate | Detected by meta/ir/kernel | Other verdicts | ok |
|---|---:|---:|---:|---|---|---|
| `tie_rne_as_rna` | 36 | 4 | 0.1111 | 4/4/4 | - | True |
| `dn_zero_sign` | 32 | 4 | 0.125 | 4/4/4 | - | True |
| `updn_swap_negative` | 29 | 5 | 0.1724 | 5/5/5 | - | True |
| `zr_overflow_to_inf` | 36 | 6 | 0.1667 | 6/6/6 | - | True |
| `subnormal_exp_off_by_one` | 29 | 12 | 0.4138 | 12/12/12 | - | True |
| `fma_double_rounding` | 19 | 8 | 0.4211 | 8/8/8 | - | True |
| `succ_max_saturates` | 11 | 5 | 0.4545 | 5/5/5 | - | True |
| `ltb_as_leb` | 4 | 4 | 1.0 | 4/4/4 | - | True |
| `trunc_floor` | 8 | 4 | 0.5 | 4/4/4 | - | True |
| `nearbyint_na_as_ne` | 8 | 2 | 0.25 | 2/2/2 | - | True |
| `enc_sign_flip` | 40 | 40 | 1.0 | 40/40/40 | - | True |
| `enc_bool_negate` | 20 | 20 | 1.0 | 20/20/20 | - | True |
| `mode_swap_up_dn` | 36 | 28 | 0.7778 | 28/28/28 | - | True |

### Exemplar lane

`FLOCQ_AUDIT_DIR=… uv run scripts/test_flocq_exemplars.py -v`, run by the campaign: status `passed`, 29 tests, 0 skipped, 0 failures, 0 errors, 43 s. The 29 tests are 12 live tests and 17 offline tests. The live tests are:

- the eight exemplar comparisons between Rocq `vm_compute` and Lean `#eval`, each with an oracle verdict on both sides;
- the three mutation controls: NE→NA drift on the Lean side, constant drift on the Rocq side, and a Lean file that does not compile, which must come back as `lean-infra`;
- the check that the verbatim upstream files have not drifted.

The offline tests cover the oracles and the fixtures. The raw test output is kept in the campaign evidence under `exemplars/`.

## 4. Campaign 2: extended

Campaign 1 used about 5 minutes of its 90-minute budget, so a second, larger
campaign was pre-registered in `c6c91837`. The descriptor was written after
campaign 1's result was known and before any campaign 2 lane ran. It has one
lane per format, a larger mixed lane, two stress lanes and a fresh control
lane:

- **One lane per format:** 120 programs each.
- **Mixed lane:** 400 programs.
- **Long-program stress lane:** programs of 16 to 28 statements, with twice
  the default per-program cost budget.
- **Wide-format stress lane:** binary32 and binary64 with an 8 s cost budget,
  which admits far exponent gaps.
- **Control lane:** a fresh positive-control lane.

The exemplar lane was not repeated, because the Lean sources and the fixtures
were unchanged.

Observed bindings compared on each path: 44,029 over 1,960 programs.

### Verdict totals (baseline cases, all lanes)

| Path | `match` |
|---|---:|
| `lean-meta` | 1960 |
| `lean-ir` | 1960 |
| `lean-kernel` | 1960 |

### Lanes

| Lane | Kind | Seed | N | Sizes | Status | Judged (meta/ir/kernel) | Mismatch | Infra | Harness | verify | Seconds |
|---|---|---:|---:|---|---|---|---:|---:|---:|---|---:|
| `only-t1-2` | run | 2026092311 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 31 |
| `only-t2-3` | run | 2026092312 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 35 |
| `only-t3-4` | run | 2026092313 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 34 |
| `only-t4-8` | run | 2026092314 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 34 |
| `only-t5-7` | run | 2026092315 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 36 |
| `only-t8-16` | run | 2026092316 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 38 |
| `only-b16` | run | 2026092317 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 41 |
| `only-bf16` | run | 2026092318 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 54 |
| `only-b32` | run | 2026092319 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 62 |
| `only-b64` | run | 2026092320 | 120 | 6-16 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 121 |
| `mixed-big` | run | 2026092321 | 400 | 4-12 | `passed` | 400/400/400 | 0 | 0 | 0 | `verified` (400 re-judged) | 128 |
| `stress-long` | run | 2026092322 | 200 | 16-28 | `passed` | 200/200/200 | 0 | 0 | 0 | `verified` (200 re-judged) | 159 |
| `stress-wide` | run | 2026092323 | 120 | 6-14 | `passed` | 120/120/120 | 0 | 0 | 0 | `verified` (120 re-judged) | 137 |
| `controls` | controls | 2026092324 | 40 | 4-12 | `controls-ok` | 40/40/40 | 0 | 0 | 0 | `verified` (337 re-judged) | 175 |

### Coverage (1960 of 1960 generated programs judged on every path)

| Format | Programs | add-sub-fma | mult | div-sqrt | sign-erase | succ-pred-ulp | scale | integer-rounding | constants | construct-round | compare | classify |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `t1_2` | 141 | 585 | 161 | 174 | 74 | 255 | 158 | 96 | 201 | 870 | 106 | 135 |
| `t2_3` | 162 | 772 | 246 | 229 | 82 | 317 | 207 | 112 | 135 | 1136 | 142 | 235 |
| `t3_4` | 213 | 998 | 348 | 310 | 140 | 449 | 218 | 150 | 135 | 1561 | 201 | 260 |
| `t4_8` | 213 | 937 | 427 | 239 | 124 | 438 | 181 | 146 | 113 | 1600 | 162 | 260 |
| `t5_7` | 176 | 811 | 312 | 272 | 109 | 327 | 194 | 143 | 91 | 1311 | 157 | 184 |
| `t8_16` | 190 | 900 | 237 | 259 | 106 | 373 | 215 | 93 | 109 | 1359 | 179 | 222 |
| `b16` | 244 | 1068 | 399 | 301 | 158 | 593 | 238 | 178 | 122 | 1688 | 217 | 258 |
| `bf16` | 162 | 744 | 281 | 188 | 85 | 302 | 148 | 112 | 103 | 1191 | 118 | 199 |
| `b32` | 220 | 808 | 372 | 276 | 127 | 498 | 230 | 152 | 118 | 1548 | 183 | 234 |
| `b64` | 239 | 532 | 417 | 287 | 136 | 514 | 134 | 150 | 136 | 1648 | 233 | 276 |

- **forms**: `branch` 530, `case4` 1289, `corner` 1406, `fold` 1266, `op` 1960, `select` 1252
- **modes**: `DN` 3967, `NA` 3962, `NE` 4021, `UP` 3879, `ZR` 3907
- **corners**: `cancel` 1145, `equal_pair` 244, `fma_error` 443, `half_int` 634, `max_succ` 212, `overflow_edge` 799, `sticky_gap` 466, `tie_mult` 491, `tie_plus` 1137, `tiny` 636
- **ops**: all 36 table ops; fewest: `Bnormfr_mantissa` 332, `Bpred_pos'` 339, `binary_round` 368, `Babs` 373, `Bopp` 374, `is_finite` 374
- **gaps**: none
- **empty (format, op) cells**: 0 of 360

### Numeric tags (reference side, all lanes)

`exact` 4662, `exact_zero_sum` 1430, `exact_zero_sum:DN` 358, `exact_zero_sum:NA` 255, `exact_zero_sum:NE` 274, `exact_zero_sum:UP` 266, `exact_zero_sum:ZR` 277, `inexact` 3170, `nan_result` 2127, `negative_zero_result` 773, `overflow_range` 1279, `subnormal_range` 1058, `tie` 2150, `tie:DN` 391, `tie:NA` 442, `tie:NE` 533, `tie:UP` 403, `tie:ZR` 381

### Positive controls

| Control | Exposed | Detected | Rate | Detected by meta/ir/kernel | Other verdicts | ok |
|---|---:|---:|---:|---|---|---|
| `tie_rne_as_rna` | 35 | 4 | 0.1143 | 4/4/4 | - | True |
| `dn_zero_sign` | 24 | 8 | 0.3333 | 8/8/8 | - | True |
| `updn_swap_negative` | 28 | 8 | 0.2857 | 8/8/8 | - | True |
| `zr_overflow_to_inf` | 28 | 3 | 0.1071 | 3/3/3 | - | True |
| `subnormal_exp_off_by_one` | 28 | 9 | 0.3214 | 9/9/9 | - | True |
| `fma_double_rounding` | 16 | 5 | 0.3125 | 5/5/5 | - | True |
| `succ_max_saturates` | 11 | 1 | 0.0909 | 1/1/1 | - | True |
| `ltb_as_leb` | 8 | 3 | 0.375 | 3/3/3 | - | True |
| `trunc_floor` | 9 | 5 | 0.5556 | 5/5/5 | - | True |
| `nearbyint_na_as_ne` | 10 | 3 | 0.3 | 3/3/3 | - | True |
| `enc_sign_flip` | 40 | 40 | 1.0 | 40/40/40 | - | True |
| `enc_bool_negate` | 24 | 24 | 1.0 | 24/24/24 | - | True |
| `mode_swap_up_dn` | 36 | 24 | 0.6667 | 24/24/24 | - | True |

## 5. Disagreements and minimal replays

**None in either campaign.** No case on any path returned
`observation-mismatch`, and the two Lean evaluators never disagreed with each
other. Both campaigns therefore have empty cluster and shrink lists, and
`scripts/fixtures/flocqsmith/replays/` does not exist. The offline test
`test_committed_minimized_replays_regenerate_their_digests` replays whatever
that directory holds. It currently passes because the directory is empty.

A clean result means something only because the same pipeline, at the same
generator revision and on fresh seeds, caught every planted defect:

- **Detected by all three paths.** Every control that was detected in a
  program was detected there by all three paths.
- **No other verdicts.** No control produced an infrastructure or harness
  verdict.
- **Rare defects were still caught.** Some planted defects show up in only
  a few of the programs that exercise them. Detection rates per exposed
  program (campaign 1 / campaign 2):
  - `tie_rne_as_rna`, a tie rounded to nearest-away under nearest-even:
    0.11 / 0.11;
  - `zr_overflow_to_inf`, overflow to infinity under round-toward-zero:
    0.17 / 0.11;
  - `succ_max_saturates`, `Bsucc` stuck at the largest finite value:
    0.45 / 0.09 (1 of 11);
  - `dn_zero_sign`, the sign of an exact zero under round-down:
    0.13 / 0.33.

  These rates come from the control-focused corpus. A real defect that is
  equally rare could escape an unfocused campaign of this size.

## 6. Infrastructure failures

**None.** Neither campaign produced a `reference-infra-failure`, a
`clone-infra-failure` (at any stage: heartbeats, timeout, `meta-stuck`,
`kernel-stuck`, `ir-panic`, `ir-crash` or `process-crash`), a
`both-infra-failure` or a `harness-error`. The two stress lanes were meant to
push programs toward the fixed heartbeat limit (40,000,000 per case) and the
process timeouts. They did not reach either limit. `stress-long` ran 200 programs of 16 to 28 statements, under a per-program cost budget of 6 s, in 159 s.
`stress-wide` ran 120 binary32/64 programs under an 8 s budget in 137 s. Its most expensive program was predicted at 7.9 s. Both lanes returned only `match`. Per-case wall time is not recorded, so how close any case came to the heartbeat limit is not known.

Infrastructure verdicts are never counted as matches. If any had occurred,
they would appear in `infra_clusters` in the report and would fail the
campaign, not pass it.

## 7. What this does not show

- **It does not prove equivalence.** 2,360 programs and 52,274
  observed bindings per path are finite evidence.
- **Only one world ran.** Every program is BinarySingleNaN at radix 2. The
  full-payload `B` world, the `W` IEEE-width wrappers, the raw `SF` kernels,
  `Fl(β)` at other radixes and the raw-parameter lane are still design only
  (FLOCQSMITH.md §14.1). The one exception is the exemplar lane: its eight
  fixed programs reach radixes 2, 3, 5, 7 and 10 and CompCert's NaN
  payloads.
- **It shows faithfulness to Flocq, not IEEE correctness.** Rocq is the
  reference. The exact oracle contributes only the numeric tags, which count
  ties, overflow-range results and so on in the reference values. It never
  votes.
- **The rare-defect rates come from a focused corpus.** The control lanes use
  a control-focused corpus (FLOCQSMITH.md §14.4). As §5 says, the low rates
  for the rarest planted defects mean an unfocused campaign of this size
  could miss a real defect that is equally rare.
- **The coverage figures are structural.** "Every (format, op family) cell"
  means each cell was generated and judged at least once. It does not mean
  each op met every boundary class in every format. In the forms lists,
  `op` and `corner` count programs that contain one; `select`, `case4`,
  `fold` and `branch` count statements; mode counts include mint statements.
  One (format, op) cell was
  empty in campaign 1 (`t5_7/Bulp`). Campaign 2 filled all 360 cells.
- **Native execution is not covered.** Hardware floats and `lean-native` are
  not run, so neither are exception flags.
- **Known budget gaps remain.** The cost model does not charge a `Z` mantissa
  by its digit count, and heartbeats are a fixed per-case constant. Neither
  limit was reached (§6), but that was not guaranteed.

## 8. Changes made for these campaigns

| Commit | Change |
|---|---|
| `d181320f` | `scripts/flocqsmith/descriptor.py`, the `campaign` and `verify-campaign` subcommands, and five offline `DescriptorTests`. The tests check that the op families partition the table, that descriptors are validated, that the root-signature fields are right, and that the committed replay digests match. |
| `a26c90a6` | Campaign 1 descriptor (pre-registered). |
| `402b5fad` | Campaign 1 report. |
| `c6c91837` | Campaign 2 descriptor (pre-registered). |
| `7c383055` | Campaign 2 report. |
| this commit | This document, and the FLOCQSMITH.md status rows and CLI section. |
