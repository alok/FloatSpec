# Exemplar lane fixtures

These fixtures take programs that other people wrote against Flocq, trim
them to Flocq only, and run them on both sides. The approach follows
[grossmith](https://github.com/OathTech/grossmith), which checks Go clones
against `gc` on complete programs rather than single operations. The
fixtures implement the exemplar lane of `FloatSpec/docs/FLOCQSMITH.md` §11.

Each exemplar is a pair of files:

- `NAME.v` depends only on the pinned Flocq and prints one `list (list Z)`
  with `Eval vm_compute`.
- `NAME.lean` computes the same rows with FloatSpec's executable API and
  prints them with `#eval`.

`scripts/flocq_exemplars.py` gives each exemplar two verdicts:

1. **Differential.** Both sides must print exactly the same rows, with the
   declared row count and width. Intermediate values are included as columns
   where the program has them, so a representation difference cannot hide
   behind an equal final answer.
2. **Oracle.** Each side's rows must satisfy the theorems that the upstream
   program proves. The checks use exact rationals in Python and never reuse
   the algorithms under test. Rows whose theorem premises are false are
   counted, not judged. Some exemplars include such rows on purpose as
   positive controls: at least one of them must break the identity, which
   shows that the oracle can fail.

```sh
uv run scripts/flocq_exemplars.py --flocq-dir "$FLOCQ_AUDIT_DIR"            # all exemplars
uv run scripts/flocq_exemplars.py --flocq-dir "$FLOCQ_AUDIT_DIR" --only CodyWaite --output DIR
FLOCQ_AUDIT_DIR=... uv run scripts/test_flocq_exemplars.py -v              # unittest wrapper
```

The runner copies the fixtures to a temporary directory. It never writes
into the reference checkout or into this directory. It first compiles the
shared modules:

- Rocq: `coqc -R <tmp> Exemplars`;
- Lean: `lean -R <tmp> -o <tmp>/olean/Exemplars/NAME.olean`, with that
  directory appended to Lake's `LEAN_PATH`.

Every exemplar then imports them as `Exemplars.Compute` and
`Exemplars.Choices`. Any compiler diagnostic fails the run. The one
exception is the deprecation warnings that the verbatim upstream
`Compute.v` produces under Rocq 9.1; the runner passes `-w -deprecated` for
that file only.

Agreement here is finite testing. It is not a proof that the Lean and Rocq
definitions are equivalent.

## Modules

| Module | Kind | Upstream (commit) | Rocq side | Lean side | Oracle |
|---|---|---|---|---|---|
| `Compute` | shared | Flocq `examples/Compute.v` (`7aab8f55`) | verbatim copy; the test checks byte equality with the pinned reference | transliteration of the four definitions over `Calc.Operations`/`Round`/`Div`/`Sqrt` | (library) |
| `Choices` | shared | not upstream; derived from Flocq `src/Calc/Round.v` (`7aab8f55`) | choice functions, each proved to satisfy `Compute.v`'s `rnd_choice` via `inbetween_int_*_sign` | same functions, same proofs via the FloatSpec ports of those lemmas | (library) |
| `ComputeGrid` | exemplar | driver over `Compute.v` (FloatSpec-authored) | radices 2/3/10 × FLX/FLT/FIX/FTZ × DN/UP/ZR/NE/NA × 16 input pairs | same | `plus/mult/div/sqrt_correct`: exact rounding of the exact result |

## Trim manifests

### `Compute` (Flocq `examples/Compute.v`, LGPL-3.0-or-later)

- Rocq: the whole file, kept verbatim.
- Lean: `plus`, `mult`, `sqrt` and `div` are transliterated line by line.
  The parameters (radix, `fexp`, `choice`) and the operation order are the
  same. The Lean side calls only the FloatSpec ports of the Flocq
  functions that `Compute.v` calls. The correctness theorems and their
  section hypotheses are not transliterated.

### `Choices` (FloatSpec-authored)

`Compute.v` is parametric in a sign-magnitude `choice` that satisfies its
hypothesis `rnd_choice`. The choices here come from Flocq's own lemmas
`inbetween_int_{DN,UP,ZR,NE,NA,N}_sign`, and each file re-proves that
hypothesis for its choice, so a wrong choice cannot compile. This matters
because guessing gets it wrong: the ZR choice is `m` itself, not
`cond_incr (round_ZR s l) m`, since `round_ZR` expects a signed mantissa.

### `ComputeGrid` (FloatSpec-authored driver)

- Row layout: `[beta; format; choice; mx; ex; my; ey; plus m e; mult m e;
  div m e; sqrt m e]`.
- Formats:
  - `0` = `FLX_exp 3`
  - `1` = `FLT_exp (-3) 3`
  - `2` = `FIX_exp (-1)`
  - `3` = `FTZ_exp (-3) 3`

  Flocq's `FLT_exp` and `FTZ_exp` take `emin` first, but the FloatSpec
  ports take `prec` first. The Lean fixture spells this out.
- Division by zero: one input pair has `y = 0`. Its `div` column is
  compared across the two sides, but the oracle does not judge it.

## Exclusions

None so far. If the Lean side lacks an executable counterpart for part of
an exemplar, that part stays in the `.v` file and is listed here. It is not
faked on the Lean side.

## Licensing

FloatSpec is Apache-2.0. The files here that contain or transliterate
third-party text keep that text's licence. Each such file says so in its
header, and the table above names the source:

- Flocq examples: LGPL-3.0-or-later.

The FloatSpec-authored drivers and `Choices` are Apache-2.0, like the rest
of the repository.
