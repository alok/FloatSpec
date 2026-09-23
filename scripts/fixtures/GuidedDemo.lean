import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.PrimFloat
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Run with `lake env lean --run scripts/fixtures/GuidedDemo.lean`.
Each section is a computation using the port, followed by a kernel-checked
finite assertion. These examples do not establish universal conformance.

Each example quotes (or points back to) the Coq that decides its answer, from
Flocq at the pinned commit 7aab8f55. Flocq takes some definitions, such as
`shr_1`, `SFcompare`, SpecFloat's `valid_binary`, and `SF2Prim`, from the Rocq
core library; those are quoted from Rocq V9.1.0, the prover that builds the
pinned reference. Quotes are verbatim, in one of two forms.

* Checked: a Flocq declaration that a Lean port anchors with `@[flocq_source]`
  is quoted in a block whose fence names the anchor (`coq BinarySingleNaN.Bplus`),
  inside a Verso docstring (`set_option doc.verso true in`). Lean resolves the
  name to one pinned line, the hover links that line at the pinned commit, and
  `scripts/validate_flocq_source_refs.py` compares the block byte for byte with
  the pinned source, from that line through the end of the Rocq sentence. These
  docstrings write names as `{coq}` (a checked, linked Flocq citation), `{name}`
  (a Lean declaration), or `{lit}` (text Lean does not check).
* Unchecked: a quote from the Rocq core library, or of a Flocq definition that no
  Lean port anchors (such as `choice_mode`), is a plain block. Nothing compares
  it with the source. Its first line, `(* Rocq V9.1.0 path:lines *)` or
  `(* Flocq path:lines (7aab8f55) *)`, gives the location; a `(* ... *)` line
  marks omitted lines; and Rocq lines keep the indentation of their enclosing
  Section or Module.

One-line aliases, type-conversion wrappers, and small helpers are cited in the
prose by file and line rather than quoted. A row `[sign, mantissa, exponent]`
means `(-1)^sign * mantissa * 2^exponent`.

Coq vocabulary: `xH` = 1, `xO p` = 2p, and `xI p` = 2p+1 spell a `positive` in
binary, lowest bit outermost; `Zpos p`, `Zneg p`, and `Z0` are +p, -p, and 0.
`Z.add`, `Z.sub`, `Z.min`, `Z.max`, `Z.eqb`, and `Z.leb` are +, -, min, max, =,
and <= on integers; `negb`, `andb`, and `orb` are not, and, or. `digits2_pos m`
and `Zdigits2 m` count the bits of `|m|`. `loc_Exact` means nothing was dropped;
`loc_Inexact Lt|Eq|Gt` means the dropped part was below, exactly, or above half.
A `shr_record` (m, r, s) holds the kept mantissa, the last dropped bit (round
bit), and whether any earlier dropped bit was 1 (sticky bit). `cond_incr b m`
adds one to m when b is true. `shl_align m e e'` shifts m left so that its
exponent drops to e' (and leaves it alone when e' is not below e).
`iter_pos f p x` applies f to x, p times. `B2SF` and `B2BSN` re-type a float
without changing its value, and arguments such as `Hx` or `Bulp_correct_aux`
are proofs carried with the data. `SF2B _ (proj1 (binary_round_correct ...))`
is `binary_round ...` packaged with the proof that its result is valid. -/

namespace GuidedDemo

private def observe : StandardFloat → List Int
  | .S754_finite sign mantissa exponent => [if sign then 1 else 0, mantissa, exponent]
  | _ => []

set_option doc.verso true in
/-- **1. Exact arithmetic.** Coq's {coq}`BinarySingleNaN.Bplus` shifts both integer
mantissas to the smaller exponent {lit}`ez`, adds them with their signs ({lit}`Fplus_naive`,
{lit}`BinarySingleNaN.v:1837-1838`), and rounds the sum once with
{coq}`BinarySingleNaN.binary_normalize`, which calls {coq}`BinarySingleNaN.binary_round`
(example 3); 3.75 fits in 24 bits, so nothing is rounded away. Flocq's {coq}`b32_plus`
({lit}`Bits.v:669`) is Binary.v's {lit}`Bplus` at precision 24 and emax 128, which handles NaN
payloads and delegates to this {coq}`BinarySingleNaN.Bplus` ({lit}`Binary.v:1049-1050`). Lean's
{name}`b32_plus` runs the computable {name}`Binary.Bplus` in {lit}`BinarySingleNaN.lean`, which
merges both layers into one match and writes {coq}`BinarySingleNaN.binary_normalize` inline: zero
test, sign split, {name}`binary_round`.

```coq BinarySingleNaN.Bplus
Definition Bplus m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => if Bool.eqb sx sy then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Fplus_naive sx mx ex sy my ey ez)
      ez (match m with mode_DN => true | _ => false end)
  end.
```

```coq BinarySingleNaN.binary_normalize
Definition binary_normalize mode m e szero :=
  match m with
  | Z0 => B754_zero szero
  | Zpos m => SF2B _ (proj1 (binary_round_correct mode false m e))
  | Zneg m => SF2B _ (proj1 (binary_round_correct mode true m e))
  end.
```
-/
private def sumBits : Nat :=
  (bits_of_b32 (b32_plus .RNE (b32_of_bits 0x3fc00000) (b32_of_bits 0x40100000))).toNat

example : sumBits = 0x40700000 := by decide +kernel

set_option doc.verso true in
/-- **2. Rounding modes.** {coq}`BinarySingleNaN.binary_round` (next example) cuts 1.125 to
the three-bit mantissa 4 with a dropped part of exactly half ({lit}`loc_Inexact Eq`),
then asks Coq's {lit}`choice_mode` whether to add one. NE adds one only if 4 were
odd (at an exact half {coq}`round_N` returns its first argument), NA always, ZR
never, DN only for a negative inexact value, and UP only for a positive one
({coq}`round_sign_DN` and {coq}`round_sign_UP`, {lit}`Round.v:180-184` and
{lit}`Round.v:273-277`). Lean's {lit}`.RNE .RTZ .RTN .RTP .RNA` are Coq's
{lit}`mode_NE mode_ZR mode_DN mode_UP mode_NA`, and Lean's {name}`choice_mode`
({lit}`BinarySingleNaN.lean`) has the same five branches.

```
(* Flocq src/IEEE754/BinarySingleNaN.v:1140-1147 (7aab8f55) *)
Definition choice_mode m sx mx lx :=
  match m with
  | mode_NE => cond_incr (round_N (negb (Z.even mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx
  end.
```

```coq round_N
Definition round_N (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => p
  | loc_Inexact Gt => true
  end.
```
-/
private def modes (sign : Bool) : List (List Int) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].map fun mode =>
    observe (binary_round (prec := 3) (emax := 4) mode sign 9 (-3))

example : modes false = [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] ∧
    modes true = [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] := by
  decide +kernel

set_option doc.verso true in
/-- **3. Double rounding.** Coq's {coq}`BinarySingleNaN.binary_round` first aligns the
mantissa to the format's exponent ({lit}`shl_align_fexp` shifts it left when it has fewer
digits than the format needs; 73 does not). Then {coq}`BinarySingleNaN.binary_round_aux`
shifts it down to the precision ({lit}`shr_fexp`), rounds with {lit}`choice_mode`, and
renormalizes. Under NE, {coq}`round_N` (example 2) rounds up above half and breaks an exact
half toward an even mantissa. Directly, {lit}`73*2^-6` (73 = 1001001 in binary) keeps 100 and
drops 1001, above half, so it rounds up to {lit}`5*2^-2` = 1.25. Lean's {name}`binary_round`
and {name}`binary_round_aux` ({lit}`BinarySingleNaN.lean`) follow these lines.

```coq BinarySingleNaN.binary_round
Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx (Zpos mz) ez loc_Exact.
```

```
(* Flocq src/IEEE754/BinarySingleNaN.v:1678-1679 (7aab8f55) *)
Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).
```

```coq BinarySingleNaN.binary_round_aux
Definition binary_round_aux mode sx mx ex lx :=
  let '(mrs', e') := shr_fexp mx ex lx in
  let '(mrs'', e'') := shr_fexp (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
  match shr_m mrs'' with
  | Z0 => S754_zero sx
  | Zpos m => binary_fit_aux mode sx m e''
  | _ => S754_nan
  end.
```
-/
private def direct : List Int :=
  observe (binary_round (prec := 3) (emax := 10) .RNE false 73 (-6))

/-- The same `binary_round` at four bits keeps 1001 and drops 001 (below half),
giving `9*2^-3` = 1.125. At three bits that is an exact half, which NE breaks
toward the even mantissa 4, so the result is 1. -/
private def viaFour : List Int :=
  match binary_round (prec := 4) (emax := 10) .RNE false 73 (-6) with
  | .S754_finite sign mantissa exponent =>
      observe (binary_round (prec := 3) (emax := 10) .RNE sign mantissa exponent)
  | _ => []

example : direct = [0,5,-2] ∧ viaFour = [0,4,-2] := by decide +kernel

set_option doc.verso true in
/-- **4. Signed zero, NaN, successor.** Coq compares through {lit}`SFcompare`, whose
zero row answers {lit}`Some Eq` whatever the signs and whose NaN row answers {lit}`None`
(unordered). Flocq's {coq}`b64_compare` ({lit}`Bits.v:743`) is Binary.v's
{coq}`Binary.Bcompare` at precision 53 and emax 1024. Lean's {name}`b64_compare` reaches
{name}`BinarySingleNaN.Bcompare` ({lit}`BinarySingleNaN.lean`), which has the same rows,
written {lit}`some .eq` and {lit}`none`.

```coq Binary.Bcompare
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2).
```

```coq BinarySingleNaN.Bcompare
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  SFcompare (B2SF f1) (B2SF f2).
```

```
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:177-209 *)
  Definition SFcompare f1 f2 :=
    match f1, f2 with
    | S754_nan , _ | _, S754_nan => None
    (* ... *)
    | S754_zero _, S754_zero _ => Some Eq
    (* ... *)
    end.
```
-/
private def zeroComparison : Option Ordering :=
  b64_compare (b64_of_bits 0) (b64_of_bits 0x8000000000000000)

/-- Same path as `zeroComparison`; the NaN row of `SFcompare` gives `none`. -/
private def nanComparison : Option Ordering :=
  b64_compare (b64_of_bits 0x7ff8000000000000) (b64_of_bits 0)

set_option doc.verso true in
/-- The Boolean tests read {lit}`SFcompare`: {lit}`SFeqb` needs {lit}`Some Eq` and
{lit}`SFltb` needs {lit}`Some Lt` ({lit}`SpecFloat.v:211-221`), while {lit}`SFleb` accepts
either, so the {lit}`None` from NaN makes all three false. Lean's {name}`Beqb`, {name}`Bltb`,
and {name}`Bleb` match on {name}`BinarySingleNaN.Bcompare` the same way.

```coq Beqb
Definition Beqb (f1 f2 : binary_float) : bool := SFeqb (B2SF f1) (B2SF f2).
```

```coq Bltb
Definition Bltb (f1 f2 : binary_float) : bool := SFltb (B2SF f1) (B2SF f2).
```

```coq Bleb
Definition Bleb (f1 f2 : binary_float) : bool := SFleb (B2SF f1) (B2SF f2).
```

```
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:223-227 *)
  Definition SFleb f1 f2 :=
    match SFcompare f1 f2 with
    | Some (Lt | Eq) => true
    | _ => false
    end.
```
-/
private def booleanComparison : List (List Bool) :=
  let positiveZero : BinarySingleNaN.binary_float 3 4 := .B754_zero false
  let negativeZero : BinarySingleNaN.binary_float 3 4 := .B754_zero true
  [negativeZero, .B754_nan].map fun y =>
    [BinarySingleNaN.Beqb positiveZero y,
     BinarySingleNaN.Bltb positiveZero y, BinarySingleNaN.Bleb positiveZero y]

set_option doc.verso true in
/-- Flocq's {coq}`b64_succ` ({lit}`Bits.v:733`) is Binary.v's {coq}`Binary.Bsucc`
({lit}`Binary.v:1392`), which applies the {coq}`BinarySingleNaN.Bsucc` below to {lit}`B2BSN x`
and lifts the result back (a proof script, not quoted). For negative {lit}`x`, {lit}`Bsucc`
rounds {lit}`x` plus half a unit in the last place toward zero: the negative number with
mantissa {lit}`xO mx - 1` (that is, {lit}`2*mx - 1`) at exponent {lit}`ex - 1`. That gives
the next float toward zero. For the smallest negative subnormal the number is
{lit}`-2^-1075`, which rounds to -0. Lean's {name}`b64_succ` ({lit}`Bits.lean`) instead
subtracts one from the 64-bit word; its agreement with {lit}`Bsucc` is tested
({lit}`FloatSpec/Test/BitOrderExecution.lean`, {lit}`scripts/fixtures/BitOrderProperties.v`),
not proven.

```coq BinarySingleNaN.Bsucc
Definition Bsucc x :=
  match x with
  | B754_zero _ => B754_finite false 1 emin Bulp_correct_aux
  | B754_infinity false => x
  | B754_infinity true => Bopp Bmax_float
  | B754_nan => B754_nan
  | B754_finite false mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode_UP false (mx + 1) ex))
  | B754_finite true mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode_ZR true (xO mx - 1) (ex - 1)))
  end.
```
-/
private def negativeTinySuccessor : Nat :=
  (bits_of_b64 (b64_succ (b64_of_bits 0x8000000000000001))).toNat

example : zeroComparison = some .eq ∧ nanComparison = none ∧
    negativeTinySuccessor = 0x8000000000000000 ∧
    booleanComparison = [[true, false, true], [false, false, false]] := by decide +kernel

/-- **5. Canonical representation.** Coq's validity check requires
`e = fexp (digits m + e)` and `e <= emax - prec`. For both (1, 0) and (4, -2),
`digits m + e` is 1, and `fexp 1` = -2 for this format (prec 3, emax 4,
emin -4), so only (4, -2) is valid. Flocq's `valid_binary_SF` is a notation for
this `valid_binary prec emax` (`Binary.v:164`); Binary.v's own `valid_binary`
(line 166) is the full-float version with NaN payloads. Lean's
`valid_binary_SF` (`Binary.lean`) makes the same check, plus `0 < m` because its
mantissa is a `Nat`, not a Coq `positive`.
```
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:36-37 *)
  Definition emin := Z.sub (Z.sub (Zpos 3) emax) prec.
  Definition fexp e := Z.max (Z.sub e prec) emin.
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:56-66 *)
    Definition canonical_mantissa m e :=
      Z.eqb (fexp (Z.add (Zpos (digits2_pos m)) e)) e.

    Definition bounded m e :=
      andb (canonical_mantissa m e) (Z.leb e (Z.sub emax prec)).

    Definition valid_binary x :=
      match x with
      | S754_finite _ m e => bounded m e
      | _ => true
      end.
```
-/
private def rawValidity : List Bool :=
  [valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 1 0),
   valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 4 (-2))]

example : rawValidity = [false, true] := by decide +kernel

/-- **6. Signed shifting.** Coq's `shr_1` drops the last bit of the magnitude:
the old round bit `r` joins the sticky bit `s`, and the dropped bit becomes the
new `r`. So it rounds toward zero for either sign: `Zneg xH` (-1) becomes `Z0`.
Lean's `(-1 : Int) / 2` is Euclidean division, which for a positive divisor is
floor division (Python's `-1 // 2`), and gives -1. Flocq's `shr_truncate`
(`BinarySingleNaN.v:1039-1044`) equates shifting with truncation only for
`0 <= m`. Lean's `shr_1` (`BinarySingleNaN.lean`) shifts negative mantissas the
same way as Coq's.
```
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:86-97 *)
    Definition shr_1 mrs :=
      let '(Build_shr_record m r s) := mrs in
      let s := orb r s in
      match m with
      | Z0 => Build_shr_record Z0 false s
      | Zpos xH => Build_shr_record Z0 true s
      | Zpos (xO p) => Build_shr_record (Zpos p) false s
      | Zpos (xI p) => Build_shr_record (Zpos p) true s
      | Zneg xH => Build_shr_record Z0 true s
      | Zneg (xO p) => Build_shr_record (Zneg p) false s
      | Zneg (xI p) => Build_shr_record (Zneg p) true s
      end.
```
-/
private def signedShiftAndFloor : List Int :=
  [(shr_1 ⟨-1, false, false⟩).shr_m, (-1 : Int) / 2]

/-- `shr_fexp` applies `shr_1` until the exponent reaches `fexp`, turning -7
into -3 and then -1 with the dropped bits above half; `mode_NA` adds one to get
0, and `binary_round_aux` (example 3) returns `S754_zero sx`, here a negative
zero. Flocq's theorems about `binary_round_aux` cover only nonnegative
mantissas: on -7, adding one moves toward zero instead of away, so the answer is
-0 rather than -0.125, the correctly rounded value of -7/64. The check is that
Lean matches Coq even outside that contract. Lean's `bsn_shr_fexp` uses this
signed shift for negative mantissas; the former Euclidean-division shortcut
returned NaN on this input.
```
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:115-122 *)
    Definition shr mrs e n :=
      match n with
      | Zpos p => (iter_pos shr_1 p mrs, Z.add e n)
      | _ => (mrs, e)
      end.

    Definition shr_fexp m e l :=
      shr (shr_record_of_loc m l) e (Z.sub (fexp (Z.add (Zdigits2 m) e)) e).
```
-/
private def rawRoundIsNegativeZero : Bool :=
  match binary_round_aux (prec := 3) (emax := 4) .RNA true (-7) (-6) .loc_Exact with
  | .S754_zero true => true
  | _ => false

example : signedShiftAndFloor = [0, -1] ∧ rawRoundIsNegativeZero = true := by
  decide +kernel

/-- **7. Conversion.** Rocq's `SF2Prim`, which Flocq's `B2Prim` uses, first
turns the integer mantissa into a machine float (`of_Z` wraps it modulo 2^63,
and Lean keeps that wrap; `of_uint63` may round), then scales it (`Z.ldexp`
clamps the exponent and `ldshiftexp` may round again); raw (3, -1) becomes the
machine float 1.5. Lean's `SF2Prim` (`PrimFloat.lean`) keeps valid inputs and
sends other finite ones through `convertRawFinite`, which takes the same two
steps; Lean's `Prim2SF` reads the stored value, where Rocq's decodes machine
bits (`FloatOps.v:37-48`).
```
(* Flocq src/IEEE754/PrimFloat.v:33-34 (7aab8f55) *)
Definition B2Prim (x : binary_float prec emax) : float :=
  SF2Prim (B2SF x).
(* Rocq V9.1.0 theories/Corelib/Floats/FloatOps.v:50-61 *)
Definition SF2Prim ef :=
  match ef with
  (* ... *)
  | S754_finite s m e =>
    let pm := of_uint63 (of_Z (Zpos m)) in
    let f := Z.ldexp pm e in
    if s then (-f)%float else f
  end.
(* Rocq V9.1.0 theories/Corelib/Floats/FloatOps.v:27-29 *)
  Definition ldexp f e :=
    let e' := Z.max (Z.min e (Z.sub emax emin)) (Z.sub (Z.sub emin emax) (Zpos 1)) in
    ldshiftexp f (of_Z (Z.add e' shift)).
```
-/
private def numericConversion : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 3 (-1))))

/-- Two roundings: `of_uint63` rounds `2^53 + 5` to `2^53 + 4` (a tie, to
even), then `Z.ldexp` hits another tie in the subnormal range and gives
`2^50*2^-1074`. -/
private def conversionDouble : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 9007199254740997 (-1077))))

/-- One rounding with Flocq's `binary_round` (example 3): the value is
`(2^50 + 5/8)*2^-1074`, above half, so the mantissa is `2^50 + 1`. -/
private def conversionSingle : List Int :=
  observe (binary_round (prec := 53) (emax := 1024) .RNE false 9007199254740997 (-1077))

example : numericConversion = [0,6755399441055744,-52] ∧
    conversionDouble = [0,1125899906842624,-1074] ∧
    conversionSingle = [0,1125899906842625,-1074] := by decide +kernel

/-- Print seven examples and fail if compiled execution disagrees with their assertions. -/
def run : IO Unit := do
  IO.println "1. Exact arithmetic: binary32 1.5 + 2.25 = 3.75."
  IO.println s!"   Result word: {sumBits} (expected 0x40700000 = 1081081856)."
  unless sumBits == 0x40700000 do throw (IO.userError "exact addition failed")
  IO.println "2. Rounding 1.125 with three bits: rows are [sign, mantissa, exponent]."
  IO.println "   Value = (-1)^sign * mantissa * 2^exponent. Modes: NE, ZR, DN, UP, NA."
  IO.println s!"   Positive: {modes false}; negative: {modes true}."
  unless modes false == [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] &&
      modes true == [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] do
    throw (IO.userError "rounding table failed")
  IO.println "3. Double rounding: 73/64 directly to three bits is 1.25; via four bits it is 1."
  IO.println s!"   Direct: {direct}; via four: {viaFour}."
  unless direct == [0,5,-2] && viaFour == [0,4,-2] do
    throw (IO.userError "double rounding witness failed")
  IO.println "4. +0 and -0 compare equal; NaN is unordered; successor of negative tiniest is -0."
  IO.println s!"   Zero comparison: {repr zeroComparison}; NaN: {repr nanComparison}."
  IO.println s!"   Boolean [=, <, <=] for +0 versus [-0, NaN]: {booleanComparison}."
  IO.println s!"   Successor word: {negativeTinySuccessor} (negative zero)."
  unless zeroComparison == some .eq && nanComparison == none &&
      negativeTinySuccessor == 0x8000000000000000 &&
      booleanComparison == [[true, false, true], [false, false, false]] do
    throw (IO.userError "special values failed")
  IO.println "5. Same real value does not mean canonical representation."
  IO.println s!"   (mantissa 1, exponent 0) versus (4, -2): validity = {rawValidity}."
  unless rawValidity == [false, true] do throw (IO.userError "raw validity failed")
  IO.println "6. Signed shifting is not floor division: shift(-1) = 0, but (-1)/2 = -1."
  IO.println s!"   [source shift, floor division] = {signedShiftAndFloor}."
  IO.println s!"   Saved raw-rounding counterexample now returns negative zero: {rawRoundIsNegativeZero}."
  IO.println "   Negative raw mantissas are outside the value theorem; the total API still follows Flocq."
  unless signedShiftAndFloor == [0, -1] && rawRoundIsNegativeZero do
    throw (IO.userError "signed raw rounding regression failed")
  IO.println "7. Numeric conversion is not validation: raw (3, -1) converts to canonical 1.5."
  IO.println s!"   Converted [sign, mantissa, exponent]: {numericConversion}."
  IO.println "   Conversion rounds the integer first, then scales; one-shot rounding can differ."
  IO.println s!"   (2^53+5)*2^-1077 converted: {conversionDouble}; one shot: {conversionSingle}."
  unless numericConversion == [0,6755399441055744,-52] &&
      conversionDouble == [0,1125899906842624,-1074] &&
      conversionSingle == [0,1125899906842625,-1074] do
    throw (IO.userError "numeric primitive conversion failed")
  IO.println "PASS: all seven compiled examples agree with their finite kernel assertions."

end GuidedDemo

def main : IO Unit := GuidedDemo.run
