import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.PrimFloat
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Run with `lake env lean --run scripts/fixtures/GuidedDemo.lean`.
Each section is a computation using the port, followed by a kernel-checked
finite assertion. These examples do not establish universal conformance.

Each section's docstring (hover its first definition) cites the Flocq source it exercises,
linked to the pinned commit, and sections 1, 2, 4, 5, and 6 quote the Rocq text. Sections 3
and 7 link whole files: their material is unanchored or belongs to Rocq's own float spec.
The citations are checked: `{coq}` fails to elaborate unless it names a pinned anchor, and
`scripts/validate_flocq_source_refs.py` compares every quote verbatim with the pinned
checkout. -/

namespace GuidedDemo

private def observe : StandardFloat → List Int
  | .S754_finite sign mantissa exponent => [if sign then 1 else 0, mantissa, exponent]
  | _ => []

set_option doc.verso true in
/--
Section 1, exact arithmetic: binary32 {lit}`1.5 + 2.25 = 3.75`. The port's {name}`b32_plus` is
Flocq's {coq}`b32_plus`, generic addition instantiated at binary32:

```coq b32_plus
Definition b32_plus :  mode -> binary32 -> binary32 -> binary32 := Bplus  _ _ Hprec Hprec_emax binop_nan_pl32.
```
-/
private def sumBits : Nat :=
  (bits_of_b32 (b32_plus .RNE (b32_of_bits 0x3fc00000) (b32_of_bits 0x40100000))).toNat

example : sumBits = 0x40700000 := by decide +kernel

set_option doc.verso true in
/--
Section 2, rounding modes: with three significant bits, {lit}`1.125` lies halfway between
{lit}`1` and {lit}`1.25`, so the modes disagree. {name}`binary_round` is the executable carrier
of Flocq's {coq}`BinarySingleNaN.binary_round`, which aligns the mantissa and then rounds with
{coq}`BinarySingleNaN.binary_round_aux` (quoted with section 6):

```coq BinarySingleNaN.binary_round
Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx (Zpos mz) ez loc_Exact.
```
-/
private def modes (sign : Bool) : List (List Int) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].map fun mode =>
    observe (binary_round (prec := 3) (emax := 4) mode sign 9 (-3))

example : modes false = [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] ∧
    modes true = [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] := by
  decide +kernel

set_option doc.verso true in
/--
Section 3, double rounding: {lit}`73/64` rounds directly to {lit}`1.25` at three bits, but to
{lit}`1` through four bits, because the intermediate result is a midpoint. This refutes only the
unconditional equation. The theorems in {coq_file}`src/Prop/Double_rounding.v` are conditional;
for products, for instance, they assume {lit}`2 * prec <= prec'`, which three and four bits fail.
-/
private def direct : List Int :=
  observe (binary_round (prec := 3) (emax := 10) .RNE false 73 (-6))

private def viaFour : List Int :=
  match binary_round (prec := 4) (emax := 10) .RNE false 73 (-6) with
  | .S754_finite sign mantissa exponent =>
      observe (binary_round (prec := 3) (emax := 10) .RNE sign mantissa exponent)
  | _ => []

example : direct = [0,5,-2] ∧ viaFour = [0,4,-2] := by decide +kernel

set_option doc.verso true in
/--
Section 4, comparison: {coq}`b64_compare` is Flocq's comparison at binary64. It bottoms out in
{coq}`BinarySingleNaN.Bcompare`, which answers {lit}`None` when the inputs are unordered, and
its correctness theorem speaks only about finite inputs:

```coq b64_compare
Definition b64_compare : binary64 -> binary64 -> option comparison := Bcompare 53 1024.
```

```coq BinarySingleNaN.Bcompare
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  SFcompare (B2SF f1) (B2SF f2).
```

```coq BinarySingleNaN.Bcompare_correct
Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
```
-/
private def zeroComparison : Option Ordering :=
  b64_compare (b64_of_bits 0) (b64_of_bits 0x8000000000000000)

private def nanComparison : Option Ordering :=
  b64_compare (b64_of_bits 0x7ff8000000000000) (b64_of_bits 0)

set_option doc.verso true in
/--
The Boolean views {coq}`Beqb`, {coq}`Bltb`, and {coq}`Bleb` read the same raw comparison, so a
NaN operand makes all three false instead of collapsing into equality:

```coq Beqb
Definition Beqb (f1 f2 : binary_float) : bool := SFeqb (B2SF f1) (B2SF f2).
```

```coq Bltb
Definition Bltb (f1 f2 : binary_float) : bool := SFltb (B2SF f1) (B2SF f2).
```

```coq Bleb
Definition Bleb (f1 f2 : binary_float) : bool := SFleb (B2SF f1) (B2SF f2).
```
-/
private def booleanComparison : List (List Bool) :=
  let positiveZero : BinarySingleNaN.binary_float 3 4 := .B754_zero false
  let negativeZero : BinarySingleNaN.binary_float 3 4 := .B754_zero true
  [negativeZero, .B754_nan].map fun y =>
    [BinarySingleNaN.Beqb positiveZero y,
     BinarySingleNaN.Bltb positiveZero y, BinarySingleNaN.Bleb positiveZero y]

set_option doc.verso true in
/--
{coq}`b64_succ` is Flocq's successor at binary64; its binary64 wrapper lifts the SingleNaN
{coq}`Binary.BsuccSingle`. For a negative finite input it rounds {lit}`2m - 1` at exponent
{lit}`e - 1` toward zero, so the successor of the negative tiniest subnormal is negative zero:

```coq b64_succ
Definition b64_succ : binary64 -> binary64 := Bsucc _ _ Hprec Hprec_emax.
```

```coq Binary.BsuccSingle
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

set_option doc.verso true in
/--
Section 5, validity: the raw pairs {lit}`(1, 0)` and {lit}`(4, -2)` both denote one, but only the
second is canonical at three-bit precision. {name}`valid_binary_SF` is the Rocq
{lit}`SpecFloat` check; Flocq's full-float {coq}`valid_binary` has the same finite case,
{lit}`bounded m e`, which demands the canonical exponent, not just a range check:

```coq valid_binary
Definition valid_binary x :=
  match x with
  | F754_finite _ m e => bounded m e
  | F754_nan _ pl => nan_pl pl
  | _ => true
  end.
```
-/
private def rawValidity : List Bool :=
  [valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 1 0),
   valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 4 (-2))]

example : rawValidity = [false, true] := by decide +kernel

set_option doc.verso true in
/--
Section 6, signed shifting: the Rocq {lit}`SpecFloat.shr_1` step behind {name}`shr_1` drops the
last bit of the magnitude and keeps the sign, so it shifts {lit}`-1` to {lit}`0`, whereas floor
division gives {lit}`-1`. Flocq's {coq}`BinarySingleNaN.binary_round_aux` shifts, rounds by
mode, shifts again, and returns {lit}`S754_zero sx` when the mantissa reaches zero. So the saved
raw input with sign {lit}`true`, mantissa {lit}`-7`, and exponent {lit}`-6`, rounded with ties
away from zero, yields negative zero:

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
private def signedShiftAndFloor : List Int :=
  [(shr_1 ⟨-1, false, false⟩).shr_m, (-1 : Int) / 2]

private def rawRoundIsNegativeZero : Bool :=
  match binary_round_aux (prec := 3) (emax := 4) .RNA true (-7) (-6) .loc_Exact with
  | .S754_zero true => true
  | _ => false

example : signedShiftAndFloor = [0, -1] ∧ rawRoundIsNegativeZero = true := by
  decide +kernel

set_option doc.verso true in
/--
Section 7, conversion: {name}`FaithfulPrimFloat.Prim2SF` and {name}`FaithfulPrimFloat.SF2Prim`
port Rocq's primitive-float specification rather than a Flocq definition; Flocq connects
primitive floats to its own formats in {coq_file}`src/IEEE754/PrimFloat.v`. Conversion is not
validation: the noncanonical raw pair {lit}`(3, -1)` comes back as canonical {lit}`1.5`.
-/
private def numericConversion : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 3 (-1))))

private def conversionDouble : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 9007199254740997 (-1077))))

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
