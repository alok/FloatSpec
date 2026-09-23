import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.PrimFloat

/-! Run with `lake env lean --run scripts/fixtures/GuidedDemo.lean`.
Each section is a computation using the port, followed by a kernel-checked
finite assertion. These examples do not establish universal conformance.

Each computation's doc comment quotes the Coq that decides its answer, from
Flocq at the pinned commit 7aab8f55. Flocq takes some definitions, such as
`shr_1`, `SFcompare`, `valid_binary`, and `SF2Prim`, from the Rocq core library;
those are quoted from Rocq V9.1.0, the prover that builds the pinned reference.
Quotes are verbatim: a `(* Flocq file:lines *)` or `(* Rocq file:lines *)` line
gives the location, and `(* ... *)` marks omitted lines. A row
`[sign, mantissa, exponent]` means `(-1)^sign * mantissa * 2^exponent`. -/

namespace GuidedDemo

private def observe : StandardFloat → List Int
  | .S754_finite sign mantissa exponent => [if sign then 1 else 0, mantissa, exponent]
  | _ => []

/-- **1. Exact arithmetic.** Coq adds two finite floats by lining up their
integer mantissas at the smaller exponent, adding the integers, and rounding
once; 3.75 fits in 24 bits, so nothing is rounded away. Lean's `b32_plus`
reaches the same finite branch in `Binary.Bplus` (`BinarySingleNaN.lean`).
```coq
(* Flocq src/IEEE754/Bits.v:669 (7aab8f55) *)
Definition b32_plus :  mode -> binary32 -> binary32 -> binary32 := Bplus  _ _ Hprec Hprec_emax binop_nan_pl32.
(* Flocq src/IEEE754/Binary.v:1049-1050 (7aab8f55) *)
Definition Bplus plus_nan m x y :=
  BSN2B (plus_nan x y) (Bplus m (B2BSN x) (B2BSN y)).
(* Flocq src/IEEE754/BinarySingleNaN.v:1940-1955 (7aab8f55) *)
Definition Bplus m x y :=
  match x, y with
  (* ... *)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Fplus_naive sx mx ex sy my ey ez)
      ez (match m with mode_DN => true | _ => false end)
  end.
(* Flocq src/IEEE754/BinarySingleNaN.v:1837-1838 (7aab8f55) *)
Definition Fplus_naive sx mx ex sy my ey ez :=
  (Zplus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))).
```
-/
private def sumBits : Nat :=
  (bits_of_b32 (b32_plus .RNE (b32_of_bits 0x3fc00000) (b32_of_bits 0x40100000))).toNat

example : sumBits = 0x40700000 := by decide +kernel

/-- **2. Rounding modes.** At three bits, `binary_round` (example 3) truncates
1.125 to mantissa 4 with a dropped part of exactly half, and Coq's `choice_mode`
decides whether to add one (`cond_incr b m` adds one when `b` is true): NE only
if 4 were odd, NA always, ZR never, DN only for a negative number, UP only for a
positive one. Lean's `.RNE .RTZ .RTN .RTP .RNA` are Coq's
`mode_NE mode_ZR mode_DN mode_UP mode_NA`, and Lean's `choice_mode`
(`BinarySingleNaN.lean`) has the same five branches.
```coq
(* Flocq src/IEEE754/BinarySingleNaN.v:1140-1147 (7aab8f55) *)
Definition choice_mode m sx mx lx :=
  match m with
  | mode_NE => cond_incr (round_N (negb (Z.even mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx
  end.
(* Flocq src/Calc/Round.v:180-184 (7aab8f55) *)
Definition round_sign_DN s l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.
(* Flocq src/Calc/Round.v:273-277 (7aab8f55) *)
Definition round_sign_UP s l :=
  match l with
  | loc_Exact => false
  | _ => negb s
  end.
```
-/
private def modes (sign : Bool) : List (List Int) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].map fun mode =>
    observe (binary_round (prec := 3) (emax := 4) mode sign 9 (-3))

example : modes false = [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] ∧
    modes true = [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] := by
  decide +kernel

/-- **3. Double rounding.** Coq's `binary_round` shifts the mantissa down to the
precision, rounds it with `choice_mode`, and renormalizes; under NE, `round_N`
rounds up above half and breaks an exact half toward an even mantissa. Directly,
73*2^-6 (73 = 1001001 in binary) drops 1001, above half, so it rounds up to
5*2^-2 = 1.25. Lean's `binary_round` and `binary_round_aux`
(`BinarySingleNaN.lean`) follow these lines.
```coq
(* Flocq src/IEEE754/BinarySingleNaN.v:1701-1702 (7aab8f55) *)
Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx (Zpos mz) ez loc_Exact.
(* Flocq src/IEEE754/BinarySingleNaN.v:1270-1277 (7aab8f55) *)
Definition binary_round_aux mode sx mx ex lx :=
  let '(mrs', e') := shr_fexp mx ex lx in
  let '(mrs'', e'') := shr_fexp (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
  match shr_m mrs'' with
  | Z0 => S754_zero sx
  | Zpos m => binary_fit_aux mode sx m e''
  | _ => S754_nan
  end.
(* Flocq src/Calc/Round.v:415-421 (7aab8f55) *)
Definition round_N (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => p
  | loc_Inexact Gt => true
  end.
```
-/
private def direct : List Int :=
  observe (binary_round (prec := 3) (emax := 10) .RNE false 73 (-6))

/-- Rounding to four bits first drops 001 (below half) and gives 9*2^-3 = 1.125,
an exact half at three bits, which NE breaks toward the even mantissa 4, so 1. -/
private def viaFour : List Int :=
  match binary_round (prec := 4) (emax := 10) .RNE false 73 (-6) with
  | .S754_finite sign mantissa exponent =>
      observe (binary_round (prec := 3) (emax := 10) .RNE sign mantissa exponent)
  | _ => []

example : direct = [0,5,-2] ∧ viaFour = [0,4,-2] := by decide +kernel

/-- **4. Signed zero, NaN, successor.** Coq compares through `SFcompare`, whose
zero row answers `Some Eq` whatever the signs and whose NaN row answers `None`
(unordered). Lean's `b64_compare` reaches `BinarySingleNaN.Bcompare`
(`BinarySingleNaN.lean`), which has the same rows, written `some .eq` and `none`.
```coq
(* Flocq src/IEEE754/Bits.v:743 (7aab8f55) *)
Definition b64_compare : binary64 -> binary64 -> option comparison := Bcompare 53 1024.
(* Flocq src/IEEE754/Binary.v:773-774 (7aab8f55) *)
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2).
(* Flocq src/IEEE754/BinarySingleNaN.v:559-560 (7aab8f55) *)
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  SFcompare (B2SF f1) (B2SF f2).
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

/-- The Boolean tests read `SFcompare`: `=` needs `Some Eq`, `<` needs
`Some Lt`, and `<=` accepts either, so the `None` from NaN makes all three
false. Lean's `Beqb`, `Bltb`, and `Bleb` match on `Bcompare` the same way.
```coq
(* Flocq src/IEEE754/BinarySingleNaN.v:628, 652, 666 (7aab8f55) *)
Definition Beqb (f1 f2 : binary_float) : bool := SFeqb (B2SF f1) (B2SF f2).
Definition Bltb (f1 f2 : binary_float) : bool := SFltb (B2SF f1) (B2SF f2).
Definition Bleb (f1 f2 : binary_float) : bool := SFleb (B2SF f1) (B2SF f2).
(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:211-227 *)
  Definition SFeqb f1 f2 :=
    match SFcompare f1 f2 with
    | Some Eq => true
    | _ => false
    end.

  Definition SFltb f1 f2 :=
    match SFcompare f1 f2 with
    | Some Lt => true
    | _ => false
    end.

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

/-- Coq's `Bsucc` moves a negative number toward zero by rounding `xO mx - 1`
(that is, 2*mx - 1) at exponent `ex - 1` toward zero; `SF2B _ (proj1 ...)` takes
`binary_round`'s result together with its validity proof. For the smallest
negative subnormal the value is 2^-1075, which rounds to zero and keeps the minus
sign. Lean's `b64_succ` (`Bits.lean`) instead subtracts one from the 64-bit
word; its agreement with `Bsucc` is tested
(`FloatSpec/Test/BitOrderExecution.lean`,
`scripts/fixtures/BitOrderProperties.v`), not proven.
```coq
(* Flocq src/IEEE754/Bits.v:733 (7aab8f55) *)
Definition b64_succ : binary64 -> binary64 := Bsucc _ _ Hprec Hprec_emax.
(* Flocq src/IEEE754/BinarySingleNaN.v:3242-3252 (7aab8f55) *)
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

/-- **5. Canonical representation.** Coq's validity check requires the exponent
to be exactly the one `fexp` assigns to a number with that many digits, so the
value 1 is valid as (4, -2) but not as (1, 0), since fexp 1 = -2 for this
format. Lean's `valid_binary_SF` (`Binary.lean`) makes the same check, plus
`0 < m` because its mantissa is a `Nat`, not a Coq `positive`.
```coq
(* Flocq src/IEEE754/Binary.v:164 (7aab8f55) *)
Notation valid_binary_SF := (valid_binary prec emax).
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

/-- **6. Signed shifting.** Coq's `shr_1` drops the last bit of the magnitude,
so it rounds toward zero for either sign (`Zneg xH` becomes `Z0`), while Lean's
`(-1 : Int) / 2` is Euclidean division and gives -1; Flocq's `shr_truncate`
equates shifting with truncation only for `0 <= m`. Lean's `shr_1`
(`BinarySingleNaN.lean`) shifts negative mantissas the same way as Coq's.
```coq
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
(* Flocq src/IEEE754/BinarySingleNaN.v:1039-1044 (7aab8f55) *)
Theorem shr_truncate :
  forall f m e l,
  Valid_exp f ->
  (0 <= m)%Z ->
  shr (shr_record_of_loc m l) e (f (Zdigits2 m + e) - e)%Z =
  let '(m', e', l') := truncate radix2 f (m, e, l) in (shr_record_of_loc m' l', e').
```
-/
private def signedShiftAndFloor : List Int :=
  [(shr_1 ⟨-1, false, false⟩).shr_m, (-1 : Int) / 2]

/-- `shr_fexp` applies `shr_1` until the exponent reaches `fexp`, turning -7
into -1 with the dropped bits above half; `mode_NA` adds one to get 0, and
`binary_round_aux` (example 3) returns `S754_zero sx`, here a negative zero.
Lean's `bsn_shr_fexp` uses this signed shift for negative mantissas; the former
Euclidean-division shortcut returned NaN on this input.
```coq
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

/-- **7. Conversion.** Rocq's `SF2Prim`, which Flocq's `B2Prim` uses, first turns
the integer mantissa into a machine float (`of_uint63`, which may round) and
then scales it (`Z.ldexp`, which may round again); raw (3, -1) becomes the
machine float 1.5. Lean's `SF2Prim` (`PrimFloat.lean`) keeps valid inputs and
sends other finite ones through `convertRawFinite`, which takes the same two
steps; Lean's `Prim2SF` reads the stored value, where Rocq's decodes machine
bits (`FloatOps.v:37-48`).
```coq
(* Flocq src/IEEE754/PrimFloat.v:33-34 (7aab8f55) *)
Definition B2Prim (x : binary_float prec emax) : float :=
  SF2Prim (B2SF x).
(* Rocq V9.1.0 theories/Corelib/Floats/FloatOps.v:50-61 *)
Definition SF2Prim ef :=
  match ef with
  | S754_nan => nan
  | S754_zero false => zero
  | S754_zero true => neg_zero
  | S754_infinity false => infinity
  | S754_infinity true => neg_infinity
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

/-- Two roundings: `of_uint63` rounds 2^53 + 5 to 2^53 + 4 (a tie, to even),
then `Z.ldexp` hits another tie in the subnormal range and gives 2^50*2^-1074. -/
private def conversionDouble : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 9007199254740997 (-1077))))

/-- One rounding with Flocq's `binary_round` (example 3): the value is
(2^50 + 5/8)*2^-1074, above half, so the mantissa is 2^50 + 1. -/
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
