import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
import FloatSpec.src.Core.Round_pred

/-! # Source surface regressions

Flocq's declarations are exported under their Coq names and with their Coq
shapes. The last section checks that each anchored `Binary.v` operation is
the `BinarySingleNaN` operation lifted through `BSN2B`, which is how
`Binary.v` defines it. -/

/-! Coq exports `Rnd_NG_pt_unique_prop` over a Type-valued tie payload. -/

example : Prop :=
  FloatSpec.Core.Round_pred.Rnd_NG_pt_unique_prop
    (fun _ : ℝ => True) (fun _ _ : ℝ => Nat)

/-! The source arithmetic contracts are exported under their exact Flocq names. -/

#check @Bplus_correct
#check @Bmult_correct
#check @Bminus_correct
#check @Bfma_correct
#check @Bdiv_correct
#check @Bsqrt_correct

/-! The complete FLoCq `Binary` surface is published on the proof-carrying
carrier.  These checks deliberately use the qualified source namespace so a
wider `Binary754` compatibility declaration cannot satisfy the regression. -/

#check @Binary.B2SF_B2BSN
#check @Binary.B2R_B2BSN
#check @Binary.B2SF_FF2B
#check @Binary.FF2SF_B2FF
#check @Binary.B2FF_FF2B
#check @Binary.FF2B_B2FF
#check @Binary.FF2B_B2FF_valid
#check @Binary.B2R_FF2B
#check @Binary.B2R_inj
#check @Binary.B2R_Bsign_inj
#check @Binary.Bcompare_correct
#check @Binary.Bnearbyint_correct
#check @Binary.Btrunc_correct
#check @Binary.Bone_correct
#check @Binary.Bldexp_correct
#check @Binary.Bfrexp
#check @Binary.Bfrexp_correct

example :
    @Binary.Bfrexp 1 2 ⟨by omega⟩ (binary_float.B754_zero false) =
      (binary_float.B754_zero false, -5) := by
  rfl

example :
    let x : binary_float 3 10 := binary_float.B754_finite false
      (FloatSpec.Core.Zaux.Positive.xO
        (FloatSpec.Core.Zaux.Positive.xO FloatSpec.Core.Zaux.Positive.xH))
      (-2) (by decide)
    (Binary.B2R (@Binary.Bfrexp 3 10 ⟨by omega⟩ x).1,
      (@Binary.Bfrexp 3 10 ⟨by omega⟩ x).2) =
      ((1 / 2 : Real), 1) := by
  simp only
  apply Prod.ext
  · simp only [Prod.fst]
    unfold Binary.Bfrexp
    rw [Binary.B2R_lift]
    simp only [Binary.B2BSN, binaryFloatToBinarySingleNaNFloat]
    unfold Binary.BfrexpSingle
    rw [Binary.B2R_standardFloatToBinarySingleNaNFloat]
    norm_num [Binary.Bfrexp, Binary.BfrexpSingle,
      ExperimentalSingleNaNArithmetic.Ffrexp_core_binary,
      Binary.B2BSN, binaryFloatToBinarySingleNaNFloat,
      binarySingleNaNFloatToB754, standardFloatToBinarySingleNaNFloat,
      B754_to_R, SF2R, F2R, FloatSpec.Core.Defs.F2R,
      FloatSpec.Core.Zaux.positiveToNat, FloatSpec.Core.Zaux.Zlt_bool,
      FloatSpec.Core.Digits.digits2_pos, FloatSpec.Core.Digits.digits2_Pnat,
      FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload]
  · simp only [Prod.snd]
    norm_num [Binary.Bfrexp, Binary.BfrexpSingle,
      ExperimentalSingleNaNArithmetic.Ffrexp_core_binary,
      Binary.B2BSN, binaryFloatToBinarySingleNaNFloat,
      FloatSpec.Core.Zaux.positiveToNat, FloatSpec.Core.Zaux.Zlt_bool,
      FloatSpec.Core.Digits.digits2_pos, FloatSpec.Core.Digits.digits2_Pnat,
      FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload]
#check @Bulp_correct
#check @Binary.Bsucc_correct
#check @Binary.Bpred_correct
#check @Binary.binary_round_aux_correct
#check @Binary.binary_round_correct
#check @Binary.binary_normalize_correct
#check @Binary.shl_align_fexp_correct
#check @Binary.eq_binary_overflow_FF2SF
#check @Beqb
#check @Beqb_correct
#check @Beqb_refl
#check @Bltb
#check @Bltb_correct
#check @Bleb
#check @Bleb_correct
#check @canonical_canonical_mantissa
#check @generic_format_B2R
#check @FLT_format_B2R
#check @BinarySingleNaN.binary_float
#check @BinarySingleNaN.B2R
#check @BinarySingleNaN.Beqb_correct
#check @BinarySingleNaN.Bltb_correct
#check @BinarySingleNaN.Bleb_correct
#check @BinarySingleNaN.generic_format_B2R
#check @BinarySingleNaN.FLT_format_B2R
#check @BinarySingleNaN.Bopp
#check @BinarySingleNaN.Bopp_involutive
#check @BinarySingleNaN.B2R_Bopp
#check @BinarySingleNaN.is_nan_Bopp
#check @BinarySingleNaN.is_finite_Bopp
#check @BinarySingleNaN.is_finite_strict_Bopp
#check @BinarySingleNaN.Bsign_Bopp
#check @BinarySingleNaN.Bmult
#check @BinarySingleNaN.Bmult_correct
#check @BinarySingleNaN.Bplus
#check @BinarySingleNaN.Bplus_correct
#check @BinarySingleNaN.Bminus
#check @BinarySingleNaN.Bminus_correct
#check @BinarySingleNaN.Bfma
#check @BinarySingleNaN.Bfma_correct
#check @BinarySingleNaN.Bdiv
#check @BinarySingleNaN.Bdiv_correct
#check @BinarySingleNaN.Bsqrt
#check @BinarySingleNaN.Bsqrt_correct_aux
#check @BinarySingleNaN.Bsqrt_correct
#check @BinarySingleNaN.erase
#check @BinarySingleNaN.erase_correct
#check @BinarySingleNaN.Babs
#check @BinarySingleNaN.B2R_Babs
#check @BinarySingleNaN.Bcompare
#check @BinarySingleNaN.Bcompare_correct
#check @BinarySingleNaN.bounded_le_emax_minus_prec
#check @BinarySingleNaN.abs_B2R_lt_emax
#check @BinarySingleNaN.binary_round_aux
#check @BinarySingleNaN.binary_round_aux_correct'
#check @BinarySingleNaN.binary_round_aux_correct
#check @BinarySingleNaN.binary_round
#check @BinarySingleNaN.binary_round_correct
#check @BinarySingleNaN.is_nan_binary_round
#check @BinarySingleNaN.binary_normalize
#check @BinarySingleNaN.binary_normalize_correct
#check @BinarySingleNaN.Bnearbyint
#check @BinarySingleNaN.Bnearbyint_correct
#check @BinarySingleNaN.Bnearbyint_correct_aux
#check @BinarySingleNaN.sign_plus_overflow
#check @BinarySingleNaN.Btrunc
#check @BinarySingleNaN.Btrunc_correct
#check @BinarySingleNaN.Bone
#check @BinarySingleNaN.Bone_correct
#check @BinarySingleNaN.Bmax_float
#check @BinarySingleNaN.Bnormfr_mantissa
#check @BinarySingleNaN.Bldexp
#check @BinarySingleNaN.Bldexp_correct
#check @BinarySingleNaN.Bfrexp
#check @BinarySingleNaN.Bfrexp_correct

example :
    @BinarySingleNaN.Bfrexp 1 1 ⟨by omega⟩
        (BinarySingleNaNFloat.B754_zero false) =
      (BinarySingleNaNFloat.B754_zero false, -3) := by
  rfl

example :
    @BinarySingleNaN.Bnearbyint 0 1 ⟨by omega⟩ RoundingMode.RNE
        (BinarySingleNaNFloat.B754_zero false) =
      BinarySingleNaNFloat.B754_zero false := by
  rfl

example :
    is_nan_SF (@BinarySingleNaN.binary_overflow 0 0 RoundingMode.RNE false) = false :=
  @BinarySingleNaN.is_nan_binary_overflow 0 0 RoundingMode.RNE false
#check @BinarySingleNaN.Bulp
#check @BinarySingleNaN.Bulp_correct
#check @BinarySingleNaN.Bulp'
#check @BinarySingleNaN.Bulp'_correct
#check @BinarySingleNaN.Bsucc
#check @BinarySingleNaN.Bsucc_correct
#check @BinarySingleNaN.Bpred
#check @BinarySingleNaN.Bpred_correct
#check @BinarySingleNaN.Bpred_pos'
#check @BinarySingleNaN.Bpred_pos'_correct
#check @BinarySingleNaN.Bsucc'
#check @BinarySingleNaN.Bsucc'_correct

/-- `Binary.B2FF` preserves the sign and payload of a source-valid NaN. -/
example (prec emax : Int) (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl prec p = true) :
    Binary.B2FF (prec := prec) (emax := emax)
        (binary_float.B754_nan true p hp) =
      FullFloat.F754_nan true (FloatSpec.Core.Zaux.positiveToNat p) := rfl

/-- Source `Bopp` and `Babs` must invoke the supplied NaN handler. -/
example (prec emax : Int) (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl prec p = true) :
    let nan := binary_float.B754_nan (prec:=prec) (emax:=emax) true p hp
    let choosePositive : Binary.BoppNaNHandler prec emax := fun _ =>
      ⟨binary_float.B754_nan false p hp, rfl⟩
    Binary.Bopp choosePositive nan = binary_float.B754_nan false p hp := rfl

example (prec emax : Int) (p : FloatSpec.Core.Zaux.Positive)
    (hp : nan_pl prec p = true) :
    let source := full_float.F754_nan true p
    Binary.B2FF_exact (Binary.FF2B (prec:=prec) (emax:=emax) source hp) = source := rfl

/-! Overflow is part of the observable source semantics.  These examples guard
the finite RTZ branch and both directions of sign-sensitive rounding. -/

example : binary_overflow 3 10 RoundingMode.RTZ false =
    FullFloat.F754_finite false 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RNE true =
    FullFloat.F754_infinity true := rfl
example : binary_overflow 3 10 RoundingMode.RTP false =
    FullFloat.F754_infinity false := rfl
example : binary_overflow 3 10 RoundingMode.RTP true =
    FullFloat.F754_finite true 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RTN false =
    FullFloat.F754_finite false 7 7 := rfl
example : binary_overflow 3 10 RoundingMode.RTN true =
    FullFloat.F754_infinity true := rfl

/-! The exact SingleNaN sign theorem includes the NaN case, matching the
source theorem's unrestricted quantification. -/

example {prec emax : Int} :
    BinarySingleNaN.Bsign
        (@BinarySingleNaN.SF2B prec emax StandardFloat.S754_nan rfl) =
      sign_SF StandardFloat.S754_nan :=
  @BinarySingleNaN.Bsign_SF2B prec emax StandardFloat.S754_nan rfl

/-! Coq's `comparison` is represented by `Ordering`; NaN remains unordered. -/

example :
    @BinarySingleNaN.Bcompare 1 1 BinarySingleNaNFloat.B754_nan
      (BinarySingleNaNFloat.B754_zero false) = none := by
  rfl

/-! These function-type checks fail if an internal `Valid_exp` or
`Monotone_exp` proof leaks into the source-facing arithmetic signatures. -/

section

namespace FloatSpec.IEEE754.BinarySingleNaN.Source

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bmult prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bplus prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bminus prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bfma prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bdiv prec emax _ _

example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    mode → _root_.BinarySingleNaN.binary_float prec emax →
      _root_.BinarySingleNaN.binary_float prec emax :=
  @Bsqrt prec emax _ _

#check @Bmult_correct
#check @Bplus_correct
#check @Bminus_correct
#check @Bfma_correct
#check @Bdiv_correct
#check @Bsqrt_correct_aux
#check @Bsqrt_correct

end FloatSpec.IEEE754.BinarySingleNaN.Source

end

/-! Each `Binary.v` operation below is defined in Coq as the `BinarySingleNaN`
operation on the `B2BSN` images, lifted back with `BSN2B` (with the caller's
NaN) or `BSN2B'`. The Lean definitions are direct transcriptions, and these
equalities hold for every input, including every NaN, zero and infinity
case. -/

section BinaryLift

private theorem binaryPositiveOfNat_positiveToNat (p : FloatSpec.Core.Zaux.Positive)
    (h : 0 < FloatSpec.Core.Zaux.positiveToNat p) :
    binaryPositiveOfNat (FloatSpec.Core.Zaux.positiveToNat p) h = p :=
  FloatSpec.Core.Zaux.positiveToNat_injective (binaryPositiveOfNat_spec _ _)

private theorem BSN2B_B2BSN_of_not_nan {prec emax : Int}
    (nan : {x : binary_float prec emax // Binary.is_nan x = true})
    (x : binary_float prec emax) (hx : Binary.is_nan x = false) :
    Binary.BSN2B nan (Binary.B2BSN x) = x := by
  cases x with
  | B754_nan s pl h => simp [Binary.is_nan] at hx
  | B754_finite s m e h =>
      simp [Binary.BSN2B, Binary.B2BSN, binaryFloatToBinarySingleNaNFloat,
        binaryPositiveOfNat_positiveToNat]
  | _ => rfl

private theorem is_nan_standardFloatToBinaryFloatOfNotNaN {prec emax : Int}
    (z : StandardFloat)
    (h₁ : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true)
    (h₂ : is_nan_SF z = false) :
    Binary.is_nan (Binary.standardFloatToBinaryFloatOfNotNaN z h₁ h₂) = false := by
  cases z with
  | S754_nan => simp [is_nan_SF] at h₂
  | _ => rfl

private theorem is_nan_normalize {prec emax : Int}
    [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (m e : Int) (szero : Bool) :
    Binary.is_nan (Binary.normalize (prec:=prec) (emax:=emax) mode m e szero) =
      false := by
  unfold Binary.normalize
  split_ifs
  · rfl
  · exact is_nan_standardFloatToBinaryFloatOfNotNaN _ _ _
  · exact is_nan_standardFloatToBinaryFloatOfNotNaN _ _ _

private theorem BSN2B_standardFloat {prec emax : Int}
    (nan : {x : binary_float prec emax // Binary.is_nan x = true})
    (z : StandardFloat)
    (h₁ : validBinarySingleNaNStandardFloat (prec:=prec) (emax:=emax) z = true)
    (h₂ : is_nan_SF z = false) :
    Binary.BSN2B nan (standardFloatToBinarySingleNaNFloat z h₁) =
      Binary.standardFloatToBinaryFloatOfNotNaN z h₁ h₂ := by
  cases z with
  | S754_nan => simp [is_nan_SF] at h₂
  | _ => rfl

-- Binary.v:947
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mult_nan : Binary.BmultNaNHandler prec emax) (m : RoundingMode)
    (x y : binary_float prec emax) :
    Binary.Bmult mult_nan m x y =
      Binary.BSN2B (mult_nan x y)
        (BinarySingleNaN.Bmult m (Binary.B2BSN x) (Binary.B2BSN y)) := by
  cases x <;> cases y
  case B754_finite.B754_finite => exact (BSN2B_standardFloat _ _ _ _).symm
  all_goals
    simp [Binary.Bmult, BinarySingleNaN.Bmult, Binary.BSN2B, Binary.B2BSN,
      binaryFloatToBinarySingleNaNFloat, Binary.build_nan]

-- Binary.v:1049
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (plus_nan : Binary.BplusNaNHandler prec emax) (m : RoundingMode)
    (x y : binary_float prec emax) :
    Binary.Bplus plus_nan m x y =
      Binary.BSN2B (plus_nan x y)
        (BinarySingleNaN.Bplus m (Binary.B2BSN x) (Binary.B2BSN y)) := by
  cases x <;> cases y
  case B754_finite.B754_finite =>
    exact (BSN2B_B2BSN_of_not_nan _ _ (is_nan_normalize _ _ _ _)).symm
  all_goals
    simp [Binary.Bplus, BinarySingleNaN.Bplus, Binary.BSN2B, Binary.B2BSN,
      binaryFloatToBinarySingleNaNFloat, Binary.build_nan,
      binaryPositiveOfNat_positiveToNat]
  all_goals first | done | (split_ifs <;> (try cases m) <;> rfl)

-- Binary.v:1086
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (minus_nan : Binary.BminusNaNHandler prec emax) (m : RoundingMode)
    (x y : binary_float prec emax) :
    Binary.Bminus minus_nan m x y =
      Binary.BSN2B (minus_nan x y)
        (BinarySingleNaN.Bminus m (Binary.B2BSN x) (Binary.B2BSN y)) := by
  cases x <;> cases y
  case B754_finite.B754_finite =>
    exact (BSN2B_B2BSN_of_not_nan _ _ (is_nan_normalize _ _ _ _)).symm
  all_goals
    simp [Binary.Bminus, BinarySingleNaN.Bminus, BinarySingleNaN.Bplus,
      BinarySingleNaN.Bopp, Binary.Bopp_preserve_nan, Binary.BSN2B, Binary.B2BSN,
      binaryFloatToBinarySingleNaNFloat, Binary.build_nan,
      binaryPositiveOfNat_positiveToNat]
  all_goals first | done | (split_ifs <;> (try cases m) <;> rfl)

-- Binary.v:1123
example {prec emax : Int} (m : RoundingMode) (x y z : binary_float prec emax) :
    Binary.Bfma_szero m x y z =
      BinarySingleNaN.Bfma_szero m (Binary.B2BSN x) (Binary.B2BSN y)
        (Binary.B2BSN z) :=
  rfl

/-- `B2BSN` forgets a NaN's sign, so `Bfma_szero` reads a negative NaN as
positive, as Coq's `Binary.Bfma_szero` does. -/
example :
    Binary.Bfma_szero (prec:=53) (emax:=1024) RoundingMode.RNE
      (binary_float.B754_nan true .xH (by decide +kernel))
      (binary_float.B754_zero false) (binary_float.B754_zero true) = false :=
  rfl

-- Binary.v:1126
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (fma_nan : Binary.BfmaNaNHandler prec emax) (m : RoundingMode)
    (x y z : binary_float prec emax) :
    Binary.Bfma fma_nan m x y z =
      Binary.BSN2B (fma_nan x y z)
        (BinarySingleNaN.Bfma m (Binary.B2BSN x) (Binary.B2BSN y)
          (Binary.B2BSN z)) := by
  cases x <;> cases y <;> cases z
  case B754_finite.B754_finite.B754_zero =>
    exact (BSN2B_B2BSN_of_not_nan _ _ (is_nan_normalize _ _ _ _)).symm
  case B754_finite.B754_finite.B754_finite =>
    exact (BSN2B_B2BSN_of_not_nan _ _ (is_nan_normalize _ _ _ _)).symm
  all_goals
    simp [Binary.Bfma, BinarySingleNaN.Bfma, Binary.BSN2B, Binary.B2BSN,
      binaryFloatToBinarySingleNaNFloat, Binary.build_nan,
      binaryPositiveOfNat_positiveToNat]
  all_goals first | rfl | (split_ifs <;> rfl)

-- Binary.v:1162
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (div_nan : Binary.BdivNaNHandler prec emax) (m : RoundingMode)
    (x y : binary_float prec emax) :
    Binary.Bdiv div_nan m x y =
      Binary.BSN2B (div_nan x y)
        (BinarySingleNaN.Bdiv m (Binary.B2BSN x) (Binary.B2BSN y)) := by
  cases x <;> cases y
  case B754_finite.B754_finite => exact (BSN2B_standardFloat _ _ _ _).symm
  all_goals
    simp [Binary.Bdiv, BinarySingleNaN.Bdiv, Binary.BSN2B, Binary.B2BSN,
      binaryFloatToBinarySingleNaNFloat, Binary.build_nan]

-- Binary.v:1193
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (sqrt_nan : Binary.BsqrtNaNHandler prec emax) (m : RoundingMode)
    (x : binary_float prec emax) :
    Binary.Bsqrt sqrt_nan m x =
      Binary.BSN2B (sqrt_nan x) (BinarySingleNaN.Bsqrt m (Binary.B2BSN x)) := by
  cases x with
  | B754_finite s mx ex h =>
      cases s
      · exact (BSN2B_standardFloat _ _ _ _).symm
      · rfl
  | B754_infinity s => cases s <;> rfl
  | _ => rfl

-- Binary.v:1266
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax] :
    (Binary.Bmax_float : binary_float prec emax) =
      Binary.BSN2B' BinarySingleNaN.Bmax_float rfl :=
  rfl

-- Binary.v:1271
example {prec emax : Int} (x : binary_float prec emax) :
    Binary.Bnormfr_mantissa x =
      BinarySingleNaN.Bnormfr_mantissa (Binary.B2BSN x) :=
  rfl

-- BinarySingleNaN.v:2820
example {prec emax : Int} (x : BinarySingleNaN.binary_float prec emax) :
    BinarySingleNaN.Bnormfr_mantissa x =
      SFnormfr_mantissa prec (binarySingleNaNFloatToStandardFloat x) :=
  rfl

/-- `Binary.valid_binary` carries the Binary.v:166 anchor. The root
`valid_binary` on the Nat-payload `FullFloat` agrees with it on every exact
`full_float`. -/
example {prec emax : Int} (x : full_float) :
    valid_binary (prec:=prec) (emax:=emax) x.toFullFloat =
      Binary.valid_binary (prec:=prec) (emax:=emax) x := by
  cases x <;> simp [valid_binary, Binary.valid_binary, valid_full_float_binary,
    full_float.toFullFloat, nan_pl, FloatSpec.Core.Zaux.positiveToNat_pos]

end BinaryLift
