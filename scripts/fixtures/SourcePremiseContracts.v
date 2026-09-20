From Stdlib Require Import ZArith Reals Lia Lra.
Require Import Flocq.Core.Core Flocq.Prop.Plus_error Flocq.Prop.Mult_error
  Flocq.Prop.Div_sqrt_error Flocq.IEEE754.Binary Flocq.IEEE754.BinarySingleNaN.
Require Import Flocq.Pff.Pff2Flocq.
Require Import Flocq.Calc.Bracket Flocq.Calc.Div Flocq.Calc.Sqrt.
Require Import Flocq.Core.FTZ.
Require Import Flocq.Prop.Round_odd.
Open Scope R_scope.

Section Contracts.
Variable beta : radix.

Definition ftz_normalized_contract (emin prec : Z) (x : R)
    (Hx : FTZ.FTZ_format beta emin prec x) : FLX.FLXN_format beta prec x :=
  @FTZ.FLXN_format_FTZ beta emin prec x Hx.

Definition ftz_generic_contract (emin prec : Z) (x : R)
    (Hx : FTZ.FTZ_format beta emin prec x) :
    generic_format beta (FTZ.FTZ_exp emin prec) x :=
  @FTZ.generic_format_FTZ beta emin prec x Hx.

Definition ftz_zero_at_any_precision (emin prec : Z) : FTZ.FTZ_format beta emin prec 0.
Proof.
  exists (Float beta 0 emin).
  - symmetry. apply F2R_0.
  - intro H. exfalso. apply H. reflexivity.
  - simpl. lia.
Defined.

Definition ftz_generic_zero_at_any_precision (emin prec : Z) :
    generic_format beta (FTZ.FTZ_exp emin prec) 0 :=
  @FTZ.generic_format_FTZ beta emin prec 0 (ftz_zero_at_any_precision emin prec).

Definition division_magnitude_contract (m1 e1 m2 e2 : Z)
    (Hm1 : (0 < m1)%Z) (Hm2 : (0 < m2)%Z) :
    let e := ((Zdigits beta m1 + e1) - (Zdigits beta m2 + e2))%Z in
    (e <= mag beta (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) <= e + 1)%Z :=
  @Div.mag_div_F2R beta m1 e1 m2 e2 Hm1 Hm2.

Definition division_core_contract (m1 e1 m2 e2 e : Z)
    (Hm1 : (0 < m1)%Z) (Hm2 : (0 < m2)%Z) :
    let '(m, l) := Div.Fdiv_core beta m1 e1 m2 e2 e in
    inbetween_float beta m e
      (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) l :=
  @Div.Fdiv_core_correct beta m1 e1 m2 e2 e Hm1 Hm2.

Definition sqrt_magnitude_contract (m e : Z) (Hm : (0 < m)%Z) :
    mag beta (sqrt (F2R (Float beta m e))) = Z.div2 (Zdigits beta m + e + 1) :> Z :=
  @Sqrt.mag_sqrt_F2R beta m e Hm.

Definition sqrt_core_contract (m e target : Z)
    (Hm : (0 < m)%Z) (He : (2 * target <= e)%Z) :
    let '(result, location) := Sqrt.Fsqrt_core beta m e target in
    inbetween_float beta result target (sqrt (F2R (Float beta m e))) location :=
  @Sqrt.Fsqrt_core_correct beta m e target Hm He.

Definition sqrt_result_contract (fexp : Z -> Z) (x : float beta) (Hx : 0 < F2R x) :
    let '(m, e, l) := @Sqrt.Fsqrt beta fexp x in
    (e <= cexp beta fexp (sqrt (F2R x)))%Z /\
    inbetween_float beta m e (sqrt (F2R x)) l :=
  @Sqrt.Fsqrt_correct beta fexp x Hx.

Definition canonical_positive_contract (fexp : Z -> Z) (Hmono : Monotone_exp fexp)
    (x y : R) (Hy : 0 < y) (Hexp : (cexp beta fexp x < cexp beta fexp y)%Z) :
    x < y := @lt_cexp_pos beta fexp Hmono x y Hy Hexp.

Definition canonical_absolute_contract (fexp : Z -> Z) (Hmono : Monotone_exp fexp)
    (x y : R) (Hy : y <> 0) (Hexp : (cexp beta fexp x < cexp beta fexp y)%Z) :
    Rabs x < Rabs y := @lt_cexp beta fexp Hmono x y Hy Hexp.

Definition canonical_upper_contract (fexp : Z -> Z) (Hmono : Monotone_exp fexp)
    (x : R) (e : Z) (Hx : x <> 0) (Hbound : Rabs x < bpow beta e) :
    (cexp beta fexp x <= fexp e)%Z := @cexp_le_bpow beta fexp Hmono x e Hx Hbound.

Definition canonical_lower_contract (fexp : Z -> Z) (Hmono : Monotone_exp fexp)
    (x : R) (e : Z) (Hbound : bpow beta (e - 1) <= Rabs x) :
    (fexp e <= cexp beta fexp x)%Z := @cexp_ge_bpow beta fexp Hmono x e Hbound.

Definition round_repr_contract (fexp : Z -> Z) (rnd : R -> Z)
    (Hr : Valid_rnd rnd) (m e : Z) :
    exists m', round beta fexp rnd (F2R (Float beta m e)) = F2R (Float beta m' e) :=
  @round_repr_same_exp beta fexp rnd Hr m e.

Definition plus_prec_contract (prec : Z) (fexp : Z -> Z)
    (Hbound : forall e, (fexp e <= e - prec)%Z)
    (x y : R) (fx fy : float beta) (Hx : x = F2R fx) (Hy : y = F2R fy)
    (Hl : Rabs (x + y) < bpow beta (prec + Fexp fx))
    (Hr : Rabs (x + y) < bpow beta (prec + Fexp fy)) :
    generic_format beta fexp (x + y) :=
  @generic_format_plus_prec beta prec fexp Hbound x y fx fy Hx Hy Hl Hr.

Definition mult_flx_contract (prec : Z) (x : R) (e : Z)
    (Hx : generic_format beta (FLX_exp prec) x) :
    generic_format beta (FLX_exp prec) (x * bpow beta e) :=
  @mult_bpow_exact_FLX beta prec x e Hx.

Definition mult_flt_contract (prec emin : Z) (x : R) (e : Z)
    (Hx : generic_format beta (FLT_exp emin prec) x)
    (Hbound : (emin + prec - mag beta x <= e)%Z) :
    generic_format beta (FLT_exp emin prec) (x * bpow beta e) :=
  @mult_bpow_exact_FLT beta emin prec x e Hx Hbound.

Definition mult_pos_flt_contract (prec emin : Z) (x : R) (e : Z)
    (Hx : generic_format beta (FLT_exp emin prec) x) (He : (0 <= e)%Z) :
    generic_format beta (FLT_exp emin prec) (x * bpow beta e) :=
  @mult_bpow_pos_exact_FLT beta emin prec x e Hx He.

Definition sqrt_decompose_contract (prec : Z) (x : R)
    (Hx : generic_format beta (FLX_exp prec) x) (Hpos : 0 < x) :
    exists (mu : R) (e : Z), generic_format beta (FLX_exp prec) mu /\
      x = mu * bpow beta (2 * e) /\ 1 <= mu /\ mu < bpow beta 2 :=
  @sqrt_error_N_FLX_aux1 beta prec x Hx Hpos.

End Contracts.

Definition compare_lt_contract (x y : R) (H : x < y) : Rcompare x y = Lt := Rcompare_Lt x y H.
Definition compare_eq_contract (x y : R) (H : x = y) : Rcompare x y = Eq := Rcompare_Eq x y H.
Definition compare_gt_contract (x y : R) (H : y < x) : Rcompare x y = Gt := Rcompare_Gt x y H.
Definition compare_not_lt_contract (x y : R) (H : y <= x) : Rcompare x y <> Lt := Rcompare_not_Lt x y H.
Definition compare_not_gt_contract (x y : R) (H : x <= y) : Rcompare x y <> Gt := Rcompare_not_Gt x y H.

Definition binary_comparison_contract (prec emax : Z)
    (x y : Binary.binary_float prec emax) : option comparison := @Binary.Bcompare prec emax x y.
Definition single_comparison_contract (prec emax : Z)
    (x y : BinarySingleNaN.binary_float prec emax) : option comparison := @BinarySingleNaN.Bcompare prec emax x y.
Definition binary_comparison_correct_contract (prec emax : Z)
    (x y : Binary.binary_float prec emax)
    (Hx : Binary.is_finite prec emax x = true) (Hy : Binary.is_finite prec emax y = true) :
    @Binary.Bcompare prec emax x y = Some (Rcompare (Binary.B2R prec emax x) (Binary.B2R prec emax y)) :=
  @Binary.Bcompare_correct prec emax x y Hx Hy.
Definition single_comparison_correct_contract (prec emax : Z)
    (x y : BinarySingleNaN.binary_float prec emax)
    (Hx : @BinarySingleNaN.is_finite prec emax x = true) (Hy : @BinarySingleNaN.is_finite prec emax y = true) :
    @BinarySingleNaN.Bcompare prec emax x y =
      Some (Rcompare (@BinarySingleNaN.B2R prec emax x) (@BinarySingleNaN.B2R prec emax y)) :=
  @BinarySingleNaN.Bcompare_correct prec emax x y Hx Hy.

Definition binary_trunc_without_precision (prec emax : Z)
    (x : Binary.binary_float prec emax) : Z := @Binary.Btrunc prec emax x.

Definition single_trunc_without_precision (prec emax : Z)
    (x : BinarySingleNaN.binary_float prec emax) : Z := @BinarySingleNaN.Btrunc prec emax x.

Definition binary_nearby_finite_contract (prec emax : Z) (Hlt : Prec_lt_emax prec emax)
    (nan : Binary.binary_float prec emax ->
      {x : Binary.binary_float prec emax | Binary.is_nan prec emax x = true})
    (md : mode) (x : Binary.binary_float prec emax) :
    Binary.is_finite prec emax (Binary.Bnearbyint prec emax Hlt nan md x) =
      Binary.is_finite prec emax x :=
  proj1 (proj2 (@Binary.Bnearbyint_correct prec emax Hlt nan md x)).

Definition binary_trunc_value_contract (prec emax : Z) (Hlt : Prec_lt_emax prec emax)
    (x : Binary.binary_float prec emax) :
    IZR (@Binary.Btrunc prec emax x) =
      round radix2 (FIX_exp 0) Ztrunc (Binary.B2R prec emax x) :=
  @Binary.Btrunc_correct prec emax Hlt x.

Definition single_trunc_value_contract (prec emax : Z) (Hlt : Prec_lt_emax prec emax)
    (x : BinarySingleNaN.binary_float prec emax) :
    IZR (@BinarySingleNaN.Btrunc prec emax x) =
      round radix2 (FIX_exp 0) Ztrunc (@BinarySingleNaN.B2R prec emax x) :=
  @BinarySingleNaN.Btrunc_correct prec emax Hlt x.

Definition real_integer_comparison_contract (left right : Z) :
    Rcompare (IZR left) (IZR right) = Z.compare left right :=
  Rcompare_IZR left right.

Definition binary_injection_contract (prec emax : Z)
    (x y : Binary.binary_float prec emax)
    (Hx : Binary.is_finite_strict prec emax x = true)
    (Hy : Binary.is_finite_strict prec emax y = true)
    (Hr : Binary.B2R prec emax x = Binary.B2R prec emax y) : x = y :=
  @Binary.B2R_inj prec emax x y Hx Hy Hr.

Definition binary_round_aux_contract (prec emax : Z) (md : mode) (sign : bool)
    (mantissa exponent : Z) (location : SpecFloat.location) : Binary.full_float :=
  @Binary.binary_round_aux prec emax md sign mantissa exponent location.

Definition binary_round_contract (prec emax : Z) (md : mode) (sign : bool)
    (mantissa : positive) (exponent : Z) : Binary.full_float :=
  @Binary.binary_round prec emax md sign mantissa exponent.

Definition binary_signed_injection_contract (prec emax : Z)
    (x y : Binary.binary_float prec emax)
    (Hx : Binary.is_finite prec emax x = true)
    (Hy : Binary.is_finite prec emax y = true)
    (Hr : Binary.B2R prec emax x = Binary.B2R prec emax y)
    (Hs : Binary.Bsign prec emax x = Binary.Bsign prec emax y) : x = y :=
  @Binary.B2R_Bsign_inj prec emax x y Hx Hy Hr Hs.

Definition binary_canonical_contract (prec emax : Z) (sign : bool)
    (mantissa : positive) (exponent : Z)
    (Hc : SpecFloat.canonical_mantissa prec emax mantissa exponent = true) :
    canonical radix2 (SpecFloat.fexp prec emax)
      (Float radix2 (SpecFloat.cond_Zopp sign (Zpos mantissa)) exponent) :=
  @Binary.canonical_canonical_mantissa prec emax sign mantissa exponent Hc.

Section StructuralRounding.
Variable beta : radix.
Variable fexp : Z -> Z.

Definition unrestricted_round (rnd : R -> Z) (x : R) : R := round beta fexp rnd x.
Definition zero_contract (rnd : R -> Z) (H : Valid_rnd rnd) :
  round beta fexp rnd 0 = 0 := @round_0 beta fexp rnd H.
Definition exact_contract (rnd : R -> Z) (H : Valid_rnd rnd) (x : R)
    (Hx : generic_format beta fexp x) : round beta fexp rnd x = x :=
  @round_generic beta fexp rnd H x Hx.
Definition ext_contract (rnd1 rnd2 : R -> Z) (H : forall x, rnd1 x = rnd2 x) (x : R) :
  round beta fexp rnd1 x = round beta fexp rnd2 x := @round_ext beta fexp rnd1 rnd2 H x.
Definition opposite_contract (rnd : R -> Z) (x : R) :
  round beta fexp rnd (-x) = -round beta fexp (Zrnd_opp rnd) x := @round_opp beta fexp rnd x.
Definition down_opposite_contract (x : R) := @round_DN_opp beta fexp x.
Definition up_opposite_contract (x : R) := @round_UP_opp beta fexp x.
Definition zero_opposite_contract (x : R) := @round_ZR_opp beta fexp x.
Definition away_opposite_contract (x : R) := @round_AW_opp beta fexp x.
Definition zero_down_contract (x : R) (Hx : 0 <= x) := @round_ZR_DN beta fexp x Hx.
Definition zero_up_contract (x : R) (Hx : x <= 0) := @round_ZR_UP beta fexp x Hx.
Definition away_up_contract (x : R) (Hx : 0 <= x) := @round_AW_UP beta fexp x Hx.
Definition away_down_contract (x : R) (Hx : x <= 0) := @round_AW_DN beta fexp x Hx.
End StructuralRounding.

Definition badExponent (e : Z) := (e + 1)%Z.
Example bad_exponent_really_invalid : ~ Valid_exp badExponent.
Proof.
  intro H.
  pose proof (proj1 (proj2 (@valid_exp badExponent H 0%Z)
    ltac:(unfold badExponent; lia))) as Hbad.
  unfold badExponent in Hbad; lia.
Qed.
Definition zero_at_bad_exponent (beta : radix) (rnd : R -> Z) (H : Valid_rnd rnd) :
  round beta badExponent rnd 0 = 0 := @round_0 beta badExponent rnd H.

Definition mult_error_bound_contract (beta : radix) (emin prec : Z)
    (rnd : R -> Z) (H : Valid_rnd rnd) (x y : R) (e : Z)
    (Hx : generic_format beta (FLT_exp emin prec) x)
    (Hy : generic_format beta (FLT_exp emin prec) y)
    (Hb : bpow beta (e + 2 * prec - 1) <= Rabs (x * y))
    (Hnz : round beta (FLT_exp emin prec) rnd (x * y) - x * y <> 0) :
    bpow beta e <= Rabs (round beta (FLT_exp emin prec) rnd (x * y) - x * y) :=
  @mult_error_FLT_ge_bpow beta emin prec rnd H x y e Hx Hy Hb Hnz.

Definition nearest_mult_error_bound_contract (beta : radix) (emin prec : Z)
    (x y : R) (e : Z)
    (Hx : generic_format beta (FLT_exp emin prec) x)
    (Hy : generic_format beta (FLT_exp emin prec) y)
    (Hb : x * y = 0 \/ bpow beta e <= Rabs (x * y)) :=
  @mult_error_FLT_ge_bpow' beta emin prec x y e Hx Hy Hb.

Module FLTUnrestrictedSourceContracts.
Open Scope R_scope.
Definition normal_exponent_client (beta : radix) (emin prec : Z) (x : R)
    (h : bpow beta (emin + prec - 1) <= Rabs x) :
    cexp beta (FLT_exp emin prec) x = cexp beta (FLX_exp prec) x :=
  cexp_FLT_FLX beta emin prec x h.
Definition normal_format_client (beta : radix) (emin prec : Z) (x : R)
    (h : bpow beta (emin + prec - 1) <= Rabs x)
    (hx : generic_format beta (FLX_exp prec) x) :
    generic_format beta (FLT_exp emin prec) x :=
  generic_format_FLT_FLX beta emin prec x h hx.
Definition unbounded_format_client (beta : radix) (emin prec : Z) (x : R)
    (hx : generic_format beta (FLT_exp emin prec) x) :
    generic_format beta (FLX_exp prec) x :=
  generic_format_FLX_FLT beta emin prec x hx.
Definition normal_round_client (beta : radix) (emin prec : Z) (rnd : R -> Z) (x : R)
    (h : bpow beta (emin + prec - 1) <= Rabs x) :
    round beta (FLT_exp emin prec) rnd x = round beta (FLX_exp prec) rnd x :=
  round_FLT_FLX beta emin prec rnd x h.
Definition small_exponent_client (beta : radix) (emin prec : Z) (x : R)
    (hne : x <> 0) (h : Rabs x < bpow beta (emin + prec)) :
    cexp beta (FLT_exp emin prec) x = cexp beta (FIX_exp emin) x :=
  cexp_FLT_FIX beta emin prec x hne h.
Definition fixed_format_client (beta : radix) (emin prec : Z) (x : R)
    (hx : generic_format beta (FLT_exp emin prec) x) :
    generic_format beta (FIX_exp emin) x :=
  generic_format_FIX_FLT beta emin prec x hx.

Definition normal_ulp_client (beta : radix) (emin prec : Z) (x : R)
    (h : bpow beta (emin + prec - 1) <= Rabs x) :
    ulp beta (FLT_exp emin prec) x <= Rabs x * bpow beta (1 - prec) :=
  @ulp_FLT_le beta emin prec x h.
Definition shift_ulp_client (beta : radix) (emin prec : Z) (x : R) (e : Z)
    (hx : x <> 0) (hm : (emin + prec <= mag beta x)%Z)
    (he : (emin + prec - mag beta x <= e)%Z) :
    ulp beta (FLT_exp emin prec) (x * bpow beta e) =
      ulp beta (FLT_exp emin prec) x * bpow beta e :=
  @ulp_FLT_exact_shift beta emin prec x e hx hm he.
Definition shift_succ_pos_client (beta : radix) (emin prec : Z) (x : R) (e : Z)
    (hx : 0 < x) (hm : (emin + prec <= mag beta x)%Z)
    (he : (emin + prec - mag beta x <= e)%Z) :
    succ beta (FLT_exp emin prec) (x * bpow beta e) =
      succ beta (FLT_exp emin prec) x * bpow beta e :=
  @succ_FLT_exact_shift_pos beta emin prec x e hx hm he.
Definition shift_succ_client (beta : radix) (emin prec : Z) (x : R) (e : Z)
    (hx : x <> 0) (hm : (emin + prec + 1 <= mag beta x)%Z)
    (he : (emin + prec - mag beta x + 1 <= e)%Z) :
    succ beta (FLT_exp emin prec) (x * bpow beta e) =
      succ beta (FLT_exp emin prec) x * bpow beta e :=
  @succ_FLT_exact_shift beta emin prec x e hx hm he.
Definition shift_pred_client (beta : radix) (emin prec : Z) (x : R) (e : Z)
    (hx : x <> 0) (hm : (emin + prec + 1 <= mag beta x)%Z)
    (he : (emin + prec - mag beta x + 1 <= e)%Z) :
    pred beta (FLT_exp emin prec) (x * bpow beta e) =
      pred beta (FLT_exp emin prec) x * bpow beta e :=
  @pred_FLT_exact_shift beta emin prec x e hx hm he.
(* All other premises of generic_format_FLT_FIX hold at precision zero. *)
Example zero_precision_reverse_inclusion_counterexample :
    Rabs 1 <= bpow radix2 (0 + 0) /\
    generic_format radix2 (FIX_exp 0) 1 /\
    ~ generic_format radix2 (FLT_exp 0 0) 1.
Proof.
  split.
  - change (Rabs 1 <= 1)%R. rewrite Rabs_R1. lra.
  - replace 1 with (bpow radix2 0) by reflexivity.
    split.
    + apply generic_format_bpow. unfold FIX_exp. lia.
    + intro H.
      pose proof (generic_format_bpow_inv' radix2 (FLT_exp 0 0) 0 H) as He.
      cbn in He. lia.
Qed.
End FLTUnrestrictedSourceContracts.

Module RoundingWitnessSourceContracts.
Definition identity_predicate : round_pred (fun x y : R => y = x).
Proof.
  split.
  - intro x. exists x. reflexivity.
  - intros x y f g Hf Hg Hxy. now rewrite Hf, Hg.
Defined.

Example identity_value (x : R) :
    proj1_sig (round_val_of_pred _ identity_predicate x) = x.
Proof. exact (proj2_sig (round_val_of_pred _ identity_predicate x)). Qed.

Example identity_function (x : R) :
    proj1_sig (round_fun_of_pred _ identity_predicate) x = x.
Proof. exact (proj2_sig (round_fun_of_pred _ identity_predicate) x). Qed.

Example no_empty_predicate : ~ round_pred (fun _ _ : R => False).
Proof. intros [H _]. destruct (H 0) as [x Hx]. exact Hx. Qed.

Definition witness_value_client (rnd : R -> R -> Prop) (h : round_pred rnd) (x : R)
    : {f : R | rnd x f} := round_val_of_pred rnd h x.
Definition witness_function_client (rnd : R -> R -> Prop) (h : round_pred rnd)
    : {f : R -> R | forall x, rnd x (f x)} := round_fun_of_pred rnd h.

End RoundingWitnessSourceContracts.

Module FLXUnitSourceContracts.
Definition ulp_one_client (beta : radix) (prec : Z) :
    ulp beta (FLX_exp prec) 1 = bpow beta (1 - prec).
Proof. replace (1 - prec)%Z with (-prec + 1)%Z by ring. apply ulp_FLX_1. Qed.
Definition succ_one_client (beta : radix) (prec : Z) :
    succ beta (FLX_exp prec) 1 = 1 + bpow beta (1 - prec).
Proof. replace (1 - prec)%Z with (-prec + 1)%Z by ring. apply succ_FLX_1. Qed.

Example nonpositive_precision_examples :
    ulp radix2 (FLX_exp 0) 1 = 2 /\
    succ radix2 (FLX_exp 0) 1 = 3 /\
    ulp radix2 (FLX_exp (-1)) 1 = 4 /\
    succ radix2 (FLX_exp (-1)) 1 = 5.
Proof.
  repeat split; rewrite ?ulp_FLX_1, ?succ_FLX_1; cbn; ring.
Qed.
End FLXUnitSourceContracts.

Module RoundParitySourceContracts.
Section Contracts.
Variable beta : radix.
Variable fexp : Z -> Z.
Definition positive_statement : Prop := Round_NE.DN_UP_parity_pos_prop beta fexp.
Definition signed_statement : Prop := Round_NE.DN_UP_parity_prop beta fexp.
Definition parity_transfer (h : Round_NE.DN_UP_parity_pos_prop beta fexp) :
  Round_NE.DN_UP_parity_prop beta fexp := Round_NE.DN_UP_parity_aux beta fexp h.
Definition nearest_negate (x : R) :
  round beta fexp ZnearestE (-x) = -round beta fexp ZnearestE x :=
  Round_NE.round_NE_opp beta fexp x.
Definition odd_negate (x : R) :
  round beta fexp Round_odd.Zrnd_odd (-x) = -round beta fexp Round_odd.Zrnd_odd x :=
  Round_odd.round_odd_opp beta fexp x.
Context {valid : Valid_exp fexp}.
Definition nearest_absolute (x : R) :
  round beta fexp ZnearestE (Rabs x) = Rabs (round beta fexp ZnearestE x) :=
  Round_NE.round_NE_abs beta fexp x.
End Contracts.

Example one_bit_fails_exists_ne : ~Round_NE.Exists_NE radix2 (FLX_exp 1).
Proof.
  intros [Hodd|Hexp].
  - discriminate Hodd.
  - specialize (Hexp 1%Z).
    unfold FLX_exp in Hexp.
    destruct Hexp as [H _].
    specialize (H ltac:(lia)). lia.
Qed.
Example one_bit_negate (x : R) :
  round radix2 (FLX_exp 1) ZnearestE (-x) =
    -round radix2 (FLX_exp 1) ZnearestE x.
Proof. apply Round_NE.round_NE_opp. Qed.
End RoundParitySourceContracts.
