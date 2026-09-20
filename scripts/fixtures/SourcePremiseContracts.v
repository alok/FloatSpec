From Stdlib Require Import ZArith Reals.
Require Import Flocq.Core.Core Flocq.Prop.Plus_error Flocq.Prop.Mult_error
  Flocq.Prop.Div_sqrt_error Flocq.IEEE754.Binary Flocq.IEEE754.BinarySingleNaN.
Open Scope R_scope.

Section Contracts.
Variable beta : radix.

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
