From Stdlib Require Import ZArith Reals.
Require Import Flocq.Core.Core Flocq.Prop.Plus_error Flocq.Prop.Mult_error
  Flocq.Prop.Div_sqrt_error Flocq.IEEE754.Binary Flocq.IEEE754.BinarySingleNaN.
Open Scope R_scope.

Section Contracts.
Variable beta : radix.

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
