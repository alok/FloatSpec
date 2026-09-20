From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
Module S := BinarySingleNaN.

Definition observe {prec emax : Z} (x : S.binary_float prec emax) := @S.B2SF prec emax x.
Definition one := @S.Bone 3 4 eq_refl eq_refl.
Definition tiny := @S.SF2B' 3 4 (SpecFloat.S754_finite false 1 (-4)).

Definition rows :=
  [observe one; observe (@Binary.B2BSN 3 4 (@Binary.Bone 3 4 eq_refl eq_refl));
   observe (@S.binary_normalize 3 4 eq_refl eq_refl S.mode_NE 0 0 true);
   observe (@S.binary_normalize 3 4 eq_refl eq_refl S.mode_NE (-9) (-3) false);
   observe (@S.Bldexp 3 4 eq_refl eq_refl S.mode_NE tiny (-1));
   observe (@S.Bldexp 3 4 eq_refl eq_refl S.mode_UP tiny (-1));
   observe (@S.Bulp' 3 4 eq_refl eq_refl one);
   observe (@S.Bpred_pos' 3 4 eq_refl eq_refl one);
   observe (@S.Bsucc' 3 4 eq_refl eq_refl one);
   observe (@S.Bsucc' 3 4 eq_refl eq_refl (@S.Bopp 3 4 tiny));
   observe (@S.Bsucc' 3 4 eq_refl eq_refl (@S.B754_zero 3 4 true));
   observe (@S.Bsucc' 3 4 eq_refl eq_refl (@S.B754_infinity 3 4 true));
   observe (@S.Bsucc' 3 4 eq_refl eq_refl (@S.B754_nan 3 4))].

Definition expected :=
  [SpecFloat.S754_finite false 4 (-2); SpecFloat.S754_finite false 4 (-2);
   SpecFloat.S754_zero true; SpecFloat.S754_finite true 4 (-2);
   SpecFloat.S754_zero false; SpecFloat.S754_finite false 1 (-4);
   SpecFloat.S754_finite false 4 (-4); SpecFloat.S754_finite false 7 (-3);
   SpecFloat.S754_finite false 5 (-2); SpecFloat.S754_zero true;
   SpecFloat.S754_finite false 1 (-4); SpecFloat.S754_finite true 7 1; SpecFloat.S754_nan].

Definition fractions :=
  [let f := @S.Bfrexp 3 4 eq_refl one in (observe (fst f), snd f);
   let f := @S.Bfrexp 3 4 eq_refl tiny in (observe (fst f), snd f);
   let f := @S.Bfrexp 3 4 eq_refl (@S.B754_zero 3 4 true) in (observe (fst f), snd f);
   let f := @S.Bfrexp 1 2 eq_refl (@S.Bone 1 2 eq_refl eq_refl) in (observe (fst f), snd f)].

Definition expectedFractions :=
  [(SpecFloat.S754_finite false 4 (-3), 1); (SpecFloat.S754_finite false 4 (-3), -3);
   (SpecFloat.S754_zero true, -11); (SpecFloat.S754_finite false 1 0, 0)].

Definition shifts :=
  [SpecFloat.shr_m (fst (SpecFloat.shr_fexp 3 4 (-1) (-5) SpecFloat.loc_Exact));
   SpecFloat.shr_m (fst (SpecFloat.shr_fexp 3 4 (-1) (-5) SpecFloat.loc_Exact))].

Example helper_boundaries : rows = expected /\ fractions = expectedFractions /\ shifts = [0; 0].
Proof. vm_compute. auto. Qed.

Example finiteness_premise_matters :
  observe (@S.Bulp' 3 4 eq_refl eq_refl (@S.B754_infinity 3 4 false)) <>
  observe (@S.Bulp 3 4 eq_refl eq_refl (@S.B754_infinity 3 4 false)).
Proof. vm_compute. discriminate. Qed.

Example positive_predecessor_premise_matters :
  observe (@S.Bpred_pos' 3 4 eq_refl eq_refl (@S.Bopp 3 4 one)) <>
  observe (@S.Bpred 3 4 eq_refl eq_refl (@S.Bopp 3 4 one)).
Proof. vm_compute. discriminate. Qed.
