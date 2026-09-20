From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
Module S := BinarySingleNaN.

Definition inputs : list (Z * Z * bool) :=
  [(0, 20, true); (0, -20, false); (9, -3, false); (-9, -3, false);
   (1, -5, false); (-1, -5, false); (15, 0, false); (-15, 0, false);
   (11, -3, false); (-11, -3, false)].

Definition observe mode m e szero : list SpecFloat.spec_float :=
  [@Binary.B2SF 3 4 (@Binary.binary_normalize 3 4 eq_refl eq_refl mode m e szero);
   @S.B2SF 3 4 (@S.binary_normalize 3 4 eq_refl eq_refl mode m e szero);
   @S.B2SF 3 4 (@S.binary_normalize 3 4 eq_refl eq_refl mode m e szero)].

Definition actual :=
  map (fun mode => flat_map (fun '(m, e, szero) => observe mode m e szero) inputs)
    [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA].

Definition expected : list (list SpecFloat.spec_float) :=
  [[SpecFloat.S754_zero true;
     SpecFloat.S754_zero false;
     SpecFloat.S754_finite false 4 (-2);
     SpecFloat.S754_finite true 4 (-2);
     SpecFloat.S754_zero false;
     SpecFloat.S754_zero true;
     SpecFloat.S754_infinity false;
     SpecFloat.S754_infinity true;
     SpecFloat.S754_finite false 6 (-2);
     SpecFloat.S754_finite true 6 (-2)];
   [SpecFloat.S754_zero true;
     SpecFloat.S754_zero false;
     SpecFloat.S754_finite false 4 (-2);
     SpecFloat.S754_finite true 4 (-2);
     SpecFloat.S754_zero false;
     SpecFloat.S754_zero true;
     SpecFloat.S754_finite false 7 (1);
     SpecFloat.S754_finite true 7 (1);
     SpecFloat.S754_finite false 5 (-2);
     SpecFloat.S754_finite true 5 (-2)];
   [SpecFloat.S754_zero true;
     SpecFloat.S754_zero false;
     SpecFloat.S754_finite false 4 (-2);
     SpecFloat.S754_finite true 5 (-2);
     SpecFloat.S754_zero false;
     SpecFloat.S754_finite true 1 (-4);
     SpecFloat.S754_finite false 7 (1);
     SpecFloat.S754_infinity true;
     SpecFloat.S754_finite false 5 (-2);
     SpecFloat.S754_finite true 6 (-2)];
   [SpecFloat.S754_zero true;
     SpecFloat.S754_zero false;
     SpecFloat.S754_finite false 5 (-2);
     SpecFloat.S754_finite true 4 (-2);
     SpecFloat.S754_finite false 1 (-4);
     SpecFloat.S754_zero true;
     SpecFloat.S754_infinity false;
     SpecFloat.S754_finite true 7 (1);
     SpecFloat.S754_finite false 6 (-2);
     SpecFloat.S754_finite true 5 (-2)];
   [SpecFloat.S754_zero true;
     SpecFloat.S754_zero false;
     SpecFloat.S754_finite false 5 (-2);
     SpecFloat.S754_finite true 5 (-2);
     SpecFloat.S754_finite false 1 (-4);
     SpecFloat.S754_finite true 1 (-4);
     SpecFloat.S754_infinity false;
     SpecFloat.S754_infinity true;
     SpecFloat.S754_finite false 6 (-2);
     SpecFloat.S754_finite true 6 (-2)]].

(* There is no separate Flocq declaration for Lean's validity adapter. Observe
   the source raw result only when the explicit validity premise holds. *)
Definition adapter prec emax mode sx mx ex lx : bool * SpecFloat.spec_float :=
  let raw := @S.binary_round_aux prec emax mode sx mx ex lx in
  let valid := SpecFloat.valid_binary prec emax raw in
  (valid, if valid then raw else SpecFloat.S754_nan).

Definition adapterRows :=
  [adapter 3 4 mode_NE false 9 (-3) SpecFloat.loc_Exact;
   adapter 3 4 mode_NA true 9 (-3) SpecFloat.loc_Exact;
   adapter 3 4 mode_NE true 0 (-4) SpecFloat.loc_Exact;
   adapter 3 4 mode_NE false (-1) (-4) SpecFloat.loc_Exact;
   adapter 3 0 mode_ZR false 1 0 SpecFloat.loc_Exact;
   adapter 0 1 mode_ZR false 1 0 SpecFloat.loc_Exact].

Definition expectedAdapters :=
  [(true, SpecFloat.S754_finite false 4 (-2)); (true, SpecFloat.S754_finite true 5 (-2));
   (true, SpecFloat.S754_zero true); (true, SpecFloat.S754_nan); (false, SpecFloat.S754_nan);
   (true, SpecFloat.S754_zero false)].

Example normalizers_agree_with_literals :
  actual = map (fun values => flat_map (fun value => repeat value 3) values) expected.
Proof. vm_compute. reflexivity. Qed.

Example adapter_premise_is_observed : adapterRows = expectedAdapters.
Proof. vm_compute. reflexivity. Qed.
