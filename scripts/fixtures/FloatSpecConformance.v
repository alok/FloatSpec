From Stdlib Require Import ZArith.
From Flocq Require Import Core.Zaux Core.Defs Core.FIX Calc.Bracket Calc.Operations Calc.Plus Calc.Round Calc.Div Calc.Sqrt IEEE754.Binary Pff.Pff2FlocqAux.

Open Scope Z_scope.

Example even_middle_exact_location :
    Bracket.new_location_even 4 2 SpecFloat.loc_Exact =
    SpecFloat.loc_Inexact Eq.
Proof. vm_compute. reflexivity. Qed.

Example odd_middle_inexact_location :
    Bracket.new_location_odd 3 1 (SpecFloat.loc_Inexact Gt) =
    SpecFloat.loc_Inexact Gt.
Proof. vm_compute. reflexivity. Qed.

Example fplus_core_negative_scale :
    (let beta := Build_radix 2 eq_refl in
      Fplus_core beta 1 0 0 1 1) =
    (0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fplus_core_positive_control :
    (let beta := Build_radix 2 eq_refl in
      Fplus_core beta 1 0 0 1 0) =
    (1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example falign_reverse_exponent :
    (let beta := Build_radix 2 eq_refl in
      Operations.Falign (Float beta 1 0) (Float beta 1 (-1))) =
    (2, 1, -1).
Proof. vm_compute. reflexivity. Qed.

Example fplus_close_magnitudes :
    (let beta := Build_radix 2 eq_refl in
      Plus.Fplus beta (FIX_exp 0) (Float beta 1 0) (Float beta 1 1)) =
    (3, 0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fdiv_core_exact_quotient :
    (let beta := Build_radix 2 eq_refl in
      Div.Fdiv_core beta 4 0 2 0 0) =
    (2, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fdiv_core_halfway_location :
    (let beta := Build_radix 2 eq_refl in
      Div.Fdiv_core beta 1 0 2 0 0) =
    (0, SpecFloat.loc_Inexact Eq).
Proof. vm_compute. reflexivity. Qed.

Example fdiv_exact_quotient :
    (let beta := Build_radix 2 eq_refl in
      Div.Fdiv (FIX_exp 0) (Float beta 4 0) (Float beta 2 0)) =
    (2, 0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fsqrt_core_exact_square :
    (let beta := Build_radix 2 eq_refl in
      Sqrt.Fsqrt_core beta 4 0 0) =
    (2, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fsqrt_core_inexact_location :
    (let beta := Build_radix 2 eq_refl in
      Sqrt.Fsqrt_core beta 2 0 0) =
    (1, SpecFloat.loc_Inexact Lt).
Proof. vm_compute. reflexivity. Qed.

Example fsqrt_exact_square :
    (let beta := Build_radix 2 eq_refl in
      Sqrt.Fsqrt (FIX_exp 0) (Float beta 4 0)) =
    (2, 0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example truncate_aux_negative_scale :
    (let beta := Build_radix 2 eq_refl in
      truncate_aux beta (2, 0, SpecFloat.loc_Exact) (-1)) =
    (0, -1, SpecFloat.loc_Inexact Gt).
Proof. vm_compute. reflexivity. Qed.

Example truncate_aux_positive_control :
    (let beta := Build_radix 2 eq_refl in
      truncate_aux beta (2, 0, SpecFloat.loc_Exact) 1) =
    (1, 1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example truncate_source_exponent :
    (let beta := Build_radix 2 eq_refl in
      truncate beta (FIX_exp 1) (4, 0, SpecFloat.loc_Exact)) =
    (2, 1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example round_sign_up_negative :
    Round.round_sign_UP true (SpecFloat.loc_Inexact Gt) = false.
Proof. vm_compute. reflexivity. Qed.

Example round_nearest_tie_choice :
    Round.round_N true (SpecFloat.loc_Inexact Eq) = true.
Proof. vm_compute. reflexivity. Qed.

Example truncate_fix_positive_shift :
    (let beta := Build_radix 2 eq_refl in
      Round.truncate_FIX beta 1 (4, 0, SpecFloat.loc_Exact)) =
    (2, 1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example nan_payload_bitlength_boundary :
    Zlt_bool (Zpos (SpecFloat.digits2_pos 4)) 3 = false.
Proof. vm_compute. reflexivity. Qed.

Example nan_payload_bitlength_valid :
    Zlt_bool (Zpos (SpecFloat.digits2_pos 3)) 3 = true.
Proof. vm_compute. reflexivity. Qed.

Example make_bound_Emin_zero_precision :
    (let beta := Build_radix 2 eq_refl in
      Z.of_N (Pff.dExp (make_bound beta 0 (-1)))) = 1.
Proof. vm_compute. reflexivity. Qed.
