From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition valid (m : positive) (e : Z) :=
  SpecFloat.valid_binary 3 4 (SpecFloat.S754_finite false m e).

Example validity_boundaries :
  valid 1 0 = false /\ valid 4 (-2) = true /\ valid 4 2 = false /\
  valid 1 (-4) = true /\ valid 1 (-5) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example total_converter_rejects_noncanonical_one :
  @BinarySingleNaN.B2SF 3 4 (@BinarySingleNaN.SF2B' 3 4 (SpecFloat.S754_finite false 1 0)) =
    SpecFloat.S754_nan /\
  @BinarySingleNaN.B2SF 3 4 (@BinarySingleNaN.SF2B' 3 4 (SpecFloat.S754_finite false 4 (-2))) =
    SpecFloat.S754_finite false 4 (-2).
Proof. vm_compute. split; reflexivity. Qed.

Example fit_requires_canonical_input :
  SpecFloat.valid_binary 3 4 (binary_fit_aux 3 4 mode_NE false 1 0) = false /\
  SpecFloat.valid_binary 3 4 (binary_fit_aux 3 4 mode_NE false 4 (-2)) = true.
Proof. vm_compute. split; reflexivity. Qed.

(* Zero mantissas cannot even be constructed in the source positive type. *)
Eval vm_compute in [valid 1 0; valid 4 (-2); valid 4 2; valid 1 (-4); valid 1 (-5)].
