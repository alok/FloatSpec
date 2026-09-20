From Stdlib Require Import ZArith List.
Require Import Flocq.Core.Zaux Flocq.Pff.Pff2FlocqAux.
Import ListNotations.
Open Scope Z_scope.

Definition fields (b : Pff.Fbound) : Z * Z :=
  (Zpos (Pff.vNum b), Z.of_N (Pff.dExp b)).

Example source_bound_literals :
  [fields (make_bound radix2 (-3) (-10));
   fields (make_bound (Build_radix 3 eq_refl) 2 10);
   fields bsingle; fields bdouble] =
  [(1,10); (9,10); (16777216,149); (9007199254740992,1074)].
Proof. vm_compute. reflexivity. Qed.

Example normalization_is_not_identity :
  Pff.Fnormalize 2 (make_bound radix2 3 (-10)) 3 (Pff.Float 1 0) =
  Pff.Float 4 (-2).
Proof. vm_compute. reflexivity. Qed.
