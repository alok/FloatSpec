From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

(* The reading guide's 3-bit halfway example: 9 * 2^-3 = 1.125.
   The mantissa/exponent pairs (4,-2) and (5,-2) represent 1 and 1.25. *)
Definition halfway (m : mode) (sign : bool) : list Z :=
  match BinarySingleNaN.binary_round 3 4 m sign 9 (-3) with
  | SpecFloat.S754_finite s mantissa exponent =>
      [if s then 1 else 0; Zpos mantissa; exponent]
  | _ => []
  end.

Example halfway_all_modes :
  map (fun m => halfway m false) [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA] =
  [[0;4;-2]; [0;4;-2]; [0;4;-2]; [0;5;-2]; [0;5;-2]] /\
  map (fun m => halfway m true) [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA] =
  [[1;4;-2]; [1;4;-2]; [1;5;-2]; [1;4;-2]; [1;5;-2]].
Proof. vm_compute. split; reflexivity. Qed.
