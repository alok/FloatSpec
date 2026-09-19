From Stdlib Require Import ZArith List.
From Flocq Require Import Core.Zaux Calc.Bracket Calc.Sqrt.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Definition locations := [SpecFloat.loc_Exact; SpecFloat.loc_Inexact Lt;
  SpecFloat.loc_Inexact Eq; SpecFloat.loc_Inexact Gt].
Definition quarter (l : SpecFloat.location) : Z :=
  match l with
  | SpecFloat.loc_Exact => 0
  | SpecFloat.loc_Inexact Lt => 1
  | SpecFloat.loc_Inexact Eq => 2
  | SpecFloat.loc_Inexact Gt => 3
  end.
Definition classify_quarter (steps index : Z) (l : SpecFloat.location) :=
  let numerator := 4 * index + quarter l in
  if Z.eqb numerator 0 then 0 else
    match Z.compare numerator (2 * steps) with Lt => 1 | Eq => 2 | Gt => 3 end.

(* 8,316 rational representatives; the oracle classifies an exact rational
   value against the enclosing interval midpoint, independently of the source
   function's parity split. *)
Example location_rational_grid :
  forallb (fun n => let steps := (n + 2)%nat in
    forallb (fun index => forallb (fun l =>
      Z.eqb (quarter (new_location (Z.of_nat steps) (Z.of_nat index) l))
        (classify_quarter (Z.of_nat steps) (Z.of_nat index) l)) locations)
      (seq 0 steps)) (seq 0 63) = true.
Proof. vm_compute. reflexivity. Qed.

(* Signed floor-division reconstruction and remainder sign/range; division by
   zero is a total-function convention, not a real-division theorem. *)
Example signed_division_grid :
  forallb (fun n => forallb (fun d =>
    let a := Z.of_nat n - 32 in let b := Z.of_nat d - 16 in
    let '(q, r) := Z.div_eucl a b in
    Z.eqb a (b * q + r) &&
      (if Z.eqb b 0 then Z.eqb q 0 && Z.eqb r a
       else if Z.ltb 0 b then Z.leb 0 r && Z.ltb r b
       else Z.ltb b r && Z.leb r 0)) (seq 0 33)) (seq 0 65) = true.
Proof. vm_compute. reflexivity. Qed.

Example sqrt_bracket_grid :
  forallb (fun n =>
    let m := Z.of_nat n - 16 in
    let '(q, l) := Fsqrt_core (Build_radix 2 eq_refl) m 0 0 in
    if Z.ltb m 0 then Z.eqb q 0 && Z.eqb (quarter l) 0
    else Z.leb 0 q && Z.leb (q * q) m && Z.ltb m ((q+1) * (q+1)) &&
      Bool.eqb (Z.eqb (quarter l) 0) (Z.eqb (q*q) m)) (seq 0 273) = true.
Proof. vm_compute. reflexivity. Qed.
