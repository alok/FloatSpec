From Stdlib Require Import ZArith List Bool.
Require Import Flocq.Core.Core Flocq.Calc.Bracket Flocq.Calc.Div Flocq.Calc.Sqrt.
Import ListNotations.
Open Scope Z_scope.

Definition matchesLocation (lowerEqual : bool) (midpoint : comparison)
    (location : SpecFloat.location) : bool :=
  match location with
  | SpecFloat.loc_Exact => lowerEqual
  | SpecFloat.loc_Inexact position => negb lowerEqual &&
      match position, midpoint with Lt, Lt | Eq, Eq | Gt, Gt => true | _, _ => false end
  end.

Definition divisionLaw (beta : radix) (m1 e1 m2 e2 target : Z) : bool :=
  let '(q, location) := Div.Fdiv_core beta m1 e1 m2 e2 target in
  let common := Z.min e1 (e2 + target) in
  let numerator := m1 * Z.pow beta (e1 - common) in
  let denominator := m2 * Z.pow beta (e2 + target - common) in
  (q * denominator <=? numerator) && (numerator <? (q + 1) * denominator) &&
    matchesLocation (numerator =? q * denominator)
      (Z.compare (2 * numerator) ((2 * q + 1) * denominator)) location.

Definition sqrtLaw (beta : radix) (mantissa exponent target : Z) : bool :=
  let '(q, location) := Sqrt.Fsqrt_core beta mantissa exponent target in
  let common := Z.min exponent (2 * target) in
  let numerator := mantissa * Z.pow beta (exponent - common) in
  let denominator := Z.pow beta (2 * target - common) in
  (0 <=? q) && (q * q * denominator <=? numerator) &&
    (numerator <? (q + 1) * (q + 1) * denominator) &&
    matchesLocation (numerator =? q * q * denominator)
      (Z.compare (4 * numerator) ((2 * q + 1) * (2 * q + 1) * denominator)) location.

Definition bases := [radix2; Build_radix 3 eq_refl; Build_radix 10 eq_refl].
Definition divisionChecks := flat_map (fun beta =>
  flat_map (fun left => flat_map (fun right =>
    flat_map (fun leftExponent => flat_map (fun rightExponent =>
      map (fun target => divisionLaw beta (Z.of_nat left + 1) leftExponent
        (Z.of_nat right + 1) rightExponent target) [-2; -1; 0; 1; 2])
        [-1; 0; 1]) [-1; 0; 1]) (seq 0 8)) (seq 0 8)) bases.

Definition sqrtChecks := flat_map (fun beta => flat_map (fun mantissa =>
  flat_map (fun exponent => map (fun target => sqrtLaw beta (Z.of_nat mantissa + 1) exponent target)
    (filter (fun target => 2 * target <=? exponent) [-3; -2; -1; 0; 1; 2; 3]))
    [-3; -2; -1; 0; 1; 2; 3]) (seq 0 32)) bases.

Example division_literal : divisionLaw radix2 1 0 3 0 0 = true.
Proof. vm_compute. reflexivity. Qed.
Example division_grid : length divisionChecks = 8640%nat /\ forallb (fun b => b) divisionChecks = true.
Proof. vm_compute. split; reflexivity. Qed.
Example sqrt_literal : sqrtLaw radix2 2 0 0 = true.
Proof. vm_compute. reflexivity. Qed.
Example sqrt_grid : length sqrtChecks = 2496%nat /\ forallb (fun b => b) sqrtChecks = true.
Proof. vm_compute. split; reflexivity. Qed.
Example sqrt_needs_exponent_premise :
  Sqrt.Fsqrt_core radix2 9 0 1 = (0, SpecFloat.loc_Exact) /\ sqrtLaw radix2 9 0 1 = false.
Proof. vm_compute. split; reflexivity. Qed.
Example quotient_two_scales :
  Div.Fdiv_core radix2 7 0 3 0 (-1) = (4, SpecFloat.loc_Inexact Gt) /\
  Div.Fdiv_core radix2 7 0 3 0 1 = (1, SpecFloat.loc_Inexact Lt).
Proof. vm_compute. split; reflexivity. Qed.
