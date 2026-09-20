From Stdlib Require Import ZArith List Lia.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

(* Independent integer quotient model; actual Flocq binary_round checks the format. *)
Definition positiveUnits : list Z :=
  [1; 2; 3] ++ flat_map (fun shift =>
    map (fun mantissa => mantissa * 2 ^ Z.of_nat shift) [4; 5; 6; 7]) (seq 0 6).
Definition finiteUnits : list Z := map Z.opp positiveUnits ++ [0] ++ positiveUnits.

Definition quotient (mode : nat) (x y : Z) : Z :=
  if Z.eqb y 0 then 0 else
    let numerator := if Z.ltb y 0 then -x else x in
    let denominator := Z.abs y in
    let lower := numerator / denominator in
    let remainder := numerator mod denominator in
    match mode with
    | O => Z.quot numerator denominator
    | S O => lower + if Z.ltb denominator (2 * remainder) then 1 else 0
    | S (S O) => lower + if Z.leb denominator (2 * remainder) then 1 else 0
    | _ => lower + if Z.eqb remainder 0 then 0 else 1
    end.

Definition roundedUnits (value : Z) : option Z :=
  if Z.eqb value 0 then Some 0 else
    match binary_round 3 4 mode_NE (Z.ltb value 0) (Z.to_pos (Z.abs value)) (-4) with
    | SpecFloat.S754_zero _ => Some 0
    | SpecFloat.S754_finite sign mantissa exponent =>
        if Z.leb (-4) exponent then
          let magnitude := Z.pos mantissa * 2 ^ (exponent + 4) in
          Some (if sign then -magnitude else magnitude)
        else None
    | _ => None
    end.

Definition same (actual : option Z) (expected : Z) : bool :=
  match actual with Some value => Z.eqb value expected | None => false end.

Definition sourcePremise (x y q : Z) : bool :=
  orb (Z.eqb y 0) (orb (Z.leb (Z.abs y) (2 * Z.abs x)) (Z.eqb q 0)).

Definition check (mode : nat) (x y : Z) : bool :=
  let q := quotient mode x y in
  let remainder := x - q * y in
  orb (negb (sourcePremise x y q)) (same (roundedUnits remainder) remainder).

Example remainder_grid :
  forallb (fun mode => forallb (fun pair => check mode (fst pair) (snd pair))
    (list_prod finiteUnits finiteUnits)) [0%nat; 1%nat; 2%nat; 3%nat] = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions remainder_grid.

Example ceiling_is_not_unconditionally_exact :
  roundedUnits (1 - quotient 3 1 128 * 128) <> Some (1 - quotient 3 1 128 * 128).
Proof. vm_compute. discriminate. Qed.
Print Assumptions ceiling_is_not_unconditionally_exact.

Definition cases := flat_map (fun mode => map (fun pair => (mode, pair))
  (list_prod finiteUnits finiteUnits)) [0%nat; 1%nat; 2%nat; 3%nat].
Definition qualified (c : nat * (Z * Z)) :=
  let '(mode, (x, y)) := c in sourcePremise x y (quotient mode x y).
Definition inexactOutside (c : nat * (Z * Z)) :=
  let '(mode, (x, y)) := c in
  let r := x - quotient mode x y * y in
  andb (negb (qualified c)) (negb (same (roundedUnits r) r)).
Eval vm_compute in
  (length cases, length (filter qualified cases),
   length (filter (fun c => negb (qualified c)) cases),
   length (filter inexactOutside cases),
   length (filter (fun c => Z.eqb (snd (snd c)) 0) cases)).
