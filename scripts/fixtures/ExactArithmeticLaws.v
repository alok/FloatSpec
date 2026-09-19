From Stdlib Require Import ZArith List Lia.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition positiveUnits : list Z :=
  [1; 2; 3] ++ flat_map (fun shift =>
    map (fun m => m * 2 ^ Z.of_nat shift) [4; 5; 6; 7]) (seq 0 6).
Definition finiteUnits : list Z := map Z.opp positiveUnits ++ [0] ++ positiveUnits.

Definition units (x : SpecFloat.spec_float) : option Z :=
  match x with
  | SpecFloat.S754_zero _ => Some 0
  | SpecFloat.S754_finite sign m e =>
      if Z.leb (-4) e then
        let magnitude := Z.pos m * 2 ^ (e + 4) in
        Some (if sign then -magnitude else magnitude)
      else None
  | _ => None
  end.

Definition rounded (mode : mode) (x : Z) : option Z :=
  if Z.eqb x 0 then Some 0
  else units (binary_round 3 4 mode (Z.ltb x 0) (Z.to_pos (Z.abs x)) (-4)).

Definition same (a b : option Z) : bool :=
  match a, b with
  | Some x, Some y => Z.eqb x y
  | _, _ => false
  end.

Definition sterbenzPairs := filter (fun pair =>
  andb (Z.leb (fst pair) (2 * snd pair)) (Z.leb (snd pair) (2 * fst pair)))
  (list_prod positiveUnits positiveUnits).
Definition additionPairs := filter (fun pair => Z.leb (Z.abs (fst pair + snd pair)) 224)
  (list_prod finiteUnits finiteUnits).

Definition additionError (mode : mode) (x y : Z) : bool :=
  match rounded mode (x + y) with
  | None => false
  | Some sum => same (rounded mode (sum - (x + y))) (Some (sum - (x + y)))
  end.

Example inputs_exact :
  forallb (fun mode => forallb (fun x => same (rounded mode x) (Some x)) finiteUnits)
    [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA] = true.
Proof. vm_compute. reflexivity. Qed.

Example sterbenz_grid :
  forallb (fun mode => forallb (fun pair =>
    same (rounded mode (fst pair - snd pair)) (Some (fst pair - snd pair))) sterbenzPairs)
    [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA] = true.
Proof. vm_compute. reflexivity. Qed.

Example addition_error_grid :
  forallb (fun mode => forallb (fun pair => additionError mode (fst pair) (snd pair)) additionPairs)
    [mode_NE; mode_NA] = true.
Proof. vm_compute. reflexivity. Qed.

Example sterbenz_premise_matters :
  rounded mode_NE 16 = Some 16 /\ rounded mode_NE 1 = Some 1 /\
  rounded mode_NE (16 - 1) = Some 16 /\ ~ (16 <= 2 * 1).
Proof. repeat split; try (vm_compute; reflexivity); lia. Qed.

Eval vm_compute in (length finiteUnits, length sterbenzPairs, length additionPairs).
