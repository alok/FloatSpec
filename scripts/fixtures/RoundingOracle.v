From Stdlib Require Import ZArith List Bool.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

(* Independent all-mode enumeration/distance oracle. Input units are 2^-8 and
   candidate output units 2^-4. Parity belongs to the canonical mantissa,
   not to the scaled integer value. *)
Definition positives : list (Z * bool) :=
  [(1, false); (2, true); (3, false)] ++
  flat_map (fun shift => map (fun m => (m * 2 ^ Z.of_nat shift, Z.even m))
    [4; 5; 6; 7]) (seq 0 6).
Definition candidates : list (Z * bool) :=
  map (fun pair => (- fst pair, snd pair)) positives ++ [(0, true)] ++ positives.

Definition allowed (mode : mode) (n v : Z) : bool :=
  match mode with
  | mode_NE | mode_NA => true
  | mode_DN => Z.leb (16 * v) n
  | mode_UP => Z.leb n (16 * v)
  | mode_ZR => if Z.ltb n 0 then Z.leb n (16 * v) else Z.leb (16 * v) n
  end.

Definition better (mode : mode) (n : Z) (a b : Z * bool) : bool :=
  let da := Z.abs (16 * fst a - n) in
  let db := Z.abs (16 * fst b - n) in
  orb (Z.ltb da db) (andb (Z.eqb da db)
    (match mode with
    | mode_NE => andb (snd a) (negb (snd b))
    | mode_NA => Z.ltb (Z.abs (fst b)) (Z.abs (fst a))
    | _ => false
    end)).

Definition oracle (mode : mode) (n : Z) : option Z :=
  option_map fst (fold_left (fun best next =>
    if negb (allowed mode n (fst next)) then best
    else match best with
    | None => Some next
    | Some old => if better mode n next old then Some next else best
    end) candidates None).

Definition observed (mode : mode) (n : Z) : option Z :=
  if Z.eqb n 0 then Some 0
  else match binary_round 3 4 mode (Z.ltb n 0) (Z.to_pos (Z.abs n)) (-8) with
  | SpecFloat.S754_zero _ => Some 0
  | SpecFloat.S754_finite sign m e =>
      if Z.leb (-4) e then
        let v := Z.pos m * 2 ^ (e + 4) in
        Some (if sign then -v else v)
      else None
  | _ => None
  end.

Definition same (a b : option Z) : bool :=
  match a, b with Some x, Some y => Z.eqb x y | _, _ => false end.
Definition modes := [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA].

Example boundary_oracle :
  oracle mode_NE 8 = Some 0 /\ oracle mode_NA 8 = Some 1 /\
  oracle mode_NE 288 = Some 16 /\ oracle mode_NE 352 = Some 24 /\
  oracle mode_NE (-352) = Some (-24) /\ oracle mode_DN (-1) = Some (-1) /\
  oracle mode_UP 1 = Some 1 /\ oracle mode_NE (-3328) = Some (-192) /\
  oracle mode_NA (-3328) = Some (-224).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example exhaustive_finite_grid :
  forallb (fun mode => forallb (fun k =>
    let n := Z.of_nat k - 3584 in same (observed mode n) (oracle mode n)) (seq 0 7169)) modes = true.
Proof. vm_compute. reflexivity. Qed.
