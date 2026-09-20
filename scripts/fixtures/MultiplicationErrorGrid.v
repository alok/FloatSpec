From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition positiveValues : list (positive * Z) :=
  [(1%positive, -4); (2%positive, -4); (3%positive, -4)] ++
  flat_map (fun shift => map (fun m => (m, Z.of_nat shift - 4))
    [4%positive; 5%positive; 6%positive; 7%positive]) (seq 0 6).

Definition inputUnits (s : bool) (m : positive) (e : Z) : Z :=
  let u := Z.pos m * 2 ^ (e + 4) in if s then -u else u.

Definition inputs : list (Z * binary_float 3 4) :=
  [(0, @B754_zero 3 4 false)] ++ flat_map (fun s =>
    map (fun pair => (inputUnits s (fst pair) (snd pair),
      @SF2B' 3 4 (SpecFloat.S754_finite s (fst pair) (snd pair)))) positiveValues) [false; true].

Definition finiteUnits := map (@fst Z (binary_float 3 4)) inputs.

Definition units (x : SpecFloat.spec_float) : option Z :=
  match x with
  | SpecFloat.S754_zero _ => Some 0
  | SpecFloat.S754_finite s m e =>
      if Z.leb (-8) e then
        let u := Z.pos m * 2 ^ (e + 8) in Some (if s then -u else u)
      else None
  | _ => None
  end.

Definition pairs := filter (fun pair =>
  let product := fst (fst pair) * fst (snd pair) in
  andb (orb (Z.eqb product 0) (Z.leb 512 (Z.abs product))) (Z.leb (Z.abs product) 3584))
  (list_prod inputs inputs).

Definition checkPair (m : mode) (x y : Z * binary_float 3 4) : bool :=
  match units (@B2SF 3 4 (@Bmult 3 4 eq_refl eq_refl m (snd x) (snd y))) with
  | None => false
  | Some rounded =>
      let error := rounded - fst x * fst y in
      andb (Z.eqb (error mod 16) 0) (existsb (Z.eqb (error / 16)) finiteUnits)
  end.

Definition modes := [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA].

Example nonvacuous_grid :
  length inputs = 55%nat /\ length pairs = 1077%nat /\ length modes = 5%nat.
Proof. vm_compute. auto. Qed.

Example inputs_exact : forallb (fun pair =>
  match units (@B2SF 3 4 (snd pair)) with
  | Some u => Z.eqb u (16 * fst pair)
  | None => false
  end) inputs = true.
Proof. vm_compute. reflexivity. Qed.

Example multiplication_error_grid :
  forallb (fun m => forallb (fun pair => checkPair m (fst pair) (snd pair)) pairs) modes = true.
Proof. vm_compute. reflexivity. Qed.

Definition tiny := @SF2B' 3 4 (SpecFloat.S754_finite false 1 (-4)).

Example underflow_premise_matters :
  units (@B2SF 3 4 tiny) = Some 16 /\
  units (@B2SF 3 4 (@Bmult 3 4 eq_refl eq_refl mode_NE tiny tiny)) = Some 0 /\
  (-1) mod 16 <> 0 /\ checkPair mode_NE (1, tiny) (1, tiny) = false.
Proof. repeat split; vm_compute; congruence. Qed.

Eval vm_compute in (length inputs, (5 * length pairs)%nat).
