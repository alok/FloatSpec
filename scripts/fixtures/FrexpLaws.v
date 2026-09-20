From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
Module S := BinarySingleNaN.

Definition finiteMember (prec emax : Z) (m : positive) (e : Z) : bool :=
  let emin := 3 - emax - prec in
  andb (Z.ltb (Z.pos m) (2 ^ prec))
    (andb (Z.leb emin e) (andb (Z.leb e (emax - prec))
      (orb (Z.eqb e emin) (Z.leb (2 ^ (prec - 1)) (Z.pos m))))).

Definition compareDyadic (m e n f : Z) : comparison :=
  if Z.leb e f then Z.compare m (n * 2 ^ (f - e))
  else Z.compare (m * 2 ^ (e - f)) n.

Definition standardEq (x y : SpecFloat.spec_float) : bool :=
  match x, y with
  | SpecFloat.S754_nan, SpecFloat.S754_nan => true
  | SpecFloat.S754_finite s m e, SpecFloat.S754_finite t n f =>
      andb (Bool.eqb s t) (andb (Pos.eqb m n) (Z.eqb e f))
  | _, _ => false
  end.

Definition checkCase (pm : nat) (emax : Z) (s : bool) (m : positive) (e : Z) : bool :=
  let prec := Z.pos (Pos.of_nat (Datatypes.S pm)) in
  let raw := SpecFloat.S754_finite s m e in
  let x := @S.SF2B' prec emax raw in
  let converted := @S.B2SF prec emax x in
  let f := @S.Bfrexp prec emax eq_refl x in
  let fraction := @S.B2SF prec emax (fst f) in
  if finiteMember prec emax m e then
    andb (standardEq converted raw)
      (match fraction with
       | SpecFloat.S754_finite fs fm fe =>
           andb (Bool.eqb fs s) (andb (finiteMember prec emax fm fe)
             (andb (match compareDyadic (Z.pos m) e (Z.pos fm) (fe + snd f) with Eq => true | _ => false end)
               (orb (Z.leb emax 2)
                 (andb (match compareDyadic (Z.pos fm) fe 1 (-1) with Lt => false | _ => true end)
                       (match compareDyadic (Z.pos fm) fe 1 0 with Lt => true | _ => false end)))))
       | _ => false
       end)
  else andb (andb (standardEq converted SpecFloat.S754_nan) (standardEq fraction SpecFloat.S754_nan))
         (Z.eqb (snd f) (-2 * emax - prec)).

Definition formats : list (nat * Z) :=
  [(0%nat, 2); (2%nat, 3); (7%nat, 2); (7%nat, 3); (0%nat, -3); (7%nat, 0); (7%nat, 1)].

Definition checks : list (bool * bool) :=
  flat_map (fun format =>
    let pm := fst format in let emax := snd format in
    let prec := Z.pos (Pos.of_nat (Datatypes.S pm)) in
    let emin := 3 - emax - prec in
    flat_map (fun s => flat_map (fun index =>
      let m := Pos.of_nat (Datatypes.S index) in
      map (fun offset => let e := emin - 1 + Z.of_nat offset in
        (finiteMember prec emax m e, checkCase pm emax s m e))
        (seq 0 (Nat.max 1 (Z.to_nat (2 * emax)))))
      (seq 0 (Nat.pow 2 (Datatypes.S pm)))) [false; true]) formats.

Example decomposition_domain_laws :
  length checks = 6772%nat /\ length (filter (@fst bool bool) checks) = 2086%nat /\
  forallb (@snd bool bool) checks = true.
Proof. vm_compute. auto. Qed.

Eval vm_compute in (length checks, length (filter (@fst bool bool) checks), forallb (@snd bool bool) checks).
