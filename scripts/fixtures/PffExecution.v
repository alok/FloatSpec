From Stdlib Require Import ZArith List.
Require Import Flocq.Pff.Pff.
Import ListNotations.
Open Scope Z_scope.

Definition bound := Pff.Bound 9 10.
Definition input := Pff.Float 1 0.
Definition pair (p : Pff.float) : list Z := [Pff.Fnum p; Pff.Fexp p].

(* Mirrors all eighteen Lean integer APIs; normalized legacy APIs explicitly
   use type radix two, rather than pretending to consume the ignored three. *)
Example integer_api_values :
  [Zpower_nat 3 2; Zpower_nat 3 2; Pff.nNormMin 3 2; Pff.pPred 9] ++
  pair (Pff.firstNormalPos 3 bound 2) ++
  [Z.of_nat (Pff.digit 3 8); Z.of_nat (Pff.Fdigit 3 input)] ++
  pair (Pff.Fshift 3 1 input) ++ pair (Pff.FSucc bound 3 2 input) ++
  pair (Pff.FPred bound 3 2 input) ++ pair (Pff.Fnormalize 3 bound 2 input) ++
  pair (Pff.FNSucc bound 2 2 input) ++ pair (Pff.FNPred bound 2 2 input) ++
  [Z.of_nat (Pff.digit 3 8)] ++ pair (Pff.boundNat 3 8) ++
  pair (Pff.boundNat 3 8) ++ [Pff.nNormMin 3 2] ++
  pair (Pff.firstNormalPos 3 bound 2) =
  [9; 9; 3; 8; 3; -10; 2; 1; 3; -1; 2; 0; 0; 0; 3; -1;
   3; -1; 8; -2; 2; 1; 2; 1; 2; 3; 3; -10].
Proof. vm_compute. reflexivity. Qed.

Example distinct_radix_neighbors :
  [Pff.FNSucc bound 3 2 input; Pff.FNPred bound 3 2 (Pff.Float 2 0);
   Pff.FNSucc bound 2 2 input; Pff.FNPred bound 2 2 (Pff.Float 2 0)] =
  [Pff.Float 4 (-1); Pff.Float 5 (-1); Pff.Float 3 (-1); Pff.Float 8 (-1)].
Proof. vm_compute. reflexivity. Qed.

Example source_normalized_parity :
  Pff.FNodd bound 3 2 input /\ ~ Pff.FNeven bound 3 2 input.
Proof.
  split.
  - exists 1. vm_compute. reflexivity.
  - intro H. change (Z.Even 3) in H.
    apply Z.even_spec in H. discriminate.
Qed.
