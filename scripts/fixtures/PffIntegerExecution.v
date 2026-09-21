From Stdlib Require Import ZArith List.
From Flocq Require Import Pff.Pff.
Import ListNotations.
Open Scope Z_scope.

Definition quotientObserve (numerator denominator : Z) : list Z :=
  [Pff.Zquotient numerator denominator].

Definition optionFields (value : Pff.Option positive) : list Z :=
  (match value with | Pff.None => [0; 0] | Pff.Some p => [1; Zpos p] end) ++
    [Z.of_nat (Pff.oZ value); Pff.oZ1 value].

Definition positiveDivisionObserve (numerator denominator : Z) : list Z :=
  let result := Pff.Pdiv (Z.to_pos numerator) (Z.to_pos denominator) in
  optionFields (fst result) ++ optionFields (snd result).

Definition optionObserve (value : Z) : list Z :=
  optionFields (if Z.eqb value 0 then Pff.None positive else
    Pff.Some positive (Z.to_pos value)).

Definition dividesObserve (value divisor : Z) : list Z :=
  [if Pff.ZdividesP value divisor then 1 else 0].

Definition maxDivObserve (radix value bound : Z) : list Z :=
  [Z.of_nat (Pff.maxDiv radix value (Z.to_nat bound))].

(* Standalone tests follow; the bridge imports only the observation prefix. *)
Example signed_quotient_literals :
  [Pff.Zquotient (-7) 3; Pff.Zquotient 7 (-3); Pff.Zquotient (-7) (-3);
   Pff.Zquotient 7 3; Pff.Zquotient (-7) 0; Pff.Zquotient 0 0] = [-2;-2;2;2;0;0].
Proof. vm_compute. reflexivity. Qed.

Example positive_division_literals :
  [positiveDivisionObserve 1 1; positiveDivisionObserve 1 3;
   positiveDivisionObserve 7 3] =
  [[1;1;1;1;0;0;0;0]; [0;0;0;0;1;1;1;1]; [1;2;2;2;1;1;1;1]].
Proof. vm_compute. reflexivity. Qed.

Example option_literals :
  [optionObserve 0; optionObserve 1; optionObserve 7] =
  [[0;0;0;0]; [1;1;1;1]; [1;7;7;7]].
Proof. vm_compute. reflexivity. Qed.

Print Assumptions signed_quotient_literals.
Print Assumptions positive_division_literals.
Print Assumptions option_literals.

Example maxDiv_literals :
  [Pff.maxDiv 2 8 7; Pff.maxDiv 2 0 7; Pff.maxDiv 0 7 7; Pff.maxDiv 0 0 7;
   Pff.maxDiv (-2) (-8) 7; Pff.maxDiv 1 7 7; Pff.maxDiv 3 81 2] = [3;7;0;7;3;7;2]%nat.
Proof. vm_compute. reflexivity. Qed.
Example divides_literals :
  [dividesObserve 0 0; dividesObserve 1 0; dividesObserve 6 3;
   dividesObserve 3 6; dividesObserve (-6) (-3)] = [[1];[0];[1];[0];[1]].
Proof. vm_compute. reflexivity. Qed.
Check (Pff.maxDiv : Z -> Z -> nat -> nat).
Check (Pff.ZdividesP : forall value divisor : Z,
  {Pff.Zdivides value divisor} + {~Pff.Zdivides value divisor}).
Print Assumptions maxDiv_literals.
Print Assumptions divides_literals.
