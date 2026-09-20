From Stdlib Require Import ZArith List Reals Psatz.
From Flocq Require Import Core.Zaux Core.Defs IEEE754.PrimFloat IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition ordering (c : option comparison) : Z :=
  match c with None => 2 | Some Lt => -1 | Some Eq => 0 | Some Gt => 1 end.
Definition boolean (b : bool) : Z := if b then 1 else 0.
Definition primitiveOrdering (c : PrimFloat.float_comparison) : Z :=
  match c with PrimFloat.FNotComparable => 2 | PrimFloat.FLt => -1
  | PrimFloat.FEq => 0 | PrimFloat.FGt => 1 end.

Definition inputs : list (SpecFloat.spec_float * SpecFloat.spec_float) :=
  [(SpecFloat.S754_finite false 3 (-1), SpecFloat.S754_finite false 6 (-2));
   (SpecFloat.S754_finite false 6 (-2), SpecFloat.S754_finite false 3 (-1));
   (SpecFloat.S754_finite true 3 (-1), SpecFloat.S754_finite true 6 (-2));
   (SpecFloat.S754_finite false 1 (1), SpecFloat.S754_finite false 16 (0));
   (SpecFloat.S754_finite false 4503599627370496 (-52), SpecFloat.S754_finite false 4503599627370496 (-51));
   (SpecFloat.S754_finite false 4503599627370496 (-51), SpecFloat.S754_finite false 4503599627370496 (-52));
   (SpecFloat.S754_finite false 4503599627370496 (-52), SpecFloat.S754_finite false 4503599627370496 (-52));
   (SpecFloat.S754_finite true 4503599627370496 (-52), SpecFloat.S754_finite false 4503599627370496 (-52));
   (SpecFloat.S754_zero false, SpecFloat.S754_zero true);
   (SpecFloat.S754_zero true, SpecFloat.S754_zero false);
   (SpecFloat.S754_nan, SpecFloat.S754_zero false);
   (SpecFloat.S754_finite false 4503599627370496 (-52), SpecFloat.S754_nan);
   (SpecFloat.S754_nan, SpecFloat.S754_nan);
   (SpecFloat.S754_infinity true, SpecFloat.S754_infinity false);
   (SpecFloat.S754_infinity false, SpecFloat.S754_infinity true);
   (SpecFloat.S754_infinity false, SpecFloat.S754_infinity false);
   (SpecFloat.S754_infinity true, SpecFloat.S754_finite false 4503599627370496 (-52));
   (SpecFloat.S754_finite false 4503599627370496 (-52), SpecFloat.S754_infinity false);
   (SpecFloat.S754_finite false 1 (-1074), SpecFloat.S754_zero false);
   (SpecFloat.S754_finite true 1 (-1074), SpecFloat.S754_zero true);
   (SpecFloat.S754_finite false 4503599627370495 (-1074), SpecFloat.S754_finite false 4503599627370496 (-1074));
   (SpecFloat.S754_finite false 9007199254740991 (971), SpecFloat.S754_infinity false);
   (SpecFloat.S754_finite false 1 (-1000000), SpecFloat.S754_finite false 1 (1000000));
   (SpecFloat.S754_finite false 1 (-1075), SpecFloat.S754_finite false 1 (-1074))].

Definition observe (rawX rawY : SpecFloat.spec_float) : list Z :=
  let x := @BinarySingleNaN.SF2B' 53 1024 rawX in
  let y := @BinarySingleNaN.SF2B' 53 1024 rawY in
  let px := Flocq.IEEE754.PrimFloat.B2Prim x in
  let py := Flocq.IEEE754.PrimFloat.B2Prim y in
  [ordering (SpecFloat.SFcompare rawX rawY);
   boolean (SpecFloat.SFeqb rawX rawY);
   boolean (SpecFloat.SFltb rawX rawY);
   boolean (SpecFloat.SFleb rawX rawY);
   boolean (SpecFloat.valid_binary 53 1024 rawX);
   boolean (SpecFloat.valid_binary 53 1024 rawY);
   primitiveOrdering (PrimFloat.compare px py);
   boolean (PrimFloat.eqb px py);
   boolean (PrimFloat.ltb px py);
   boolean (PrimFloat.leb px py);
   ordering (@BinarySingleNaN.Bcompare 53 1024 x y);
   boolean (@BinarySingleNaN.Beqb 53 1024 x y);
   boolean (@BinarySingleNaN.Bltb 53 1024 x y);
   boolean (@BinarySingleNaN.Bleb 53 1024 x y)].

Definition expected : list (list Z) :=
  [[1; 0; 0; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0];
   [-1; 0; 1; 1; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0];
   [-1; 0; 1; 1; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0];
   [1; 0; 0; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [1; 0; 0; 0; 1; 1; 1; 0; 0; 0; 1; 0; 0; 0];
   [0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1];
   [0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1];
   [2; 0; 0; 0; 1; 1; 2; 0; 0; 0; 2; 0; 0; 0];
   [2; 0; 0; 0; 1; 1; 2; 0; 0; 0; 2; 0; 0; 0];
   [2; 0; 0; 0; 1; 1; 2; 0; 0; 0; 2; 0; 0; 0];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [1; 0; 0; 0; 1; 1; 1; 0; 0; 0; 1; 0; 0; 0];
   [0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [1; 0; 0; 0; 1; 1; 1; 0; 0; 0; 1; 0; 0; 0];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [-1; 0; 1; 1; 1; 1; -1; 0; 1; 1; -1; 0; 1; 1];
   [-1; 0; 1; 1; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0];
   [-1; 0; 1; 1; 0; 1; 2; 0; 0; 0; 2; 0; 0; 0]].

Example literalObservations :
  map (fun '(x, y) => observe x y) inputs = expected.
Proof. vm_compute. reflexivity. Qed.

Example equalValues :
  SF2R radix2 (SpecFloat.S754_finite false 3 (-1)) =
  SF2R radix2 (SpecFloat.S754_finite false 6 (-2)).
Proof.
  unfold SF2R, F2R, Raux.bpow.
  change (3 * / 2 = 6 * / 4)%R.
  field.
Qed.

Example differentRawComparison :
  SpecFloat.SFcompare (SpecFloat.S754_finite false 3 (-1))
    (SpecFloat.S754_finite false 6 (-2)) = Some Gt.
Proof. vm_compute. reflexivity. Qed.
