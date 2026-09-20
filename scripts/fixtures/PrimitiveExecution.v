From Stdlib Require Import ZArith List Floats Uint63.
From Flocq Require Import IEEE754.PrimFloat IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
Definition bone := @BinarySingleNaN.Bone 53 1024 eq_refl eq_refl.
Definition outputs : list SpecFloat.spec_float :=
  [(* binary_round_aux *) SpecFloat.binary_round_aux 53 1024 false 1 0 SpecFloat.loc_Exact;
   (* SFmul *) SpecFloat.SFmul 53 1024 (FloatOps.Prim2SF PrimFloat.one) (FloatOps.Prim2SF PrimFloat.one);
   (* SFdiv *) SpecFloat.SFdiv 53 1024 (FloatOps.Prim2SF PrimFloat.one) (FloatOps.Prim2SF PrimFloat.one);
   (* binary_round *) SpecFloat.binary_round 53 1024 false 1%positive 0;
   (* binary_normalize *) SpecFloat.binary_normalize 53 1024 1 0 false;
   (* SFldexp *) SpecFloat.SFldexp 53 1024 (FloatOps.Prim2SF PrimFloat.one) 1;
   (* SFadd *) SpecFloat.SFadd 53 1024 (FloatOps.Prim2SF PrimFloat.one) (FloatOps.Prim2SF PrimFloat.one);
   (* mul *) FloatOps.Prim2SF (PrimFloat.mul PrimFloat.one PrimFloat.one);
   (* div *) FloatOps.Prim2SF (PrimFloat.div PrimFloat.one PrimFloat.one);
   (* sqrt *) FloatOps.Prim2SF (PrimFloat.sqrt PrimFloat.one);
   (* of_uint63 *) FloatOps.Prim2SF (PrimFloat.of_uint63 (Uint63.of_Z 1));
   (* ldexp *) FloatOps.Prim2SF (FloatOps.Z.ldexp PrimFloat.one 1);
   (* Z_ldexp *) FloatOps.Prim2SF (FloatOps.Z.ldexp PrimFloat.one 1);
   (* Z_frexp *) FloatOps.Prim2SF (fst (FloatOps.Z.frexp PrimFloat.one));
   (* ldshiftexp *) FloatOps.Prim2SF (PrimFloat.ldshiftexp PrimFloat.one (Uint63.of_Z 2102));
   (* frshiftexp *) FloatOps.Prim2SF (fst (PrimFloat.frshiftexp PrimFloat.one));
   (* ulp *) FloatOps.Prim2SF (FloatOps.ulp PrimFloat.one);
   (* next_up *) FloatOps.Prim2SF (Corelib.Floats.PrimFloat.next_up PrimFloat.one);
   (* next_down *) FloatOps.Prim2SF (Corelib.Floats.PrimFloat.next_down PrimFloat.one);
   (* add *) FloatOps.Prim2SF (PrimFloat.add PrimFloat.one PrimFloat.one);
   (* two *) FloatOps.Prim2SF PrimFloat.two;
   (* sub *) FloatOps.Prim2SF (PrimFloat.sub PrimFloat.one PrimFloat.one);
   (* Mul_instance *) FloatOps.Prim2SF (PrimFloat.mul PrimFloat.one PrimFloat.one);
   (* Div_instance *) FloatOps.Prim2SF (PrimFloat.div PrimFloat.one PrimFloat.one);
   (* Add_instance *) FloatOps.Prim2SF (PrimFloat.add PrimFloat.one PrimFloat.one);
   (* Sub_instance *) FloatOps.Prim2SF (PrimFloat.sub PrimFloat.one PrimFloat.one);
   (* Bmult *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bmult 53 1024 eq_refl eq_refl mode_NE bone bone);
   (* Bdiv *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bdiv 53 1024 eq_refl eq_refl mode_NE bone bone);
   (* Bsqrt *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bsqrt 53 1024 eq_refl eq_refl mode_NE bone);
   (* binary_normalize_bsn *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 0 false);
   (* Bldexp *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bldexp 53 1024 eq_refl eq_refl mode_NE bone 1);
   (* Bfrexp *) @BinarySingleNaN.B2SF 53 1024 (fst (@BinarySingleNaN.Bfrexp 53 1024 eq_refl bone));
   (* Bulp *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bulp' 53 1024 eq_refl eq_refl bone);
   (* Bsucc *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bsucc 53 1024 eq_refl eq_refl bone);
   (* Bpred *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bpred 53 1024 eq_refl eq_refl bone);
   (* Bplus *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bplus 53 1024 eq_refl eq_refl mode_NE bone bone);
   (* Bminus *) @BinarySingleNaN.B2SF 53 1024 (@BinarySingleNaN.Bminus 53 1024 eq_refl eq_refl mode_NE bone bone)].
Definition expected : list SpecFloat.spec_float :=
  [SpecFloat.S754_finite false 1 (0);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-53);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-53);
   SpecFloat.S754_finite false 4503599627370496 (-104);
   SpecFloat.S754_finite false 4503599627370497 (-52);
   SpecFloat.S754_finite false 9007199254740991 (-53);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_zero false;
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_zero false;
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_finite false 4503599627370496 (-53);
   SpecFloat.S754_finite false 4503599627370496 (-104);
   SpecFloat.S754_finite false 4503599627370497 (-52);
   SpecFloat.S754_finite false 9007199254740991 (-53);
   SpecFloat.S754_finite false 4503599627370496 (-51);
   SpecFloat.S754_zero false].
Example each_entry_point_matches_literal : outputs = expected.
Proof. vm_compute. reflexivity. Qed.
Example decomposition_exponents :
    snd (FloatOps.Z.frexp PrimFloat.one) = 1 /\
    Uint63.to_Z (snd (PrimFloat.frshiftexp PrimFloat.one)) = 2102 /\
    snd (@BinarySingleNaN.Bfrexp 53 1024 eq_refl bone) = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition raw_product := SpecFloat.SFmul 53 1024
  (SpecFloat.S754_finite false 3 (-1)) (SpecFloat.S754_finite false 3 (-1)).
Definition primitive_product :=
  let x := FloatOps.SF2Prim (SpecFloat.S754_finite false 3 (-1)) in
  FloatOps.Prim2SF (PrimFloat.mul x x).
Example raw_and_converted_arithmetic_have_distinct_encodings :
    raw_product = SpecFloat.S754_finite false 9 (-2) /\
    primitive_product = SpecFloat.S754_finite false 5066549580791808 (-51) /\
    SpecFloat.valid_binary 53 1024 raw_product = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
