From Stdlib Require Import Reals ZArith.
From Flocq Require Import Pff.Pff.
Open Scope Z_scope.

(* Rocq side of the typed clients in PffStatementContracts.lean. *)

Check (FnormalUnique : forall radix : Z, 1 < radix ->
  forall (b : Fbound) (precision : nat), precision <> 0%nat ->
  Z.pos (vNum b) = Zpower_nat radix precision ->
  forall p q : float, Fnormal radix b p -> Fnormal radix b q ->
  FtoR radix p = FtoR radix q -> p = q).

Check (ImplyClosest : forall (b : Fbound) (radix : Z) (p : nat), 1 < radix ->
  Z.pos (vNum b) = Zpower_nat radix p -> (1 < p)%nat ->
  forall (z : R) (f : float) (e : Z), Fbounded b f -> Fcanonic radix b f ->
  (powerRZ radix (e + p - 1) <= z)%R ->
  (powerRZ radix (e + p - 1) <= FtoR radix f)%R ->
  - dExp b <= e ->
  (Rabs (z - FtoR radix f) <= powerRZ radix e / 2)%R ->
  Closest b radix z f).

Check (errorBoundedMult : forall (b : Fbound) (radix : Z) (precision : nat),
  1 < radix -> (1 < precision)%nat ->
  Z.pos (vNum b) = Zpower_nat radix precision ->
  forall P : R -> float -> Prop, RoundedModeP b radix P ->
  forall p q f : float, Fbounded b p -> Fbounded b q ->
  - dExp b <= Fexp p + Fexp q ->
  P (FtoR radix p * FtoR radix q)%R f ->
  exists r : float, FtoR radix r = (FtoR radix p * FtoR radix q - FtoR radix f)%R /\
    Fbounded b r /\ Fexp r = Fexp p + Fexp q).

Check (discri3 : forall (bo : Fbound) (precision : nat), (1 < precision)%nat ->
  Z.pos (vNum bo) = Zpower_nat 2 precision ->
  forall a b b' c p q t dp dq s d : float, Fbounded bo p -> Fbounded bo q ->
  (0 <= FtoR 2 b * FtoR 2 b')%R ->
  EvenClosest bo 2 precision (FtoR 2 b * FtoR 2 b') p ->
  (3 * Rabs (FtoR 2 p - FtoR 2 q) < FtoR 2 p + FtoR 2 q)%R ->
  EvenClosest bo 2 precision (FtoR 2 p - FtoR 2 q) t ->
  FtoR 2 dp = (FtoR 2 b * FtoR 2 b' - FtoR 2 p)%R ->
  FtoR 2 dq = (FtoR 2 a * FtoR 2 c - FtoR 2 q)%R ->
  EvenClosest bo 2 precision (FtoR 2 dp - FtoR 2 dq) s ->
  EvenClosest bo 2 precision (FtoR 2 t + FtoR 2 s) d ->
  (exists f : float, Fbounded bo f /\ FtoR 2 f = (FtoR 2 dp - FtoR 2 dq)%R) ->
  (Rabs (FtoR 2 d - (FtoR 2 b * FtoR 2 b' - FtoR 2 a * FtoR 2 c)) <=
    2 * Fulp bo 2 precision d)%R).

Check (eqExpLess : forall radix : Z, 1 < radix ->
  forall (b : Fbound) (p q : float), Fbounded b p -> FtoR radix p = FtoR radix q ->
  exists r : float, Fbounded b r /\ FtoR radix r = FtoR radix q /\
    (Fexp q <= Fexp r)%R).
