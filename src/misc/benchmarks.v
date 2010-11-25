Require Import 
  BigZ BigQ fast_integers positive_integers_naturals
  fast_rationals
  abstract_algebra interfaces.integers interfaces.rationals 
  interfaces.additional_operations interfaces.appfield
  dyadics dyadics_appfield.

Check (_ : Integers fastZ).
Check (_ : ∀ (x y : fastZ), Decision (x = y)).
Check (_ : ∀ (x y : Pos fastZ), Decision (x = y)).
Check (_ : ∀ (x y : fastZ), Decision (x ≤ y)).
Check (_ : ∀ (x y : Pos fastZ), Decision (x ≤ y)).
Check (_ : NatPow fastZ (Pos fastZ)).
Check (_ : ShiftLeft fastZ (Pos fastZ)). 
Check (_ : ShiftRight fastZ (Pos fastZ)). 
Check (_ : RingMinus fastZ).
Check (_ : CutMinus fastZ).
Check (_ : Log (2:fastZ) (Pos fastZ)).
Check (_ : DivEuclid fastZ).
Check (_ : RingMinus fastZ).
Check (_ : CutMinus fastZ).
Check (_ : CutMinus (Pos fastZ)).

Definition D : Dyadic fastZ := (2331%bigZ) $ (14%bigZ).
Definition E : Dyadic fastZ := (215%bigZ) $ (-132%bigZ).

Definition Q1 : fastQ := (1#3)%bigQ.

Program Definition Y : Pos fastZ := 256%bigZ.
Next Obligation.  Admitted.

Time Eval vm_compute in (QtoD Q1 Y).
Time Eval vm_compute in (((QtoD Q1 Y) * (3%bigZ $ 0))).
Time Eval vm_compute in (DtoQ (
  ((QtoD Q1 Y) ✖ (3%bigZ $ 0)) Y
)).
Time Eval vm_compute in (Q1 * (3#1)%bigQ).
Time Eval vm_compute in (((QtoD Q1 Y) ✖ (3%bigZ $ 0)) Y).
Time Eval vm_compute in (DtoQ (
  ((QtoD Q1 Y) ✚ (3%bigZ $ 0)) Y
)).
Time Eval vm_compute in (D + E).
Time Eval vm_compute in ((D ✚ E) Y).

Program Definition D2 : { z : Dyadic fastZ | ~dy_eq z 0} := D.
Next Obligation.  Admitted.

Program Definition Y2 : Pos fastZ := 45%bigZ.
Next Obligation. Admitted.
Eval vm_compute in ((/// D2) Y2).

Check (_ : Integers Z).
Check (_ : ∀ (x y : Z), Decision (x = y)).
Check (_ : ∀ (x y : Z), Decision (x ≤ y)).
Check (_ : NatPow Z (Pos Z)).
Check (_ : ShiftLeft Z (Pos Z)). 
Check (_ : RingMinus Z).
Check (_ : CutMinus Z).

Definition DZ : Dyadic Z := (233123124123412343%Z) # (12314%Z).
Definition EZ : Dyadic Z := (2151453412523525234%Z) # (-13152%Z).
Time Eval vm_compute in (DZ + EZ).
(* log2 and div_euclid aren't implemented for Z yet, so we can't test ✚ *)