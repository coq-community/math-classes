Require Import 
  BigZ fast_integers positive_integers_naturals
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

Definition D : Dyadic fastZ := (233123124123412343%bigZ) # (12314%bigZ).
Definition E : Dyadic fastZ := (2151453412523525234%bigZ) # (-13152%bigZ).

Program Definition Y : Pos fastZ := 5%bigZ.
Next Obligation.  Admitted.

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