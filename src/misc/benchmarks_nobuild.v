Require Import 
  BigZ BigQ fast_integers nonneg_integers_naturals
  fast_rationals
  abstract_algebra interfaces.integers interfaces.rationals 
  interfaces.additional_operations (* interfaces.appfield *)
  dyadics (* dyadics_appfield *).

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

Definition D : Dyadic fastZ := (233123124123412343%bigZ) $ (12314%bigZ).
Definition E : Dyadic fastZ := (2151453412523525234%bigZ) $ (-13152%bigZ).
Program Definition Y : fastZ⁺ := 256%bigZ.
Next Obligation. Admitted.

Time Eval vm_compute in (D + E).
Time Eval vm_compute in ((D ✚ E) Y).

Definition Q1 : fastQ := (1#3)%bigQ.

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

Definition DyadicNeZero := sig (λ z : Dyadic fastZ , z ≠ 0).

Program Definition D2 : DyadicNeZero := D.
Next Obligation.  Admitted.

Program Definition Y2 : Pos fastZ := 45%bigZ.
Next Obligation. Admitted.
Eval vm_compute in ((/// D2) Y2).

(* Ad hoc implementation of Euler *)
Program Fixpoint euler_aux (x : Dyadic fastZ) (n : nat) (m : DyadicNeZero) (ε : Pos fastZ) {struct n} : Dyadic fastZ := 
  match n with 
  | O => 1
  | S n' => 1 + (((x ✖ ((/// m) ε)) ε) ✖ (euler_aux x n' (exist _ (1 + proj1_sig m) _) ε)) ε
  end.
Next Obligation. Admitted.

Program Definition D3 : DyadicNeZero := (1:Dyadic fastZ).
Next Obligation.  Admitted.

Program Definition Y3 : Pos fastZ := 90%bigZ.
Next Obligation.  Admitted.

(* Extremely hacky way to display a dyadic in a readable way *)
Program Definition answer (n : fastZ) (x : Dyadic fastZ) : fastZ :=
 div_euclid (mant x * (10%bigZ) ^ (int_abs fastZ (Pos fastZ) n)) (exist _ (1 ≪ int_abs fastZ (Pos fastZ) (expo x)) _).
Next Obligation. Admitted.

Time Eval vm_compute in (answer (20%bigZ) (euler_aux (euler_aux 2 50 D3 Y3) 50 D3 Y3)).
Time Eval vm_compute in (answer (20%bigZ) (euler_aux (euler_aux (euler_aux (1$(-1%bigZ)) 45 D3 Y3) 45 D3 Y3) 45 D3 Y3)).

Definition fastQNeZero := sig (λ z : fastQ, z ≠ 0).

Program Fixpoint eulerQ_aux (x : fastQ) (n : nat) (m : fastQNeZero) {struct n} : fastQ := 
  match n return fastQ with 
  | O => 1
  | S n' => 1 + x * ((eulerQ_aux x n' (exist _ (1 + proj1_sig m) _)) // m)
  end.
Next Obligation. Admitted.

Time Eval vm_compute in (eulerQ_aux (eulerQ_aux 2 300 1) 300 1).

Check (_ : Integers Z).
Check (_ : ∀ (x y : Z), Decision (x = y)).
Check (_ : ∀ (x y : Z), Decision (x ≤ y)).
Check (_ : NatPow Z (Pos Z)).
Check (_ : ShiftLeft Z (Pos Z)). 
Check (_ : RingMinus Z).
Check (_ : CutMinus Z).

Definition DZ : Dyadic Z := (233123124123412343%Z) $ (12314%Z).
Definition EZ : Dyadic Z := (2151453412523525234%Z) $ (-13152%Z).
Time Eval vm_compute in (DZ + EZ).

(* log2 and div_euclid aren't implemented for Z yet, so we can't test ✚ *)