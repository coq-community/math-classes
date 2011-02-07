Require
  theory.rings.
Require Import
  Morphisms Ring Setoid Program
  abstract_algebra.

Inductive SRpair (SR : Type) : Type := C { pos : SR ; neg : SR }.
Implicit Arguments C [[SR]].
Implicit Arguments pos [[SR]].
Implicit Arguments neg [[SR]].

Section semiring_pairs.
Context `{SemiRing SR}.
Context `{∀ z, LeftCancellation (+) z}.

Add Ring SR : (rings.stdlib_semiring_theory SR).

(* Equivalence *)
Global Instance SRpair_equiv : Equiv (SRpair SR) := λ x y, pos x + neg y = pos y + neg x.

Instance: Setoid (SRpair SR).
Proof with auto.
  split; red; unfold equiv, SRpair_equiv.
    reflexivity.
   intros. symmetry...
  intros x y z E E'.
  rewrite commutativity.
  rewrite (commutativity (pos z)).
  apply (left_cancellation (+) (pos y)).
  do 2 rewrite associativity.
  rewrite <- E, E'. ring.
Qed.

Global Instance SRpair_dec `{∀ x y : SR, Decision (x = y)} : ∀ x y : SRpair SR, Decision (x = y)
  := λ x y, decide_rel (=) (pos x + neg y) (pos y + neg x).

Instance: Proper ((=) ==> (=) ==> (=)) C.
Proof.
  intros x1 y1 E1 x2 y2 E2. unfold equiv, SRpair_equiv. simpl.
  rewrite E1, E2. reflexivity.
Qed.

(* injection from SR *)
Global Instance SRpair_inject: Inject SR (SRpair SR) := λ r, C r 0.

Global Instance: Proper ((=) ==> (=)) inject.
Proof. intros x1 x2 E. unfold inject, equiv, SRpair_equiv. simpl. rewrite E. reflexivity. Qed.

(* Relations, operations and constants *)
Global Instance SRpair_plus: RingPlus (SRpair SR) := λ x y, C (pos x + pos y) (neg x + neg y).
Global Instance SRpair_opp: GroupInv (SRpair SR) := λ x, C (neg x) (pos x).
Global Instance SRpair_0: RingZero (SRpair SR) := ('0 : SRpair SR).
Global Instance SRpair_mult: RingMult (SRpair SR) := λ x y, C (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y).
Global Instance SRpair_1: RingOne (SRpair SR) := ('1 : SRpair SR).

Ltac unfolds := unfold SRpair_opp, SRpair_plus, equiv, SRpair_equiv in *; simpl in *.
Ltac ring_on_sr := repeat intro; unfolds; try ring.

Instance: Proper ((=) ==> (=)) SRpair_opp.
Proof. 
  intros x y E. unfolds. 
  rewrite commutativity, <- E. ring.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) SRpair_plus.
Proof with try ring.
  intros x1 y1 E1 x2 y2 E2. unfolds.
  transitivity (pos x1 + neg y1 + (pos x2 + neg y2))...
  rewrite E1, E2...
Qed.

Let SRpair_mult_compat_r (y1 y2 : SRpair SR) : y1 = y2 → ∀ x, x * y1 = x * y2.
Proof with try ring.
  intros E x. unfolds.
  transitivity (pos x * (pos y1 + neg y2) + neg x * (pos y2 + neg y1))...
  transitivity (pos x * (pos y2 + neg y1) + neg x * (pos y1 + neg y2))...
  rewrite E. reflexivity.
Qed.

Instance: Commutative SRpair_mult. 
Proof. repeat intro. ring_on_sr. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) SRpair_mult.
Proof with auto.
  intros x1 y1 E1 x2 y2 E2.
  transitivity (x1 * y2).
   apply SRpair_mult_compat_r...
 rewrite commutativity.
 rewrite (commutativity y1).
 apply SRpair_mult_compat_r...
Qed.

Global Instance: Ring (SRpair SR).
Proof. repeat (split; try apply _); ring_on_sr. Qed.

(* A final word about inject *)
Global Instance: SemiRing_Morphism inject.
Proof.
  repeat (constructor; try apply _); try reflexivity.
   intros x y. change (x + y + (0 + 0) = x + y + 0). ring.
  intros x y. change (x * y + (x * 0 + 0 * y) = x * y + 0 * 0 + 0). ring.
Qed.

Global Instance: Injective inject.
Proof. 
  repeat (constructor; try apply _).
  intros x y. unfolds. do 2 rewrite rings.plus_0_r. auto.
Qed.

Lemma SRpair_splits n m : C n m = 'n + -'m.
Proof. ring_on_sr. Qed.

Context `{!SemiRingOrder o}.

Global Instance SRpair_order : Order (SRpair SR) := λ x y, pos x + neg y ≤ pos y + neg x.

Instance: Proper ((=) ==> (=) ==> iff) SRpair_order.
Proof with trivial; try ring.
  assert (∀ x1 y1 : SRpair SR, x1 = y1 → ∀ x2 y2, x2 = y2 → x1 ≤ x2 → y1 ≤ y2) as E.
    unfold precedes, SRpair_order, equiv, SRpair_equiv.
   intros [xp1 xn1] [yp1 yn1] E1 [xp2 xn2] [yp2 yn2] E2 F. simpl in *.
   apply srorder_plus in F. destruct F as [c [Ec1 Ec2]].
   apply srorder_plus. exists c. split...
   apply (left_cancellation (+) (xp2 + xp1)).
   transitivity (xp1 + yn1 + (yp2 + xp2))...
   rewrite E1.
   transitivity (xp2 + xn1 + (yp2 + yp1))...
   rewrite Ec2.
   transitivity (yp2 + xn2 + c + (xp1 + yp1))...
   rewrite <-E2...
  split; repeat intro; eapply E; eauto; symmetry; eauto.
Qed.

Instance: OrderPreserving inject.
Proof.
  repeat (split; try apply _).
  intros x y E. unfold precedes, SRpair_order. simpl.
  do 2 rewrite rings.plus_0_r. assumption.
Qed.

Instance SRpair_order_back: OrderPreservingBack inject.
Proof.
  repeat (split; try apply _).
  intros x y E. unfold precedes, SRpair_order in E. simpl in E.
  do 2 rewrite rings.plus_0_r in E. assumption.
Qed.

Global Instance: OrderEmbedding inject.

Instance: Reflexive SRpair_order.
Proof. intros [? ?]. unfold SRpair_order. reflexivity. Qed.

Instance: Transitive SRpair_order.
Proof with trivial; try ring.
  intros [xp xn] [yp yn] [zp zn] E1 E2. 
  unfold SRpair_order in *. simpl in *.
  apply srorder_plus in E1. destruct E1 as [a [Ea1 Ea2]].
  apply srorder_plus in E2. destruct E2 as [b [Eb1 Eb2]].
  apply srorder_plus. exists (a + b).
  split.
   transitivity a... apply srorder_plus. exists b; split...
  apply (left_cancellation (+) (yn + yp)).
  transitivity ((yp + xn) + (zp + yn))...
  rewrite Ea2, Eb2...
Qed.

Instance: AntiSymmetric SRpair_order.
Proof. 
  intros [xp xn] [yp yn] E1 E2. 
  unfold equiv, SRpair_equiv. apply (antisymmetry (≤)); assumption.
Qed.

Instance: ∀ z : SRpair SR, OrderPreserving ((+) z).
Proof with trivial; try ring.
  repeat (split; try apply _).
  unfold precedes, SRpair_order.
  destruct z as [zp zn]. intros [xp xn] [yp yn] E. simpl in *.
  apply srorder_plus in E. destruct E as [c [Ec1 Ec2]].
  apply srorder_plus. exists c. split...
  transitivity ((yp + xn) + (zn + zp))...
  rewrite Ec2...
Qed.

Global Instance: RingOrder SRpair_order.
Proof with trivial; try ring.
  repeat (split; try apply _).
  unfold precedes, SRpair_order.
  intros [xp xn] E1 [yp yn] E2. simpl in *.
  ring_simplify in E1. ring_simplify in E2.
  apply srorder_plus in E1. apply srorder_plus in E2.
  destruct E1 as [a [Ea1 Ea2]], E2 as [b [Eb1 Eb2]].
  rewrite Ea2, Eb2. ring_simplify.
  apply srorder_plus. exists (a * b). split... 
  apply srorder_mult; assumption.
Qed. 

Global Program Instance SRpair_le_dec `{∀ x y: SR, Decision (x ≤ y)} : ∀ x y : SRpair SR, Decision (x ≤ y) := λ x y,
  match decide_rel (≤) (pos x + neg y) (pos y + neg x) with
  | left E => left _
  | right E => right _
  end. 

Global Instance SRpair_total `{!TotalOrder o} : TotalOrder SRpair_order.
Proof.
  intros [xp xn] [yp yn]. 
  unfold precedes, SRpair_order.
  apply total_order.
Qed.
End semiring_pairs.
