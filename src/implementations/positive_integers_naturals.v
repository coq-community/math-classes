Require Import
  Morphisms Ring Program RelationClasses
  abstract_algebra
  interfaces.integers
  interfaces.naturals
  canonical_names
  theory.integers theory.rings theory.naturals
  orders.semiring
  peano_naturals.

Section positive_integers_naturals.
Context Z `{Integers Z}.

Add Ring Z: (stdlib_ring_theory Z).

Definition ZPos := { z : Z | 0 ≤ z }.

Local Ltac unfold_equivs := unfold equiv, sig_equiv, sig_relation in *; simpl in *.

(* Operations *)
Global Program Instance ZPos_plus: RingPlus ZPos := λ x y, exist _ (`x + `y) _. 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  simpl. unfold "≤".  unfold integer_precedes. 
  apply sr_precedes_nonneg_plus_compat...
Qed.

Global Program Instance ZPos_mult: RingMult ZPos := λ x y, exist _ (`x * `y) _. 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  simpl. apply sr_precedes_nonneg_mult_compat...
Qed.

Global Program Instance ZPos_0: RingZero ZPos := exist _ 0 _.
Next Obligation. reflexivity. Qed. 

Global Program Instance ZPos_1: RingOne ZPos := exist _ 1 _.
Next Obligation. apply sr_precedes_0_1. Qed.
 
Global Instance: Proper (equiv ==> equiv ==> equiv) ZPos_plus.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs. 
  rewrite E1, E2. reflexivity.
Qed.

Global Instance: Proper (equiv ==> equiv ==> equiv) ZPos_mult.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs. 
  rewrite E1, E2. reflexivity.
Qed.

(* Properties: *)
Global Instance: Associative ZPos_plus.
Proof. intros [x Ex] [y Ey] [z Ez]. unfold_equivs. apply associativity. Qed.
Global Instance: Associative ZPos_mult. 
Proof. intros [x Ex] [y Ey] [z Ez]. unfold_equivs. apply associativity. Qed.
Global Instance: Commutative ZPos_plus.
Proof. intros [x Ex] [y Ey]. unfold_equivs. apply commutativity. Qed.
Global Instance: Commutative ZPos_mult.
Proof. intros [x Ex] [y Ey]. unfold_equivs. apply commutativity. Qed.
Global Instance: Distribute ZPos_mult ZPos_plus.
Proof. split; intros [x Ex] [y Ey] [z Ez]; unfold_equivs. apply distribute_l. apply distribute_r. Qed.
Global Instance: LeftIdentity ZPos_plus ZPos_0.
Proof. intros [x Ex]. unfold_equivs. apply left_identity. Qed.
Global Instance: RightIdentity ZPos_plus ZPos_0.
Proof. intros [x Ex]. unfold_equivs. apply right_identity. Qed.
Global Instance: LeftIdentity ZPos_mult ZPos_1.
Proof. intros [x Ex]. unfold_equivs. apply left_identity. Qed.
Global Instance: RightIdentity ZPos_mult ZPos_1.
Proof. intros [x Ex]. unfold_equivs. apply right_identity. Qed.
Global Instance: LeftAbsorb ZPos_mult ZPos_0.
Proof. intros [x Ex]. unfold_equivs. apply left_absorb. Qed.

(* Structures: *)
Global Instance: Setoid ZPos.
Global Instance: SemiGroup ZPos (op:=ZPos_plus).
Global Instance: SemiGroup ZPos (op:=ZPos_mult).
Global Instance: Monoid ZPos (op:=ZPos_plus) (unit:=ZPos_0).
Global Instance: Monoid ZPos (op:=ZPos_mult) (unit:=ZPos_1).
Global Instance: CommutativeMonoid ZPos (op:=ZPos_mult) (unit:=ZPos_1).
Global Instance: CommutativeMonoid ZPos (op:=ZPos_plus) (unit:=ZPos_0).
Global Instance: SemiRing ZPos.

(* Misc *)
Global Instance: ∀ x y: ZPos, Decision (x = y) := λ x y, decide (`x = `y).

Definition to_nat (x : { x : Z | 0 ≤ x}) : nat := int_abs Z nat (`x).
Program Definition of_nat (x : nat) : { x : Z | 0 ≤ x} := exist (λ x, 0 ≤ x) (naturals_to_semiring nat Z x) _.
Next Obligation. 
  apply zero_sr_precedes_nat.
Qed.

Instance: Proper ((=) ==> (=)) to_nat.
Proof.
  intros [x Ex] [y Ey] E. unfold to_nat. unfold_equivs. 
  rewrite E. reflexivity.
Qed.

Instance: SemiRing_Morphism to_nat.
Proof with auto.
  repeat (split; try apply _). 

  intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
  apply abs_nonneg_plus...

  apply abs_0.
  
  intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
  apply abs_nonneg_mult...

  apply abs_1.
Qed.

Instance: Proper ((=) ==> (=)) of_nat.
Proof.
  intros x y E. unfold of_nat. unfold_equivs. 
  rewrite E. reflexivity.
Qed.

Instance: SemiRing_Morphism of_nat.
Proof with reflexivity.
  repeat (split; try apply _); repeat intro; unfold of_nat; unfold_equivs.
  apply preserves_plus...
  apply preserves_0...
  apply preserves_mult...
  apply preserves_1...
Qed.

Lemma of_nat_to_nat x : of_nat (to_nat x) = x.
Proof.
  destruct x as [x Ex]. 
  unfold to_nat, of_nat. unfold_equivs. 
  apply abs_nonneg. assumption.
Qed.

Global Instance: NaturalsToSemiRing ZPos := theory.naturals.retract_is_nat_to_sr to_nat.
Global Instance: Naturals ZPos := theory.naturals.retract_is_nat of_nat to_nat of_nat_to_nat.

End positive_integers_naturals.
