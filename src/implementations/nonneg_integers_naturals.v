Require 
  peano_naturals orders.integers theory.integers.
Require Import
  Morphisms Ring Program RelationClasses Setoid
  abstract_algebra interfaces.integers interfaces.naturals interfaces.additional_operations int_abs.
Require Export
  implementations.nonneg_semiring_elements.

Section nonneg_integers_naturals.
Context Z `{Integers Z} `{!RingOrder o} `{!TotalOrder o}.

Add Ring Z: (rings.stdlib_ring_theory Z).

(* We show that [Z⁺] is an instance of the naturals by constructing a retract to [nat] *)
Program Definition of_nat (x : nat) : Z⁺ := exist (λ x, 0 ≤ x) (naturals_to_semiring nat Z x) _.
Next Obligation. apply naturals.to_semiring_nonneg. Qed.

Local Ltac unfold_equivs := unfold equiv, NonNeg_equiv, inject, NonNeg_inject in *; simpl in *.

Instance: Proper ((=) ==> (=)) of_nat.
Proof.
  intros x y E. unfold_equivs. 
  rewrite E. reflexivity.
Qed.

Instance: SemiRing_Morphism of_nat.
Proof with reflexivity.
  pose proof (_ : SemiRing (Z⁺)).
  repeat (split; try apply _); repeat intro; unfold_equivs.
     apply rings.preserves_plus...
    apply rings.preserves_0...
   apply rings.preserves_mult...
  apply rings.preserves_1...
Qed.

Program Instance to_nat: Inverse of_nat := λ x, int_abs Z nat (`x).

Instance: Proper ((=) ==> (=)) to_nat.
Proof.
  intros [x Ex] [y Ey] E. unfold to_nat. unfold_equivs. 
  rewrite E. reflexivity.
Qed.

Instance ZPos_to_nat_sr_morphism: SemiRing_Morphism to_nat.
Proof with auto.
  pose proof (_ : SemiRing (Z⁺)).
  repeat (split; try apply _). 
     intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
     apply int_abs_nonneg_plus...
    apply int_abs_0.
   intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
   apply int_abs_nonneg_mult...
  apply int_abs_1.
Qed.

Instance: Surjective of_nat.
Proof.
  split. 2: apply _.
  intros [x Ex] y E. rewrite <- E.
  unfold to_nat, of_nat. unfold_equivs.
  apply int_abs_nonneg. assumption.
Qed.

Global Instance: NaturalsToSemiRing (Z⁺) := naturals.retract_is_nat_to_sr of_nat.
Global Instance: Naturals (Z⁺) := naturals.retract_is_nat of_nat.

Global Program Instance ZPos_cut_minus: CutMinus (Z⁺) := λ x y, if decide ('x ≤ 'y) then 0 else exist (λ z, 0 ≤ z) ('x - 'y) _.
Next Obligation.
  apply <-rings.flip_nonneg_minus. 
  now apply orders.precedes_flip.
Qed.

Global Instance: CutMinusSpec (Z⁺) ZPos_cut_minus.
Proof.
  split; intros [x Ex] [y Ey] E1; unfold cut_minus, ZPos_cut_minus; unfold_equivs.
   case (decide (x ≤ y)); intros E2.
    rewrite left_identity.
    now apply (antisymmetry o).
   simpl. ring.
  case (decide (x ≤ y)); intros E2.
   reflexivity.
  simpl.
  apply (antisymmetry o).
   now apply rings.flip_nonpos_minus.
  now apply rings.flip_nonneg_minus, orders.precedes_flip.
Qed.
End nonneg_integers_naturals.
