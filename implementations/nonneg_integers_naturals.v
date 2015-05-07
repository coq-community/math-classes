Require 
  MathClasses.implementations.peano_naturals.
Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.integers MathClasses.interfaces.naturals MathClasses.interfaces.orders
  MathClasses.interfaces.additional_operations MathClasses.theory.int_abs.
Require Export
  MathClasses.implementations.nonneg_semiring_elements.

Section nonneg_integers_naturals.
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z} `{!FullPseudoSemiRingOrder Zle Zlt}.

Add Ring Z: (rings.stdlib_ring_theory Z).

(* We show that [Z⁺] is an instance of the naturals by constructing a retract to [nat] *)
Program Let of_nat (x : nat) : Z⁺ := (naturals_to_semiring nat Z x)↾_.
Next Obligation. apply nat_int.to_semiring_nonneg. Qed.

Local Ltac unfold_equivs := unfold equiv, sig_equiv in *; simpl in *.

Instance: Proper ((=) ==> (=)) of_nat.
Proof. intros ?? E. unfold_equivs. now rewrite E. Qed.

Instance: Setoid_Morphism of_nat := {}.

Instance: SemiRing_Morphism of_nat.
Proof.
  repeat (split; try apply _); repeat intro; unfold_equivs.
     now apply rings.preserves_plus.
    unfold mon_unit, zero_is_mon_unit. now apply rings.preserves_0.
   now apply rings.preserves_mult.
  unfold mon_unit, one_is_mon_unit. now apply rings.preserves_1.
Qed.

Program Let to_nat: Inverse of_nat := λ x, int_abs Z nat (`x).
Existing Instance to_nat.

Instance: Proper ((=) ==> (=)) to_nat.
Proof.
  intros [x Ex] [y Ey] E. unfold to_nat. do 2 red in E. simpl in E. simpl.
  now rewrite E.
Qed.

Instance: SemiRing_Morphism to_nat.
Proof.
  pose proof (_ : SemiRing (Z⁺)).
  repeat (split; try apply _).
     intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
     now apply int_abs_nonneg_plus.
    unfold mon_unit, zero_is_mon_unit. now apply int_abs_0.
   intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
   now apply int_abs_mult.
  unfold mon_unit, one_is_mon_unit. apply int_abs_1.
Qed.

Instance: Surjective of_nat.
Proof.
  split. 2: apply _.
  intros [x Ex] y E. rewrite <- E.
  unfold to_nat, of_nat. unfold_equivs.
  now apply int_abs_nonneg.
Qed.

Global Instance: NaturalsToSemiRing (Z⁺) := naturals.retract_is_nat_to_sr of_nat.
Global Instance: Naturals (Z⁺) := naturals.retract_is_nat of_nat.

Context `{∀ x y : Z, Decision (x ≤ y)}.

Global Program Instance ZPos_cut_minus: CutMinus (Z⁺) := λ x y, 
  if decide_rel (≤) x y then 0 else ((x : Z) - (y : Z))↾_.
Next Obligation.
  apply <-rings.flip_nonneg_minus.
  now apply orders.le_flip.
Qed.

Global Instance: CutMinusSpec (Z⁺) ZPos_cut_minus.
Proof.
  split; intros [x Ex] [y Ey] E1; unfold cut_minus, ZPos_cut_minus; unfold_equivs.
   case (decide_rel (≤)); intros E2.
    rewrite left_identity.
    now apply (antisymmetry (≤)).
   simpl. ring.
  case (decide_rel (≤)); intros E2.
   reflexivity.
  simpl.
  apply (antisymmetry (≤)).
   now apply rings.flip_nonpos_minus.
  now apply rings.flip_nonneg_minus, orders.le_flip.
Qed.
End nonneg_integers_naturals.
