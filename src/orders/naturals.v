Require
 theory.naturals.
Require Import
 Relation_Definitions Morphisms Ring Program
 abstract_algebra interfaces.naturals
 orders.semiring orders.semigroup.

Section contents.
Context `{Naturals N}.
Add Ring N: (rings.stdlib_semiring_theory N).

Lemma sg_sr_precedes (x y : N) : sg_precedes x y ↔ sr_precedes x y.
Proof with auto.
  split; intros [z Ez].
  exists (naturals_to_semiring N nat z).
  rewrite naturals.to_semiring_involutive; try apply _...
  exists (naturals_to_semiring nat N z)...
Qed.

Lemma natural_precedes_with {x y: N}: x ≤ y → ∃ z: N, x + z = y.
Proof.
  intros E. eapply sg_sr_precedes in E. assumption.
Qed.

Lemma natural_precedes_from {x y: N} (z: N) : x + z = y → x ≤ y.
Proof.
  intros E. eapply sg_sr_precedes. exists z. assumption.
Qed.

Lemma preserves_naturals_order_back `{Naturals B} (f: N → B) `{!SemiRing_Morphism f} (x y: N): 
  f x ≤ f y → x ≤ y.
Proof.
 intros.
 rewrite <- (naturals.morphisms_involutive (naturals_to_semiring _ _) f y).
 rewrite <- (naturals.morphisms_involutive (naturals_to_semiring _ _) f x).
 apply nats_preserve_sr_order. apply _.
 assumption.
Qed.

Lemma preserves_naturals_order `{Naturals B} (f: N → B) `{!SemiRing_Morphism f} (x y: N): 
  x ≤ y ↔ f x ≤ f y.
Proof.
 split. apply nats_preserve_sr_order. apply _.
 apply preserves_naturals_order_back. apply _.
Qed.

Global Instance: TotalOrder (sr_precedes (R:=N)).
Proof.
  intros x y. 
  destruct (total_order (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y)) as [E|E];
  eapply preserves_naturals_order in E; try apply _; auto.
Qed.

Global Instance: AntiSymmetric (sr_precedes (R:=N)).
Proof.
  intros x y E F. 
  destruct (natural_precedes_with E) as [v A].
  destruct (natural_precedes_with F) as [w B].
  rewrite <- A in *. clear A.
  rewrite <- associativity in B.
  assert (v + w = 0) as C.
  apply (injective (ring_plus x)). rewrite right_identity. assumption.
  destruct (naturals.zero_sum v w C) as [D _]. rewrite D.
  ring.
Qed.

Global Instance: PartialOrder (sr_precedes (R:=N)).

Global Program Instance: ∀ x y: N, Decision (x ≤ y) | 10 := λ x y,
  match decide (naturals_to_semiring _ nat x ≤ naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.

Next Obligation.
  intros.
  apply (preserves_naturals_order (naturals_to_semiring N nat) x y).
  assumption. 
Qed.

Next Obligation.
  intros F. apply E.
  apply (preserves_naturals_order (naturals_to_semiring N nat) x y).
  assumption. 
Qed.

Lemma le_mult_compat_inv_l (x x' y: N): y ≠ 0 → x * y ≤ x' * y → x ≤ x'.
Proof.
  destruct (total_order x x') as [|E]. intuition. 
  destruct (natural_precedes_with E) as [z Ez].
  rewrite <- Ez. 
  intros ne F. 
  destruct (natural_precedes_with F) as [v Ev].
  apply (natural_precedes_from 0).
  apply (naturals.mult_injective y ne).
  destruct (naturals.zero_sum (z * y) v) as [A _].
  apply (injective (ring_plus (x' * y))). 
  rewrite <- Ev at 2. ring.
  ring_simplify. rewrite (commutativity y z), A. ring.
Qed.

End contents.
