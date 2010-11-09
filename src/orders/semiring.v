Set Automatic Introduction.

Require
 theory.naturals.
Require Import
 Relation_Definitions Morphisms Ring Program
 abstract_algebra interfaces.naturals theory.rings workaround_tactics.

Section sr_order. 
  Context `{SemiRing R}.
  Add Ring SR: (stdlib_semiring_theory R).

  Global Instance sr_precedes_proper: Proper ((=) ==> (=) ==> iff) sr_precedes.
  Proof with assumption.
   intros x x' E y y' E'. 
   split; intros [z p]; exists z.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance: Transitive sr_precedes.
  Proof.
   intros x y z [d p] [d' p'].
   exists (d + d'). rewrite <- p', <- p. 
   rewrite preserves_sg_op.
   apply associativity.
  Qed.

  Global Instance: Reflexive sr_precedes.
  Proof.
   exists (0:nat). rewrite preserves_0.
   ring.
  Qed.

  Global Instance: PreOrder sr_precedes.

  Lemma sr_precedes_nonneg_plus_compat (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
  Proof.
    intros [x' Ex] [y' Ey].
    rewrite <-Ex, <-Ey.
    exists (x' + y').
    rewrite preserves_plus.
    ring.
  Qed.

  Lemma sr_precedes_nonneg_mult_compat (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
  Proof.
    intros [x' Ex] [y' Ey].
    rewrite <-Ex, <-Ey.
    exists (x' * y').
    rewrite preserves_mult.
    ring.
  Qed.

  Lemma sr_precedes_0_1: (0:R) ≤ (1:R).
  Proof.
    exists (1:nat).
    rewrite preserves_1. ring. 
  Qed.
End sr_order.

Section with_naturals.
  Context `{SemiRing R}.
  Add Ring SR2: (stdlib_semiring_theory R).

  Lemma sr_precedes_with N `{Naturals N} {x y: R}: x ≤ y → ∃ z: N, x + naturals_to_semiring N R z = y.
  Proof.
   intros [z E].
   exists (naturals_to_semiring nat N z).
   posed_rewrite (theory.naturals.to_semiring_unique R (naturals_to_semiring N R ∘ naturals_to_semiring nat N) z).
   assumption.
  Qed.

  Lemma sr_precedes_from N `{Naturals N} {x y: R} (z: N): x + naturals_to_semiring N R z = y → x ≤ y.
  Proof.
   intros.
   exists (naturals_to_semiring N nat z).
   posed_rewrite (theory.naturals.to_semiring_unique R (naturals_to_semiring nat R ∘ naturals_to_semiring N nat) z).
   assumption.
  Qed.

  Lemma preserves_nonneg `{SemiRing B} `{Naturals N} (f: R → B) `{!SemiRing_Morphism f}: 
   ∀ n: N, 0 ≤ f (naturals_to_semiring N R n).
  Proof.
   intros n. pattern n.
   apply theory.naturals.induction.
     intros x y E. rewrite <-E. intuition.
   do 2 rewrite preserves_0. reflexivity.
   intros m [x E].
   do 2 rewrite preserves_plus.
   rewrite <- E.
   rewrite plus_0_l.
   do 2 rewrite preserves_1.
   exists (1 + x).
   rewrite preserves_plus, preserves_1.
   apply plus_0_l.
  Qed. 

  Lemma nats_preserve_sr_order `{SemiRing A} `{Naturals B} (f: A → B) `{!SemiGroup_Morphism f} (x y: A):
    x ≤ y → f x ≤ f y.
  Proof.
   intros [z p].
   exists (naturals_to_semiring B nat (f (naturals_to_semiring nat A z))).
   rewrite <- p, preserves_sg_op.
   rewrite (theory.naturals.to_semiring_involutive B nat).
   reflexivity.
  Qed.

  Lemma zero_sr_precedes_nat `{Naturals N} (n: N): 
    0 ≤ naturals_to_semiring N R n.
  Proof.
   exists (naturals_to_semiring N nat n).
   posed_rewrite (theory.naturals.to_semiring_unique R (naturals_to_semiring nat R ∘ naturals_to_semiring N nat) n).
   ring.
  Qed.
End with_naturals.

Section ring. 
  Context `{Ring R}. (* extra sr_precedes properties that hold in rings: *)
  Add Ring R: (stdlib_ring_theory R).

  Lemma precedes_flip (x y: R): x ≤ y ↔ -y ≤ -x.
  Proof.
   split; intros [z p]; exists z.
    rewrite <- p. ring.
   rewrite <- (inv_involutive x), <- p. ring.
  Qed.

  Lemma precedes_0_flip (z: R): 0 ≤ z ↔ -z ≤ 0. 
  Proof with auto.
   pose proof (precedes_flip z 0).
   pose proof (precedes_flip 0 z).
   intuition. rewrite <- opp_0...
   apply H4. rewrite opp_0...
  Qed.

  Lemma neg_precedes_pos `{Naturals N} (n m: N): 
    - naturals_to_semiring N R n ≤ naturals_to_semiring N R m.
  Proof. transitivity (0:R); [apply -> precedes_0_flip |]; apply zero_sr_precedes_nat. Qed.

End ring.
