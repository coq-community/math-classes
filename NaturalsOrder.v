Require Import Relation_Definitions Morphisms Structures Numbers (*nat_Naturals*) RingOps Ring.
Require Import BoringInstances.
Require MonoidOrder.

Global Instance naturals_partial_order `{Naturals N}: @PartialOrder N equiv MonoidOrder.m_le.
Proof.
 constructor; try apply _.
 split.
  intro.
  split; rewrite H1; reflexivity.
 intros [[y A] [y' A']].
 admit. (* easy *)
Qed.

Global Instance naturals_total_order `{Naturals N}: @TotalOrder N MonoidOrder.m_le.
Admitted.

Lemma nat_ding (x y: nat): le x y -> x <= y.
 intros x y H.
 induction H.
  exists 0.
  apply plus_0_r.
 destruct IHle.
 exists (S x0).
 rewrite <- H0.
 change (x + (1 + x0) == 1 + (x + x0)).
 ring.
Qed.

Lemma nat_ding_rev (x y: nat): x <= y -> le x y.
 intros x y [z H].
 unfold equiv, nat_equiv in H.
 subst.
 auto with arith.
Qed.

Section more_contents.

  Context `{Naturals N} `{Naturals M}.

  Lemma naturals_to_semiring_preserves_order (x y: N): x <= y ->
   naturals_to_semiring N M x <= naturals_to_semiring N M y.
  Proof.
   intros.
   destruct H3.
   rewrite <- H3.
   rewrite preserves_sg_op.
   unfold precedes, MonoidOrder.m_le.
   exists (naturals_to_semiring N M x0).
   reflexivity.
  Qed.

End more_contents.
