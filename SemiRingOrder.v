Set Automatic Introduction.

Require Import Relation_Definitions Morphisms Structures AbstractNaturals nat_Naturals RingOps Ring AbstractProperties.

Section sr_order. Context `{SemiRing R}.

  Instance sr_precedes: Order R := fun x y: R =>
    exists z: nat, x + naturals_to_semiring nat R z == y.

  Global Instance sr_precedes_proper: Proper (equiv ==> equiv ==> iff) sr_precedes.
  Proof with assumption.
   intros x x' E y y' E'. unfold sr_precedes.
   split; intros [z p]; exists z.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance: Transitive sr_precedes.
  Proof.
   unfold sr_precedes. intros x y z [d p] [d' p'].
   exists (d & d'). rewrite <- p', <- p. 
   rewrite preserves_sg_op.
   apply associativity.
  Qed.

  Global Instance: Reflexive sr_precedes.
  Proof. unfold sr_precedes. exists 0. rewrite preserves_0. apply plus_0_r. Qed.

  Global Instance: PreOrder sr_precedes.

  Definition sr_precedes_with N `{Naturals N} {x y: R}: sr_precedes x y -> exists z: N, x + naturals_to_semiring N R z == y.
   intros [z E].
   exists (naturals_to_semiring nat N z).
   rewrite (naturals_to_semiring_unique R (fun x => naturals_to_semiring N R (naturals_to_semiring nat N x))).
    assumption.
   apply (compose_semiring_morphisms _ _ _ _ _).
  Qed.

  Definition sr_precedes_from N `{Naturals N} {x y: R} (z: N): x + naturals_to_semiring N R z == y -> sr_precedes x y.
   intros.
   exists (naturals_to_semiring N nat z).
   rewrite (naturals_to_semiring_unique R (fun x => naturals_to_semiring nat R (naturals_to_semiring N nat x))).
    assumption.
   apply (compose_semiring_morphisms _ _ _ _ _).
  Qed.

End sr_order.

Instance: Params (@sr_precedes) 6.

Lemma preserves_nonneg `{SemiRing A} `{SemiRing B} `{Naturals N} (f: A -> B) `{!SemiRing_Morphism f}: forall n: N,
 sr_precedes 0 (f (naturals_to_semiring N A n)).
Proof.
 intros.
 pattern n.
 apply Naturals_ordinary_ind.
   intros x y E.
   rewrite E.
   intuition.
  do 2 rewrite preserves_0.
  reflexivity.
 intros m [x E].
 do 2 rewrite preserves_plus.
 rewrite <- E.
 rewrite plus_0_l.
 do 2 rewrite preserves_1.
 exists (1 + x).
 rewrite preserves_plus.
 rewrite preserves_1.
 apply plus_0_l.
Qed. 

Section ring. Context `{Ring R}. (* extra sr_precedes properties that hold in rings: *)

  Add Ring R: (Ring_ring_theory R).

  Lemma precedes_flip (x y: R): sr_precedes x y <-> sr_precedes (-y) (-x).
  Proof.
   split; intros [z p]; exists z.
    rewrite <- p. ring.
   rewrite <- (inv_involutive x), <- p. ring.
  Qed.

  Lemma precedes_0_flip (z: R): sr_precedes 0 z <-> sr_precedes (-z) 0. 
  Proof. 
   pose proof (precedes_flip z 0).
   pose proof (precedes_flip 0 z).
   intuition.
    apply (sr_precedes_proper (-z) (-z) (reflexivity _) 0 (-0)).
     symmetry.
     apply opp_0.
    assumption.
    (* for some reason [rewrite] didn't work above. todo: look into it *)
   apply H4.
   rewrite opp_0.
   assumption.
  Qed.

  Lemma zero_sr_precedes_nat `{Naturals N} (n: N): sr_precedes 0 (naturals_to_semiring N R n).
  Proof.
   exists (naturals_to_semiring N nat n).
   rewrite (naturals_to_semiring_unique R (fun x => naturals_to_semiring nat R (naturals_to_semiring N nat x))).
    ring.
   apply (compose_semiring_morphisms N nat R); apply _.
  Qed.

  Lemma neg_precedes_pos `{Naturals N} (n m: N): sr_precedes (- naturals_to_semiring N R n) (naturals_to_semiring N R m).
  Proof.
   apply (@transitivity R sr_precedes _ _ 0).   
    apply -> precedes_0_flip.
    apply zero_sr_precedes_nat.
   apply zero_sr_precedes_nat.
  Qed.

End ring.

Lemma nats_preserve_sr_order `{SemiRing A} `{Naturals B} (f: A -> B) `{!SemiGroup_Morphism f} (x y: A):
  sr_precedes x y -> sr_precedes (f x) (f y).
Proof. intros [z p]. 
 unfold sr_precedes. 
 exists (naturals_to_semiring B nat (f (naturals_to_semiring nat A z))).
 rewrite <- p.
 rewrite preserves_sg_op.
 rewrite (iso_nats B nat).
 reflexivity.
Qed.
