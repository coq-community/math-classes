Require Import
  Relation_Definitions Morphisms Ring
  Structures CatStuff RingOps FieldOps
  SemiRingAlgebra RingAlgebra UniversalAlgebra
  Numbers nat_Naturals AbstractProperties.

Section contents.

  Context `{Integers Int}.

  Add Ring Int: (Ring_ring_theory Int).

  Definition int_le: relation Int := fun x y: Int =>
   exists z: nat, x + naturals_to_semiring nat Int z == y.

  Global Instance: Proper (equiv ==> equiv ==> iff) int_le.
  Proof with assumption.
   intros x x' E y y' E'.
   unfold int_le.
   split; intros [z p]; exists z.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance: Reflexive int_le.
  Proof.
   unfold int_le.
   exists 0. 
   rewrite preserves_0.
   ring.
  Qed.

  Global Instance: Transitive int_le.
  Proof.
   unfold int_le.
   intros x y z [d p] [d' p'].
   exists (d + d').
   rewrite preserves_plus.
   rewrite <- p', <- p.
   ring.
  Qed.

  Global Instance: PreOrder int_le.

  Lemma ding x y: int_le x y -> int_le y x -> x == y.
  Proof.
   intros x x'.
   unfold relation_conjunction.
   unfold predicate_intersection.
   unfold pointwise_extension.
   unfold int_le.
   intros [v p] [w q].
   rewrite <- p in q.
   rewrite <- p.
   clear p x'.
   assert (naturals_to_semiring nat Int v + naturals_to_semiring nat Int w == 0).
    apply (plus_reg_l _ _ x).
    ring_simplify.
    assumption.
   rewrite <- preserves_plus in H1.
   pose proof preserves_0.
   assert (naturals_to_semiring nat Int (v + w) == naturals_to_semiring nat Int 0).
    transitivity 0.
     assumption.
    symmetry.
    assumption.
   pose proof (naturals_to_integers_injective (v + w) 0 H3).
   destruct (naturals_zero_sum v w 0 H4).
   rewrite H5.
   rewrite preserves_0.
   ring.
  Qed. (* ugh.. *)

  Global Instance: PartialOrder int_le.
  Proof with intuition.
   constructor; try apply _.
   intros x x'.
   unfold relation_conjunction.
   unfold predicate_intersection.
   unfold pointwise_extension.
   split; intro M.
    rewrite M...
   apply ding...
  Qed.

  (* hm, the lemmas below look rather field-like *)

  Lemma int_le_0_mult x y: int_le 0 x -> int_le 0 y -> int_le 0 (x * y).
  Proof.
   unfold int_le. intros x y [v p] [w q].
   ring_simplify in p. ring_simplify in q.
   exists (v * w). rewrite preserves_mult, p, q. ring.
  Qed.

  Lemma int_le_plus_compat_l x x' y: int_le x x' -> int_le (x + y) (x' + y).
  Proof.
   unfold int_le. intros x x' y [v p].
   exists v. rewrite <- p. ring.
  Qed.

  Lemma int_le_mult_compat_inv_l x x' y: int_le 1 y -> int_le (x * y) (x' * y) -> int_le x x'.
  Proof.
   intros x x' y [v p] [w q].
   unfold int_le.
  Admitted.

  Lemma int_le_mult_compat_l x x' y: int_le x x' -> int_le 0 y -> int_le (x * y) (x' * y).
  Proof.
   unfold int_le.
   intros x x' y [v p] [w q].
   exists (v * w).
   rewrite preserves_mult.
   rewrite <- p, <- q.
   ring.
  Qed.

  Lemma int_le_0_sqr x: int_le 0 (x * x).
  Proof.
   unfold int_le.
   intros x.
  Admitted. (* need absolute value stuff *)

End contents.
