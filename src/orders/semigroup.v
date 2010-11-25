Require Import Relation_Definitions Morphisms abstract_algebra.

Section sg_order. 
  Context `{SemiGroup G}.

  Global Instance sg_precedes: Order G | 10 := λ x y: G, exists z: G, x & z = y.

  Global Instance: Proper (equiv ==> equiv ==> iff) sg_precedes.
  Proof with assumption.
   intros x x' E y y' E'.
   split; intros [z p]; exists z.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance: Transitive sg_precedes.
  Proof.
   unfold sg_precedes. intros x y z [d p] [d' p'].
   exists (d & d'). rewrite <- p', <- p. apply associativity.
  Qed.

End sg_order.

Instance: Params (@sg_precedes) 3.

Lemma preserves_sg_order `{SemiGroup A} `{SemiGroup B} (f: A → B) `{!SemiGroup_Morphism f} (x y: A):
  x ≤ y → f x ≤ f y.
Proof. 
  intros [z p]. 
  exists (f z). 
  rewrite <-preserves_sg_op, p. reflexivity. 
Qed.

Section monoid. 
  Context `{Monoid M}. (* On monoids, sg_precedes is a preorder. *)

  Global Instance: Reflexive sg_precedes.
  Proof. unfold sg_precedes. exists mon_unit. apply right_identity. Qed.

  Global Instance: PreOrder sg_precedes.

End monoid.
