Require Import 
  Morphisms Setoid Program 
  abstract_algebra orders.orders.

Instance order_iso_injective `{OrderIsomorphism A B f} `{!PartialOrder (precedes (A:=A))} `{!PartialOrder (precedes (A:=B))} : 
  Injective f.
Proof.
  split; try apply _.
  pose proof (poset_setoid : Setoid B).
  intros x y E.
  apply (antisymmetry (≤)); apply (order_preserving_back f); apply equiv_precedes.
   assumption.
  symmetry. assumption.
Qed.

(* Some helper lemmas *)
Section order_preserving_ops.
  Context `{Equiv R} `{Order R}.

  Lemma order_preserving_flip `{!Commutative op} `{!OrderPreserving (op z)} : OrderPreserving (flip op z).
  Proof with eauto.
    repeat (split; try apply _).
    intros x y E. unfold flip.
    eapply order_preserving_proper_a...
    apply order_preserving...
  Qed.

  Lemma order_preserving_back_flip `{!Commutative op} `{!OrderPreservingBack (op z) } : OrderPreservingBack (flip op z).
  Proof with eauto.
    repeat (split; try apply _).
    intros x y E. unfold flip in E.
    apply (order_preserving_back (op z)).
    eapply order_preserving_back_proper_b...
  Qed.

  Lemma order_preserving_ge_0 (op : R → R → R) `{!RingZero R} `{∀ z, GeZero z → OrderPreserving (op z)} z : 
    0 ≤ z → OrderPreserving (op z).
  Proof. auto. Qed.

  Lemma order_preserving_back_gt_0 (op : R → R → R) `{!RingZero R} `{∀ z, GtZero z → OrderPreservingBack (op z)} z : 
    0 < z → OrderPreservingBack (op z).
  Proof. auto. Qed.
End order_preserving_ops.
