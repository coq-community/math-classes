Set Automatic Introduction.

Require Import Relation_Definitions Morphisms Setoid abstract_algebra.

Section contents.

  Context `{Category X A}.

  Definition iso_arrows {x y: X} (a: A x y) (b: A y x): Prop := comp a b == cat_id /\ comp b a == cat_id.

  Definition is_iso {x y: X} (a: A x y): Prop := ex (iso_arrows a).

  Let bah := @Ae_equiv X A _ _ _ _ _.
  Let meh := @comp_proper X A _ _ _ _ _.

  Definition isos_unique (x y: X) (a: A x y) (b b': A y x): iso_arrows a b -> iso_arrows a b' -> b == b'.
  Proof. intros [P Q] [R S]. rewrite <- id_l. rewrite <- S, <- comp_assoc, P. apply id_r. Qed.

  Definition iso: relation X := fun x y => ex (@is_iso x y).

  Definition proves_initial {x: X} (f: forall y: X, A x y): Prop :=
    forall (y: X) f', f y == f'.

  Definition initial (x: X): Type := forall y: X, sig (fun a: A x y => forall a': A x y, a == a').

  Definition initials_unique (x x': X) (a: initial x) (b: initial x'): iso_arrows (proj1_sig (a x')) (proj1_sig (b x)).
  Proof with auto.
   unfold initial.
   intros.
   destruct (a x). destruct (b x').
   destruct a. destruct b. simpl.
   split.
    rewrite <- e0. apply e0.
   rewrite <- e. apply e.
  Qed.

  Definition initials_unique' (x x': X) (a: forall y, A x y) (b: forall y, A x' y):
    proves_initial a -> proves_initial b ->
    iso_arrows (a x') (b x).
  Proof with reflexivity.
   intros H1 H2.
   split.
    rewrite <- (H2 x' cat_id).
    rewrite <- H2...
   rewrite <- (H1 x cat_id).
   rewrite <- H1...
  Qed.

End contents.
