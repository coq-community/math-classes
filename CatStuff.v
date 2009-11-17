Require Import Relation_Definitions Morphisms Setoid CanonicalNames.

Section contents.

  Class Category O (A: O -> O -> Type) {Oe: Equiv O} {Ae: forall x y, Equiv (A x y)} `{CatId O A} `{cc: CatComp O A}: Type :=
    { Oe_equiv:> Equivalence Oe
       (* hm, not strictly needed here. does make the quotient construction rather easy. but shouldn't we now have a morphism for A? *)
    ; Ae_equiv:> forall x y, Equivalence (Ae x y)
    ; comp_proper: forall x y z, Proper (equiv ==> equiv ==> equiv)%signature (@cc x y z)
    ; comp_assoc: forall w x y z (a: A w x) (b: A x y) (c: A y z),
        equiv (comp c (comp b a)) (comp (comp c b) a)
    ; id_l: forall x y (a: A y x), equiv (comp cat_id a) a
    ; id_r: forall x y (a: A x y), equiv (comp a cat_id) a
    }.

  Context `{Category X A}.

  Definition iso_arrows {x y: X} (a: A x y) (b: A y x): Prop := comp a b == cat_id /\ comp b a == cat_id.

  Definition is_iso {x y: X} (a: A x y): Prop := ex (iso_arrows a).

  Let bah := @Ae_equiv X A _ _ _ _ _.
  Let meh := @comp_proper X A _ _ _ _ _.

  Definition isos_unique (x y: X) (a: A x y) (b b': A y x): iso_arrows a b -> iso_arrows a b' -> b == b'.
  Proof.
   intros.
   unfold iso_arrows in *.
   intuition.
   rewrite <- id_l.
   rewrite <- H5.
   rewrite <- comp_assoc.
   rewrite H3.
   apply id_r.
  Qed.

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
   unfold iso_arrows.
   split.
    rewrite <- e0. apply e0.
   rewrite <- e. apply e.
  Qed.

  Definition initials_unique' (x x': X) (a: forall y, A x y) (b: forall y, A x' y):
    proves_initial a -> proves_initial b ->
    iso_arrows (a x') (b x).
  Proof.
   intros.
   unfold proves_initial in *.
   split.
    rewrite <- (H2 x' cat_id).
    rewrite <- H2.
    reflexivity.
   rewrite <- (H1 x cat_id).
   rewrite <- H1.
   reflexivity.
  Qed.

End contents.
