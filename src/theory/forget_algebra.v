(* "Forgetting" an algebra's operations (but keeping the setoid equality) is a trivial functor.

This functor should nicely compose with the one forgetting variety laws. *)

Require Import
  Morphisms Coq.Setoids.Setoid abstract_algebra universal_algebra interfaces.functors
  ua_homomorphisms theory.categories
  categories.setoids categories.product categories.algebras.

Section contents.
  Variable sign: Signature.

  Notation TargetObject := (product.Object (λ _: sorts sign, setoids.Object)).

  Let TargetArrows: Arrows TargetObject := @product.pa _ (λ _: sorts sign, setoids.Object) (λ _, _: Arrows setoids.Object).
    (* hm, not happy about this *)

  Definition object (v: algebras.Object sign): TargetObject := λ i, setoids.object (v i) (algebras.algebra_equiv sign v i) _.

  Global Program Instance: Fmap object := λ _ _, id.
  Next Obligation. destruct x. simpl. apply _. Qed.

  Global Instance forget: Functor object _.
  Proof with intuition.
   constructor; try apply _.
     constructor; try apply _.
     intros x y E i A B F. simpl in *.
     unfold id.
     destruct (@homo_proper _ _ _ _ _ _ _ (proj1_sig x) (proj2_sig x) i).
     (* todo: shouldn't be necessary. perhaps an [Existing Instance] for
       a specialization of proj2_sig is called for. *)
     rewrite F. apply E.
    repeat intro...
   intros ? ? f ? g i ? ? E.
   simpl in *. unfold Basics.compose.
   destruct (@homo_proper _ _ _ _ _ _ _ (proj1_sig f) (proj2_sig f) i). (* todo: clean up *)
   destruct (@homo_proper _ _ _ _ _ _ _ (proj1_sig g) (proj2_sig g) i).
   rewrite E...
  Qed.

  Let hintje: ∀ x y, Equiv (object x ⟶ object y). intros. apply _. Defined. (* todo: shouldn't be necessary *)

  Global Instance mono: ∀ (X Y: algebras.Object sign) (a: X ⟶ Y),
    Mono (@fmap _ _ _ TargetArrows object _ _ _ a) → (* todo: too ugly *)
    Mono a.
  Proof with simpl in *; intuition.
   repeat intro.
   destruct a as [? [? ?]].
   assert (fmap object f = fmap object g).
    apply H.
    repeat intro...
    destruct f as [? [? ?]].
    simpl in *.
    pose proof (H0 i).
    rewrite H1...
   apply H1...
  Qed.

End contents.
