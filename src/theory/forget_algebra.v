(* "Forgetting" an algebra's operations (but keeping the setoid equality) is a trivial functor.

This functor should nicely compose with the one forgetting variety laws. *)
Require Import
  abstract_algebra universal_algebra interfaces.functors
  ua_homomorphisms theory.categories
  categories.setoids categories.product categories.algebras.

Section contents.
  Variable sign: Signature.

  Notation TargetObject := (product.Object (λ _: sorts sign, setoids.Object)).

  Let TargetArrows: Arrows TargetObject := @product.pa _ (λ _: sorts sign, setoids.Object) (λ _, _: Arrows setoids.Object).
    (* hm, not happy about this *)

  Definition object (v: algebras.Object sign): TargetObject := λ i, @setoids.object (v i) (algebras.algebra_equiv sign v i) _.

  Global Program Instance: Fmap object := λ _ _, id.

  Global Instance forget: Functor object _.
  Proof.
   constructor; try apply _.
     constructor; try apply _.
     intros x y E i A B F. rewrite F. now apply E.
    now repeat intro.
   intros ? ? f ? g i ? ? E. now rewrite E.
  Qed.

  Let hint: ∀ x y, Equiv (object x ⟶ object y). intros. apply _. Defined. (* todo: shouldn't be necessary *)

  Global Instance mono: ∀ (X Y: algebras.Object sign) (a: X ⟶ Y),
    Mono (fmap object a) → Mono a.
  Proof.
   intros ??? H1 ??? H2 ??.
   assert (fmap object f = fmap object g).
    apply H1. intros ??? H3. rewrite H3. now apply H2.
   now apply H.
  Qed.
End contents.
