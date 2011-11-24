(* "Forgetting" an algebra's operations (but keeping the setoid equality) is a trivial functor.

This functor should nicely compose with the one forgetting variety laws. *)

Require Import
  Morphisms Coq.Setoids.Setoid abstract_algebra universal_algebra interfaces.functors
  ua_homomorphisms theory.categories.
Require
  categories.setoids categories.product categories.algebras.

Section contents.
  Variable sign: Signature.

  Notation TargetObject := (product.Object (λ _: sorts sign, setoids.Object)).

  Definition object (v: algebras.Object sign): TargetObject := λ i, setoids.object (v i) (algebras.algebra_equiv sign v i).

  Global Program Instance: Fmap object := λ _ _, id.
  Next Obligation. apply _. Qed.

  Global Instance forget: Functor object _.
  Proof.
   constructor; try apply _.
   - constructor; try apply _.
     intros x y E i A B F.
     rewrite F. apply E.
   - now repeat intro.
   - intros ? ? f ? g i ? ? E.
     now rewrite E.
  Qed.

  Global Instance mono: ∀ (X Y: algebras.Object sign) (a: X ⟶ Y),
    Mono (fmap object a) → Mono a.
  Proof with simpl in *; intuition.
   repeat intro.
   assert (fmap object f = fmap object g). {
    apply H.
    repeat intro.
    rewrite H1.
    apply H0.
   }
   now apply H1.
  Qed.

End contents.
