Set Automatic Introduction.

(** We prove the equivalence of the two definitions of adjunction. *)

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra setoids functors categories
  workaround_tactics.

Section unit.

  Context
    `(φ_adj: Adjunction A e X (F:=F) (G:=G) (φ:=φ))
    `{Π x a, Inverse (φ x a)}
    `{Π x a, Bijective (φ x a)}.

  Implicit Arguments φ [[a] [x]].

  (* Move to Utils *)
  Hint Unfold id compose:typeclass_instances.

  (* Waiting for the new proof engine ... *)
  Let hint'''' x y: Injective (@φ x y) := _.
  Let hint''''' x y: Setoid_Morphism (@φ x y) := injective_mor (@φ x y).
  Let hint := adjunction_left_functor F G (@φ).
  Let hint' := adjunction_right_functor F G (@φ).
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.

  Definition η: id ⇛ G ∘ F := λ x: X => @φ x (F x) cat_id.

 Instance eta: NaturalTransformation η.
 Proof with try reflexivity; try apply _. (* todo: latter should not be necessary *)
   (* MacLane p81 *)
  intros x' x h.
  transitivity (φ (fmap F h ◎ cat_id)).
   symmetry. transitivity (φ (cat_id ◎ fmap F h)).
    transitivity (φ (fmap F h)); [rewrite id_r|rewrite id_l]...
   transitivity (φ cat_id ◎ fmap id h)... 
   apply (rad_r F G)...   (* the naturality of φ.*)
  rewrite rad_l...                           (*the naturality of φ.*)
 Qed.

  (**
  It is a natural transformation because:
  GF h ∘ (φ (cat_id (F x')))
     = (φ (fmap F h∘ cat_id (F x')))
     = φ ( cat_id (F x) ∘ (fmap F h))
     = φ ( cat_id (F x) ∘ h

  Based on the naturality of φ.
  *)

  (** Characterization of φ in terms of G and η *)
  Lemma φarrows `(f: F x ⟶ a): φ f = fmap G f ◎ η x.
  Proof with reflexivity.
   rewrite <- (id_r  f).
   (* TODO: Finish the proof by autorewrite *)
   rewrite  rad_l by apply _.
   rewrite id_r...
  Qed.

End unit.

Require categories.dual jections.

Section counit.

  Context
    `(φ_adj: Adjunction A e X (F:=F) (G:=G) (φ:=φ))
    `{Π x a, Inverse (φ x a)}
    `{Π x a, Bijective (φ x a)}.

  Let hint := adjunction_left_functor F G (@φ).
  Let hint' := adjunction_right_functor F G (@φ).
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.

  Notation "f ⁻¹" := (inverse f) (at level 30).

  Definition φinv x a := (@φ x a)⁻¹.

  (** And an adjunction *)

  Definition inverse0: ∀x a, Inverse (φinv a x) := λ a x => φ x a. 

  Lemma inverse: Π (x: A) (a : X), @Bijective _ (dual.e _ _) _ (dual.e _ _) (φinv a x) (inverse0 x a).
  Proof. intros a x. unfold φinv. apply _. Qed.

  Instance: @Adjunction X _ _ _ _ A _ _ _ _ G (dual.fmap_op G) F (dual.fmap_op F) (λ a x => (@φ x a)⁻¹ ). (* flip *)
  Proof with intuition; try reflexivity.
   destruct φ_adj. 
   constructor; try apply _.
    (* first law *)
    intros x x' k a h.
    apply jections.cancel_left...
    transitivity (φ x a ((φ x a ⁻¹) h) ◎ k).
     symmetry; apply natural_right.
    posed_rewrite (surjective (φ x a) h)...
    (* second law *)
   intros a a' h x k.
   apply jections.cancel_left...
   change (a' ⟶ a) in h.
   change (φ x a (h ◎ ((φ x a' ⁻¹) k)) = Fmap1 a' a h ◎ k).
   transitivity (fmap G h ◎ φ x a' ((φ x a' ⁻¹) k)).
    symmetry; apply natural_left.
   apply comp_proper...
   apply surjective...
  Qed.

  Definition ϵnat: @NaturalTransformation _ _ _ _ _ _ _ _ (F ∘ G)
    (@comp_Fmap _ _ A _ _ _ F (dual.fmap_op F) G (dual.fmap_op G))
    (@η X (@dual.flipA X Arrows1) _ A (@dual.flipA A Arrows0) G F (λ (a : A) (x : X) => φinv x a)).
  Proof.
   apply (@eta X _ _ _ _ A _ _ _ _ G (dual.fmap_op G) F (dual.fmap_op F) (λ a x => (@φ x a)⁻¹ )) with
     (λ a x => @φ x a); intros; apply _.
  Qed.

End counit.
