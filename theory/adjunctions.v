Set Automatic Introduction.

(** We prove the equivalence of the two definitions of adjunction. *)

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra setoids functors categories.

Section unit.

  Context
    `(φ_adj: Adjunction A e X (F:=F) (G:=G) (φ:=φ))
    `{Π x a, Inv (φ x a)}
    `{Π x a, Bijective (φ x a)}.

  Implicit Arguments φ [[a] [x]].

  (* Move to Utils *)
  Hint Unfold id compose:typeclass_instances.

  Instance: Setoid_Morphism (@φ x y).
  Proof. intros. destruct (H0 x y). apply _. Qed.

  Let hint := adjunction_left_functor F G (@φ).
  Let hint' := adjunction_right_functor F G (@φ).
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.

  Definition η: id ⇛ G ∘ F := λ x: X => @φ x (F x) cat_id.

  Instance eta: NaturalTransformation η.
  Proof.
   (* MacLane p81 *)
   unfold η. intros x' x h.
   symmetry.
   setoid_replace (fmap (G ∘ F) h ◎ φ cat_id) with (φ (fmap F h ◎ cat_id)).
    Focus 2. symmetry; rewrite rad_l; [| apply _].
   cut ( fmap (G ∘ F) h = fmap G (fmap F h)). (intro H5; rewrite H5; reflexivity).
   (* apply preserves_comp. TODO: Prove for normal arrow in Sets *) admit.
   setoid_replace (φ (fmap F h ◎ cat_id)) with (φ ( cat_id ◎ (fmap F h))) by
    (transitivity (φ (fmap F h)); [rewrite id_r|rewrite id_l];reflexivity).
    (* TODO: add Hint that bijective is a Setoid_Morphism. *)
   setoid_replace (φ (cat_id ◎ fmap F h)) with (φ cat_id ◎ fmap id h) by (apply (rad_r F G); apply _).
   reflexivity. 
  Qed.

  (**
  It is a natural transformation because:
  GF h ∘ (φ (cat_id (F x')))=(φ (fmap F h∘ cat_id (F x')))
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

Require categories.dual bijective.

Section counit.

  Context
    `(φ_adj: Adjunction A e X (F:=F) (G:=G) (φ:=φ))
    `{Π x a, Inv (φ x a)}
    `{Π x a, Bijective (φ x a)}.

  Let hint := adjunction_left_functor F G (@φ).
  Let hint' := adjunction_right_functor F G (@φ).
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.

  Notation "f ⁻¹" := (@inv _ _ f _) (at level 30).

  Definition φinv x a := (@φ x a)⁻¹.

  (** And an adjunction *)

  Definition inverse0: ∀x a, Inv (φinv a x) := λ a x => φ x a. 

  Lemma inverse: Π (x: A) (a : X), @Bijective _ (dual.e _ _) _ (dual.e _ _) (φinv a x) (inverse0 x a).
  Proof.
   intros a x. unfold φinv, dual.e, inverse0.
   apply bijective.invBij.
   apply _.
  Qed.

  Instance: @Adjunction X _ _ _ _ A _ _ _ _ G (dual.fmap_op G) F (dual.fmap_op F) (λ a x => (@φ x a)⁻¹ ). (* flip *)
  Proof with intuition; try reflexivity.
   destruct φ_adj. 
   constructor. 
      apply _.
     apply _.
    intros x x' k a h.
    unfold compose.
    apply bijective.cancel_left...
    transitivity (φ x a ((φ x a ⁻¹) h) ◎ k).
     symmetry. apply natural_right.
    pose proof (bijective.back' (H0 x a) h) as E.
    unfold compose, id in E.
    rewrite E...
   intros a a' h x k.
   unfold compose.
   apply bijective.cancel_left...
   change (a' ⟶ a) in h.
   change (φ x a (h ◎ ((φ x a' ⁻¹) k)) = Fmap1 a' a h ◎ k).
   transitivity (fmap G h ◎ φ x a' ((φ x a' ⁻¹) k)).
    symmetry. apply natural_left.
   apply comp_proper...
   apply bijective.back'...
  Qed.

  Definition ϵnat: @NaturalTransformation _ _ _ _ _ _ _ _ (F ∘ G)
    (@comp_Fmap _ _ A _ _ _ F (dual.fmap_op F) G (dual.fmap_op G))
    (@η X (@dual.flipA X Arrows1) _ A (@dual.flipA A Arrows0) G F (λ (a : A) (x : X) => φinv x a)).
  Proof.
   apply (@eta _ _ _ _ _ _ _ _ _ _ G (dual.fmap_op G) F (dual.fmap_op F) _ _ _ inverse); apply _.
  Qed.

End counit.
