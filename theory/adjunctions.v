Set Automatic Introduction.

(** We prove the equivalence of the two definitions of adjunction *)
Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra setoids functors categories.
Section unit.

Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F Fa} (* todo: we don't want to name Fa and Fg here *)
    (G: A → X) `{!Functor G Ga}
    (φ: Π {x a}, (F x ⟶ a) → (x ⟶ G a))
    `{Π x a, Inv (φ x a)}
    `{Π x a, Bijective (φ x a)}
    (φ_adj:Adjunction _ _ φ).

Implicit Arguments φ [[a] [x]].

(* Move to Utils *)
Hint Unfold id compose:typeclass_instances.

Definition η:id ⇛ G ∘ F:=
  (λ x:X => (@φ x (F x) (@cat_id A _ _ (F x)))).

Instance: ∀ x y, Setoid_Morphism (@φ x y).
 intros.
 destruct (H4 x y).
 destruct bijective_injective.
 apply _.
Qed.

Instance eta: NaturalTransformation η.
 unfold NaturalTransformation. 
 (* MacLane p81 *)
 unfold η. intros x' x h.
 symmetry.
 setoid_replace (fmap (G ∘ F) h ◎ φ cat_id) with (φ (fmap F h ◎ cat_id)).
  2: symmetry; rewrite rad_l; [| apply _].
  Focus 2. cut (fmap G (fmap F h)=  fmap (G ∘ F) h).
   (intro H5; rewrite H5; reflexivity).
  symmetry.
   (* apply preserves_comp. TODO: Prove for normal arrow in Sets *) admit.
  setoid_replace (φ (fmap F h ◎ cat_id)) with (φ ( cat_id ◎ (fmap F h))) by
(transitivity (φ (fmap F h)); [rewrite id_r;reflexivity|rewrite id_l; reflexivity]).
(* TODO: add Hint that bijective is a Setoid_Morphism. *)
setoid_replace (φ (cat_id ◎ fmap F h)) with (φ cat_id ◎ fmap id h) by apply (rad_r F G).
reflexivity. apply _.
Qed.

(**
It is a natural transformation because:
GF h ∘ (φ (cat_id (F x')))=(φ (fmap F h∘ cat_id (F x')))
   = φ ( cat_id (F x) ∘ (fmap F h))
   = φ ( cat_id (F x) ∘ h

Based on the naturality of φ.
*)

(** Characterization of φ in terms of G and η *)
Lemma φarrows `(f:(F x)  ⟶ a):φ f = (fmap G f)  ◎ (η x).
Proof with reflexivity.
rewrite <- (id_r  f).
(* TODO: Finish the proof by autorewrite *)
rewrite  rad_l by apply _.
rewrite id_r...
Qed.
End unit.

Require Import dual.

Section opfunctor.
(** Given a functor F:C->D, we have a functor F^op:C^op -> D^op *)
Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F Fa}.
Definition functor_op (func:Fmap F)  :(@Fmap _ flipA _ flipA F):=
fun v w f => func w v f.
Implicit Arguments functor_op [[func]].

Instance :Functor F functor_op.
unfold e, functor_op, flipA, flip, CatId_instance_0, CatComp_instance_0, flip. constructor. intuition.
      destruct (functor_morphism F b a); constructor; intuition.
   intro a. set (preserves_id F a);intuition.
  intros. unfold fmap. apply (@preserves_comp _ _ H1 _ _ _ _ H _ _ F);assumption.
Qed.
End opfunctor.

Section counit.
Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F Fa} (* todo: we don't want to name Fa and Fg here *)
    (G: A → X) `{!Functor G Ga}
    (φ: Π {x a}, (F x ⟶ a) → (x ⟶ G a))
    `{Π x a, Inv (φ x a)}
    `{Π x a, Bijective (φ x a)}
    (φ_adj:Adjunction _ _ φ).
Notation "f ⁻¹" := (@inv _ _ f _) (at level 30).
Definition φinv:=λ x a => (@φ x a)⁻¹.

(** And an adjunction *)

Require Import bijective.
Definition inverse0: ∀x : A, ∀a : X, Inv ((fun (a0 : A) (x0 : X) => φinv x0 a0) x a):=
fun (a : A) (x : X) => φ x a. 

Lemma inverse: (∀x : A,
        ∀a : X,
        @Bijective (G x ⟶ a) (@e X Arrows1 H1 (G x) a) (x ⟶ F a)
          (@e A Arrows0 H x (F a))
          ((fun (a0 : A) (x0 : X) => φinv x0 a0) x a) (inverse0 x a)).
intros a x. unfold φinv, e, inverse0. apply (@invBij _ _ _ _ _ _ (φ x a)); auto.
Qed.

Instance op_adj:(@Adjunction _ _ _ _ _  _ _  _ (functor_op G _)  _ ( functor_op F _) 
  (λ a x => (@φ x a)⁻¹ )). (* flip *)
  destruct φ_adj. 
  constructor. 
    intros x x' k a h. set (g:=((φ x a ⁻¹) h)).
   assert ((φ x' a) (CatComp0 (F x') (F x) a g (Fa x' x k)) = (CatComp1 x' x (G a) ((φ x a) g) k)) by
      (symmetry; apply natural_right).
    unfold comp, compose, φinv, CatComp_instance_0, flip, flipA, flip, functor_op, fmap, e. 
    revert H5. set (t1:=(CatComp0 (F x') (F x) a g (Fa x' x k))).
    subst g. rewrite (back' (H4 x a) h). (* hangs on: intro r.  rewrite <- r *)
    apply cancel_left. 
  clear natural_right. intros a a' h x k. set (l:=((φ x a' ⁻¹) k)).
  assert ((φ x a) (CatComp0 (F x) a' a h l) = (CatComp1 x (G a') (G a) (Ga a' a h) (φ x a' l))) by
      (symmetry; apply natural_left).
  unfold comp, compose, φinv, CatComp_instance_0, flip, flipA, flip, functor_op, fmap, e. 
  revert H5. set (t1:=(CatComp0 (F x) a' a h l)). unfold l.
   rewrite (back' (H4 x a') k). apply cancel_left.
Qed.

Definition ϵnat := (@eta X (@flipA X Arrows1) (@e X Arrows1 H1)
  (@CatId_instance_0 X Arrows1 CatId1)
  (@CatComp_instance_0 X Arrows1 CatComp1)
  (@cat X Arrows1 H1 CatId1 CatComp1 H2) A (@flipA A Arrows0)
  (@e A Arrows0 H) (@CatId_instance_0 A Arrows0 CatId0)
  (@CatComp_instance_0 A Arrows0 CatComp0)
  (@cat A Arrows0 H CatId0 CatComp0 H0) G (functor_op G Ga) F (functor_op F Fa) 
  (fun (a : A) (x : X) => φinv x a) _ inverse  op_adj).
End counit.

