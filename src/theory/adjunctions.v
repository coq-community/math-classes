(** We prove the equivalence of the two definitions of adjunction. *)

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra setoids interfaces.functors categories
  workaround_tactics theory.jections.
Require dual.

Hint Unfold id compose: typeclass_instances. (* todo: move *)

Lemma equal_because_sole `{Setoid T} (P: T → Prop) x: is_sole P x → forall y z, P y → P z → y = z.
Proof. firstorder. Qed. (* todo: move *)

Section for_φAdjunction.

  (* MacLane p79/p80, showing that from an φAdjunction we can make
   both a ηAdjunction and a ηεAdjunction. *)

  Context `(φAdjunction).

  Implicit Arguments φ [[d] [c]].

  Let hint''''' := φ_adjunction_bijective F G.
  Let hint'''' x y: Injective (@φ x y) := _.
  Let hint := φ_adjunction_left_functor F G.
  Let hint' := φ_adjunction_right_functor F G.
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.
   (* Waiting for the new proof engine ... *)

  Lemma φ_adjunction_natural_right_inv `(g: c ⟶ G d) `(h: c' ⟶ c): φ⁻¹ (g ◎ h) = φ⁻¹ g ◎ fmap F h.
  Proof with try reflexivity; try apply _.
   intros.
   apply (injective φ).
   rewrite surjective_applied...
   rewrite φ_adjunction_natural_right...
   rewrite surjective_applied...
  Qed.

  Lemma φ_adjunction_natural_left_inv `(g: c ⟶ G d) `(k: d ⟶ d'): φ⁻¹ (fmap G k ◎ g) = k ◎ φ⁻¹ g.
  Proof with try reflexivity; try apply _.
   intros.
   apply (injective φ).
   rewrite surjective_applied...
   rewrite φ_adjunction_natural_left...
   rewrite surjective_applied...
  Qed.

  Let η: id ⇛ G ∘ F := λ c, φ (cat_id: F c ⟶ F c).
  Let ε: F ∘ G ⇛ id := λ d, φ ⁻¹ (cat_id: G d ⟶ G d).

  Global Instance η_natural: NaturalTransformation η.
  Proof with try reflexivity; try apply _.
   intros x' x h.
   change (φ cat_id ◎ h = fmap G (fmap F h) ◎ φ cat_id).
   rewrite <- φ_adjunction_natural_left, <- φ_adjunction_natural_right, left_identity, right_identity...
  Qed.

  Global Instance: NaturalTransformation ε.
  Proof with try reflexivity; try apply _.
   intros d d' f.
   change ((φ ⁻¹) cat_id ◎ fmap F (fmap G f) = f ◎ (φ ⁻¹) cat_id).
   rewrite <- φ_adjunction_natural_left_inv, <- φ_adjunction_natural_right_inv, left_identity, right_identity...
  Qed.

  Lemma φ_in_terms_of_η `(f: F x ⟶ a): φ f = fmap G f ◎ η x.
  Proof.
   rewrite <- (right_identity f) at 1.
   rewrite φ_adjunction_natural_left. reflexivity. apply _.
  Qed.

  Lemma φ_in_terms_of_ε `(g: x ⟶ G a): φ⁻¹ g = ε a ◎ fmap F g.
  Proof.
   rewrite <- (left_identity g) at 1.
   apply φ_adjunction_natural_right_inv.
  Qed.

  Definition univwit (c : C) (d : D): (c ⟶ G d) → (F c ⟶ d) := φ⁻¹.

  Instance: ∀ c, UniversalArrow (η c: c ⟶ G (F c)) (univwit c).
  Proof.
   unfold univwit.
   constructor; unfold compose.
    rewrite <- (φ_in_terms_of_η ((φ ⁻¹) f)).
    symmetry.
    apply surjective_applied.
   intros ? E.
   rewrite E.
   rewrite <- (φ_in_terms_of_η y).
   symmetry.
   apply bijective_applied.
  Qed.

  Instance φAdjunction_ηAdjunction: ηAdjunction F G η univwit.

  Instance φAdjunction_ηεAdjunction: ηεAdjunction F G η ε.
  Proof with try apply _.
   constructor; try apply _; intro x.
    rewrite <- @φ_in_terms_of_η.
    unfold ε. apply surjective_applied.
   rewrite <- @φ_in_terms_of_ε.
   unfold η. apply surjective_applied.
  Qed.

  (* On a side note, if we let F and G map between the duals of C and D, the adjunction is reversed: *)

  Goal @φAdjunction D _ _ _ _ C _ _ _ _ G (dual.fmap_op G) F (dual.fmap_op F) (λ d c, (@φ c d)⁻¹)
    (λ d c, @φ c d).
  Proof with try apply _.
   constructor; intros...
     pose proof (φ_adjunction_bijective F G)...
    change (d' ⟶ d) in k.
    change (d ⟶ G c) in f.
    change ((φ ⁻¹) (f ◎ k) = (φ ⁻¹) f ◎ fmap F k).
    apply (injective (@φ d' c)).
    rewrite surjective_applied.
    rewrite φ_adjunction_natural_right...
    rewrite surjective_applied.
    reflexivity.
   change (c ⟶ c') in h.
   change (d ⟶ G c) in f.
   change ((φ ⁻¹) (fmap G h ◎ f) = h ◎ (φ ⁻¹) f).
   apply (injective (@φ d c')).
   rewrite surjective_applied.
   rewrite φ_adjunction_natural_left...
   rewrite surjective_applied.
   reflexivity.
  Qed.

End for_φAdjunction.

Section for_ηAdjunction.

  Context `(ηAdjunction).

  Let hint := η_adjunction_left_functor F G.
  Let hint' := η_adjunction_right_functor F G.
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.

  Let φ x a (g: F x ⟶ a): (x ⟶ G a) := fmap G g ◎ η x.

  Instance: ∀ (c: C) (d: D), Inverse (@φ c d) := uniwit.

  Instance: ∀ x a, Surjective (@φ x a).
  Proof with try apply _.
   unfold φ.
   repeat intro.
   constructor.
    intros x0 y E. symmetry.
    rewrite <- E.
    apply (η_adjunction_universal F G x).
   constructor...
   intros ?? E. rewrite E. reflexivity.
  Qed.

  Instance: ∀ x a, Injective (@φ x a).
  Proof with try reflexivity; try apply _; auto.
   repeat intro. constructor... unfold φ. repeat intro.
   apply (equal_because_sole _ _ (η_adjunction_universal F G _ _ (fmap G x0 ◎ η x))); unfold compose...
  Qed.

  Instance: ∀ x a, Bijective (@φ x a).

  Instance ηAdjunction_φAdjunction: φAdjunction F G φ.
  Proof with try reflexivity; try apply _.
   unfold φ. unfold id in *. unfold compose in η.
   constructor...
    repeat intro. unfold compose.
    rewrite associativity...
    rewrite preserves_comp...
   repeat intro. unfold compose.
   rewrite preserves_comp...
   rewrite <- associativity.
   pose proof (η_adjunction_natural F G c' c h) as P.
   change (η c ◎ h = fmap G (fmap F h) ◎ η c') in P.
   rewrite <- P.
   rewrite associativity...
  Qed.

End for_ηAdjunction.

Section for_ηεAdjunction.

  Context `(ηεAdjunction).

  Let hint := ηε_adjunction_left_functor F G.
  Let hint' := ηε_adjunction_right_functor F G.
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.
  Let hint'''' := ηε_adjunction_η_natural F G.
  Let hint''''' := ηε_adjunction_ε_natural F G.

  Let φ `(f: F c ⟶ d): (c ⟶ G d) := fmap G f ◎ η c.
  Instance uniwit c d: Inverse (φ c d) := λ f, ε d ◎ fmap F f.

  Instance ηεAdjunction_ηAdjunction: ηAdjunction F G η uniwit.
  Proof with try apply _.
   constructor...
   unfold uniwit.
   constructor; unfold compose.
    rewrite preserves_comp...
    pose proof (ηε_adjunction_η_natural F G c (G d) f) as P.
    change (η (G d) ◎ f = fmap G (fmap F f) ◎ η c) in P.
    rewrite <- associativity.
    rewrite <- P.
    rewrite associativity.
    pose proof (ηε_adjunction_identity_at_G F G d) as Q.
    simpl in Q.
    rewrite Q.
    symmetry.
    apply left_identity.
   intros y E. rewrite E. clear E f.
   rewrite preserves_comp...
   rewrite associativity.
   pose proof (ηε_adjunction_ε_natural F G (F c) d y) as P.
   change (ε d ◎ fmap F (fmap G y) = y ◎ ε (F c)) in P.
   rewrite P.
   rewrite <- associativity.
   pose proof (ηε_adjunction_identity_at_F F G c) as Q.
   simpl in Q.
   rewrite Q.
   symmetry.
   apply right_identity.
  Qed.

  Instance ηεAdjunction_φAdjunction: φAdjunction F G φ.
  Proof. apply ηAdjunction_φAdjunction, _. Qed.

End for_ηεAdjunction.
