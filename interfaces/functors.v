Global Set Automatic Introduction. (* todo: do this in a more sensible place *)

Require Import abstract_algebra canonical_names Program setoids.

Section functor_class.

  Context `{Category C} `{Category D} (map_obj: C → D).

  Class Fmap: Type := fmap: Π {v w: C}, (v ⟶ w) → (map_obj v ⟶ map_obj w).

  Class Functor `(Fmap): Prop :=
    { functor_morphism:> Π a b: C, Setoid_Morphism (@fmap _ a b)
    ; preserves_id: `(fmap (cat_id: a ⟶ a) = cat_id)
    ; preserves_comp `(f: y ⟶ z) `(g: x ⟶ y): fmap (f ◎ g) = fmap f ◎ fmap g }.

End functor_class.

Section id_functor.

  Context `{Category C}.

  Global Instance: Fmap id := λ _ _ => id.

  Global Instance id_functor: Functor (id: C → C) _.
  Proof.
   constructor; try reflexivity. intros.
   change (Setoid_Morphism (id: (a ⟶ b) → (a ⟶ b))).
   apply _.
  Qed.

End id_functor.

Section compose_functors.

  Context
    `{Category A} `{Category B} `{Category C}
    `{!Functor (f: B → C) f'} `{!Functor (g: A → B) g'}.

  Global Instance comp_Fmap: Fmap (f ∘ g) := λ _ _ => fmap f ∘ fmap g.

  Global Instance compose_functors: Functor (f ∘ g) _.
  Proof with intuition; try apply _.
   constructor; intros.
     apply (@compose_setoid_morphisms _ _ _ _ _ _)...
     apply (@functor_morphism _ _ _ _ _ _ _ _ _ _ f _)...
     (* todo: this part really should be automatic *)
    change (fmap f (fmap g (cat_id: a ⟶ a)) = cat_id).
    repeat try rewrite preserves_id...
   change (fmap f (fmap g (f0 ◎ g0)) = fmap f (fmap g f0) ◎ fmap f (fmap g g0)).
   repeat try rewrite preserves_comp...
  Qed.

End compose_functors.
