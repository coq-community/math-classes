Set Automatic Introduction.

(** We prove the equivalence of the two definitions of adjunction *)
Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra setoids functors categories.
(*
Section New_Adjunction.
  Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F Fa} (* todo: we don't want to name Fa and Fg here *)
    (G: A → X) `{!Functor G Ga}
    (φ: Π {x a}, (F x ⟶ a) → (x ⟶ G a))
    `{Π x a, Inv (φ x a)}
    `{Π x a, Bijective (φ x a)}
    (φ_adj:Adjunction _ _ φ).
Implicit Arguments φ [[x] [a]].
(* The definition of adjunction in terms of arrows, i.e. using the right_adjunct *)
Context `{f:F x ⟶ a}.
Lemma rad_l `(k:a  ⟶ a'): φ (k ◎ f)= (fmap G k) ◎ φ f.

Admitted.
Lemma rad_r `(h:x' ⟶ x): φ (f ◎ fmap F h) = φ f ◎ h.
Admitted.


  Context `{Category C} `{Category D}
    `{!Functor (F: C → D) F'} (* todo: we don't want to name F' and F' here *)
    `{!Functor (G: D → C) G'}
    (η: id ⇛ G ∘ F) `{!NaturalTransformation η}
    (φ: Π (x: C) (y: D) (f: x ⟶ G y), F x ⟶ y).

  Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F} (* todo: we don't want to name Fa and Fg here *)
    (G: A → X) `{!Functor G Ga}
    (φ: Π {x a}, (F x ⟶ a) → (x ⟶ G a))
    (φinv: Π {x a}, Inv (@φ x a))
(*Can we make the inverse implicit??*)
    `{Π x a, Bijective' (φ x a) (*(φinv x a)*)}.

  Class Adjunction': Prop :=
   { natural_left `(k: a ⟶ a'): `((fmap G k ◎) ∘ φ = @φ x _ ∘ (k ◎))
   ; natural_right `(h: x' ⟶ x):`((◎ h) ∘ @φ _ a = φ ∘ (◎ fmap F h)) }.

End New_Adjunction.
*)
Section adj2alt_adj.

Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F Fa} (* todo: we don't want to name Fa and Fg here *)
    (G: A → X) `{!Functor G Ga}
    (φ: Π {x a}, (F x ⟶ a) → (x ⟶ G a))
    `{Π x a, Inv (φ x a)}
    `{Π x a, Bijective (φ x a)}
    (φ_adj:Adjunction _ _ φ).

Lemma rad_l `{f:F x ⟶ a}`(k:a  ⟶ a'): φ _ _ (k ◎ f)= (fmap G k) ◎ φ _ _ f.
symmetry.
apply  (@natural_left _ _ _ _ _ _ _ F _ G _ φ φ_adj _ _ k).
(* TODO: simplify *)
Qed.

Lemma rad_r `{f:F x ⟶ a}`(h:x' ⟶ x): φ _ _ (f ◎ fmap F h) = φ _ _ f ◎ h.
Admitted.

Definition η:id ⇛ G ∘ F:=
  (λ x:X => (@φ x (F x) (@cat_id A _ _ (F x)))).

Implicit Arguments φ [[a] [x]].

Hint Unfold id compose:typeclass_instances.
Instance: (NaturalTransformation η).
unfold NaturalTransformation. 
(* MacLane p81 *)
unfold η. intros x' x h.
symmetry.
setoid_replace (fmap (G ∘ F) h ◎ φ cat_id) with (φ (fmap F h ◎ cat_id)).

Focus 2. symmetry. rewrite rad_l. cut (fmap G (fmap F h)=  fmap (G ∘ F) h).
intro. rewrite H5. reflexivity. admit.
setoid_replace (φ (fmap F h ◎ cat_id)) with (φ ( cat_id ◎ (fmap F h))).
Focus 2. transitivity (φ (fmap F h)). assert ((fmap F h ◎ cat_id) = (fmap F h)) by apply id_r.
(* rewrite H5. ??? f_equal ???*) admit. admit.
setoid_replace (φ (cat_id ◎ fmap F h)) with (φ cat_id ◎ fmap id h) by apply rad_r.
reflexivity.
Qed.

(**
It is a natural transformation because:
GF h ∘ (φ (cat_id (F x')))=(φ (fmap F h∘ cat_id (F x')))
   = φ ( cat_id (F x) ∘ (fmap F h))
   = φ ( cat_id (F x) ∘ h

Based on the naturality of φ.
*)