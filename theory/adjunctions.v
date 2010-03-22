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

Instance: NaturalTransformation η.
 unfold NaturalTransformation. 
 (* MacLane p81 *)
 unfold η. intros x' x h.
 symmetry.
 setoid_replace (fmap (G ∘ F) h ◎ φ cat_id) with (φ (fmap F h ◎ cat_id)).
  Focus 2.
  symmetry.
  rewrite rad_l; [| apply _].
  cut (fmap G (fmap F h)=  fmap (G ∘ F) h).
   intro. rewrite H5. reflexivity.
  symmetry.
   (* apply preserves_comp. TODO: Prove for normal arrow in Sets *) admit.
  setoid_replace (φ (fmap F h ◎ cat_id)) with (φ ( cat_id ◎ (fmap F h))).
Focus 2. transitivity (φ (fmap F h)). 
rewrite id_r.
(* TODO: add Hint that bijective is a Steoid_Morphism. *)
reflexivity.
rewrite id_l. reflexivity.
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


Lemma φarrows `(f:(F x)  ⟶ a):φ f = (fmap G f)  ◎ (η x).
Proof with reflexivity.
rewrite <- (id_r  f).
(* TODO: Finish the proof by autorewrite *)
rewrite  rad_l by apply _.
rewrite id_r...
Qed.

Definition ϵ  : F ∘ G ⇛ id :=
  (λ a:A => (@inv _  _ (@φ (G a) a) _ (@cat_id X _ _ (G a)))).

(*
Instance: ∀ x y, Setoid_Morphism (@inv _  _ (@φ x y)).
 intros.
 destruct (H4 x y).
 destruct bijective_injective.
 apply _.
Qed.
*)

Instance: NaturalTransformation ϵ.
 unfold NaturalTransformation. 
 (* MacLane p82 *)
 unfold ϵ. intros a' a k.
 symmetry. 
(* ETC ... Can we use the op-cat?? 

 setoid_replace (fmap (G ∘ F) h ◎ φ cat_id) with (φ (fmap F h ◎ cat_id)).
  Focus 2.
  symmetry.
  rewrite rad_l; [| apply _].
  cut (fmap G (fmap F h)=  fmap (G ∘ F) h).
   intro. rewrite H5. reflexivity.
  symmetry.
   (* apply preserves_comp. TODO: Prove for normal arrow in Sets *) admit.
  setoid_replace (φ (fmap F h ◎ cat_id)) with (φ ( cat_id ◎ (fmap F h))).
Focus 2. transitivity (φ (fmap F h)). 
rewrite id_r.
(* TODO: add Hint that bijective is a Steoid_Morphism. *)
reflexivity.
rewrite id_l. reflexivity.
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


Lemma φarrows `(f:(F x)  ⟶ a):φ f = (fmap G f)  ◎ (η x).
Proof with reflexivity.
rewrite <- (id_r  f).
(* TODO: Finish the proof by autorewrite *)
rewrite  rad_l by apply _.
rewrite id_r...
Qed.


