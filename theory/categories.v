Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra setoids functors.

Notation "x ⇛ y" := (Π a, x a ⟶ y a) (at level 90, right associativity).
  (* Transformations (polymorphic arrows). Couldn't find an "arrow with dot over it" unicode character. *)

(* Natural transformations: *)

Section natural_transformation.

  Context `{Category C} `{Category D} `{!Functor (F: C → D) Fa} `{!Functor (G: C → D) Ga}.

  Class NaturalTransformation (η: Π c, F c ⟶ G c): Prop :=
    natural: Π (x y: C) (f: x ⟶ y), η y ◎ fmap F f = fmap G f ◎ η x.

End natural_transformation.

(* The elegant symmetrical definition of adjunctions: *)

Section adjunction.

  Context `{Category A} `{Category X}
    (F: X → A) `{!Functor F Fa} (* todo: we don't want to name Fa and Fg here *)
    (G: A → X) `{!Functor G Ga}
    (φ: Π {x a}, (F x ⟶ a) → (x ⟶ G a))
    `{Π x a, Bijective (φ x a)}.

  Implicit Arguments φ [[x] [a]].

  Class Adjunction: Prop :=
   { natural_left `(k: a ⟶ a'): `((fmap G k ◎) ∘ φ = @φ x _ ∘ (k ◎))
   ; natural_right `(h: x' ⟶ x):`((◎ h) ∘ @φ _ a = φ ∘ (◎ fmap F h)) }.

End adjunction.

(* The more practical definition via universal morphisms: *)

Section alt_adjunction.

  Context `{Category C} `{Category D}
    `{!Functor (F: C → D) F'} (* todo: we don't want to name F' and F' here *)
    `{!Functor (G: D → C) G'}
    (η: id ⇛ G ∘ F) `{!NaturalTransformation η}
    (φ: Π (x: C) (y: D) (f: x ⟶ G y), F x ⟶ y).

  Class AltAdjunction: Prop :=
   { alt_adjunction_natural_unit: NaturalTransformation η (* todo: really necessary? *)
   ; alt_adjunction_factor: Π (x: C) (y: D) (f: x ⟶ G y),
       is_sole ((f =) ∘ (◎ η x) ∘ fmap G) (φ x y f) }.

End alt_adjunction.

Section contents.

  Context `{Category X}.

  Class Mono `(a: x ⟶ y): Prop :=
    mono: Π z (f g: z ⟶ x), a ◎ f = a ◎ g → f = g.

  Section isomorphy.

    Definition iso_arrows {x y: X} (a: x ⟶ y) (b: y ⟶ x): Prop
      := a ◎ b = cat_id ∧ b ◎ a = cat_id. (* todo: product *)

    Global Instance: HeteroSymmetric (@iso_arrows).
    Proof. unfold iso_arrows. repeat intro. intuition. Qed.

    Definition is_iso {x y: X} (a: x ⟶ y): Prop := ex (iso_arrows a).

    Definition isos_unique (x y: X) (a: x ⟶ y) (b b': y ⟶ x): iso_arrows a b → iso_arrows a b' → b = b'.
    Proof. intros [P Q] [R S]. rewrite <- id_l. rewrite <- S, <- comp_assoc, P. apply id_r. Qed.

    Definition iso: Equiv X := λ x y => ex (uncurry (@iso_arrows x y)).
    Definition isoT: X → X → Type := λ x y => sig (uncurry (@iso_arrows x y)).

    Program Instance: Reflexive iso := λ x => ex_intro _ (cat_id, cat_id) _.
    Next Obligation. split; apply id_l. Qed.

    Instance: Symmetric iso.
    Proof. intros ? ? [[f f'] ?]. exists (f', f). unfold uncurry. apply (hetero_symmetric). assumption. Qed.

    Instance: Transitive iso.
    Proof with assumption.
     intros ? ? ? [[f f'] [U V]] [[g g'] [W Z]].
     exists (g ◎ f, f' ◎ g').
     split; simpl in *.
      rewrite <- comp_assoc, (comp_assoc g' f' f), U, id_l...
     rewrite <- comp_assoc, (comp_assoc f g g'), Z, id_l...
    Qed.

    Global Instance iso_equivalence: Equivalence iso.
    Global Instance iso_setoid: @Setoid X iso.

    Lemma arrows_between_isomorphic_objects (a b c d: X)
      (ab: a ⟶ b) (ba: b ⟶ a) (cd: c ⟶ d) (dc: d ⟶ c) (ac: a ⟶ c) (bd: b ⟶ d):
       iso_arrows ab ba → iso_arrows cd dc →
        ac ◎ ba = dc ◎ bd →
        bd ◎ ab = cd ◎ ac.
    Proof. (* shows that you only need one half of the diagram to commute for the other half to commute as well*)
     intros [H1 H4] [H2 H5] H3.
     rewrite <- (id_l (comp bd ab)).
     rewrite <- H2.
     rewrite <- comp_assoc.
     rewrite (comp_assoc ab bd dc).
     rewrite <- H3.
     rewrite <- comp_assoc.
     rewrite H4.
     rewrite id_r.
     reflexivity.
    Qed.

    Program Definition refl_arrows (x: X): isoT x x := (cat_id, cat_id).
    Next Obligation. split; apply id_l. Qed.

  End isomorphy.

  Section initiality.

    Class InitialArrow (x: X): Type := initial_arrow: Π y, x ⟶ y.

    Class Initial (x: X) `{InitialArrow x}: Prop :=
      initial_arrow_unique: Π y f', initial_arrow y = f'.

    Definition initial (x: X): Type := Π y: X, sig (λ a: x ⟶ y => Π a': x ⟶ y, a = a').

    Lemma initials_unique' (x x': X) `{Initial x} `{Initial x'}:
      iso_arrows (initial_arrow x': x ⟶ x') (initial_arrow x).
    Proof with reflexivity.
     split. rewrite <- (H4 _ cat_id), <- H4...
     rewrite <- (H2 _ cat_id), <- H2...
    Qed.

    Program Lemma initials_unique (x x': X) (a: initial x) (b: initial x'): iso_arrows (a x') (b x).
    Proof.
     split.
      destruct (b x') as [? e1]. rewrite <- e1. apply e1.
     destruct (a x) as [? e0]. rewrite <- e0. apply e0.
    Qed.

  End initiality.

  Section products.

    Context {I: Type} (component: I → X).

    Section def.

      Context (product: X).

      Class ElimProduct: Type := tuple_proj: Π i, product ⟶ component i.
      Class IntroProduct: Type := make_tuple: Π x, (Π i, x ⟶ component i) → (x ⟶ product).

      Class Product `{ElimProduct} `{IntroProduct}: Prop :=
        product_factors: Π c ccomp, is_sole (λ h' => Π i, ccomp i = tuple_proj i ◎ h')
          (make_tuple c ccomp).

      Lemma tuple_round_trip `{Product} (x: X) (h: Π i, x ⟶ component i) i:
        tuple_proj i ◎ make_tuple x h = h i.
      Proof. symmetry. apply product_factors. Qed.

    End def.

    Lemma products_unique `{Product c} `{Product c'}:
      iso_arrows
        (make_tuple c c' (tuple_proj c'))
        (make_tuple c' c (tuple_proj c)).
    Proof with intuition.
     unfold iso_arrows.
     revert c H1 H2 H3 c' H4 H5 H6.
     cut (Π `{Product x} `{Product y},
       make_tuple x y (tuple_proj y) ◎ make_tuple y x (tuple_proj x) = cat_id)...
     pose proof (proj2 (product_factors x x (tuple_proj x))) as Q.
     rewrite (Q cat_id)... rewrite Q...
      rewrite comp_assoc.
      repeat rewrite tuple_round_trip...
     rewrite id_r...
    Qed.

  End products.

  Class Producer: Type := product I: (I → X) → X.

  Class HasProducts `{Producer}
    `{Π I c, ElimProduct c (product I c)}
    `{Π I c, IntroProduct c (product I c)}: Prop :=
      makes_products: Π I (c: I → X), Product c (product I c).

(*
  Definition binary_product `{Producer} (x y: X): Product (λ b: bool => if b then x else y) := produce _.
  Definition empty_product `{Producer}: Product (λ f: False => match f with end) := produce _.
*)

  Section freedom.

    Context `{Category B} (forget: X → B) `{!Functor forget forget_arr} (S: B).

    Section candidate.

      Context {x} (inject: S ⟶ forget x).

      Definition proves_free (factor: Π x', (S ⟶ forget x') → (x ⟶ x')): Prop :=
          Π x' (inject': S ⟶ forget x'), is_sole ((inject' =) ∘ (◎ inject) ∘ fmap forget) (factor _ inject').

      Definition free: Prop := ex proves_free.

    End candidate.

    Lemma frees_unique (x x': X) (inject: S ⟶ forget x) (inject': S ⟶ forget x')
      (factor: Π z, (S ⟶ forget z) → (x ⟶ z))
      (factor': Π z, (S ⟶ forget z) → (x' ⟶ z)):
       proves_free inject factor → proves_free inject' factor' →
       iso_arrows (factor _ inject') (factor' _ inject).
    Proof with auto; try reflexivity; try apply _.
     intros P Q.
     pose proof (proj1 (P _ inject')) as E.
     pose proof (proj2 (P _ inject)) as R.
     pose proof (proj1 (Q _ inject)) as E'.
     pose proof (proj2 (Q _ inject')) as R'.
     clear P Q.
     unfold compose in *.
     split.
      rewrite (R' cat_id)...
       apply (R' (factor _ inject' ◎ factor' _ inject)).
       rewrite preserves_comp...
       rewrite <- comp_assoc, <- E'...
      rewrite preserves_id, id_l...
     rewrite (R cat_id)...
      apply (R (factor' _ inject ◎ factor _ inject')).
      rewrite preserves_comp...
      rewrite <- comp_assoc, <- E...
     rewrite preserves_id, id_l...
    Qed.

  End freedom.

End contents.

Lemma freedom_as_adjunction
  `{Category Base} `{Category Extra}
  `{!Functor (forget: Extra → Base) forget_arr}
  `{!Functor (freeF: Base → Extra) free_arr}
  (eta: id ⇛ forget ∘ freeF)
  (phi: Π x y, (x ⟶ forget y) → (freeF x ⟶ y))
  `{!AltAdjunction eta phi}:
    Π b, proves_free forget b (eta b) (phi b).
Proof. exact (alt_adjunction_factor _ _). Qed.

Implicit Arguments Producer [].
Implicit Arguments HasProducts [[Arrows0] [H] [CatComp0] [H1] [H2] [H3]]. (* todo: rename args *)
Implicit Arguments product [[X] [Producer] [I]].
