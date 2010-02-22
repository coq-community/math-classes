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

  Section initiality. (* todo: typeclassify *)

    Definition proves_initial {x: X} (f: Π y, x ⟶ y): Prop := Π y f', f y = f'.

    Definition initial (x: X): Type := Π y: X, sig (λ a: x ⟶ y => Π a': x ⟶ y, a = a').

    Lemma initials_unique' (x x': X) (a: Π y, x ⟶ y) (b: Π y, x' ⟶ y):
      proves_initial a → proves_initial b → iso_arrows (a x') (b x).
    Proof with reflexivity.
     intros H1 H2. split.
      rewrite <- (H2 _ cat_id). rewrite <- H2...
     rewrite <- (H1 _ cat_id). rewrite <- H1...
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

    Record Product: Type := mkProduct
      { product_object:> X
      ; project: Π i, product_object ⟶ component i
      ; prod_factor: Π (c: X), (Π i, c ⟶ component i) → (c ⟶ product_object) }.

    Definition is_product (candidate: X) (proj: Π i, candidate ⟶ component i)
      (h: Π (c: X) (ccomp: Π i, c ⟶ component i), c ⟶ candidate): Prop
        := Π c ccomp, is_sole (λ h' => Π i, ccomp i = proj i ◎ h') (h c ccomp).

    Definition is_product' (p: Product): Prop
        := Π c ccomp, is_sole (λ h' => Π i, ccomp i = project p i ◎ h') (prod_factor p c ccomp).

(*    Class IsProduct (p: Product) := is_p: is_product p. *)
(*
    Record Product: Type := product
      { product_object:> X
      ; project: Π i, A product_object (component i)
      ; factor: Π (c: X) (ccomp: Π i, A c (component i)), A c product_object
      ; correct: is_product product_object project factor
      }.
*)
(*
    Existing Class Product.
*)
    Lemma help_products_unique (d: X) (proj: Π i, d ⟶ component i) h:
      is_product d proj h →
      is_sole (λ a: d ⟶ d => Π i, proj i = proj i ◎ a) cat_id.
    Proof with intuition.
     intros.
     split; intros.
      symmetry.
      apply id_r.
     destruct (H1 d proj).
     clear H1.
     rewrite (H4 y)...
     rewrite (H4 cat_id)...
     intros.
     symmetry.
     apply id_r.
    Qed.

    Lemma products_unique (c c': X) (proj: Π i, c ⟶ component i) (proj': Π i, c' ⟶ component i)
      h h':
      is_product _ proj h → is_product _ proj' h' → iso_arrows (h c' proj') (h' c proj).
    Proof with auto.
     intro.
     intros.
     split.
      destruct (help_products_unique c proj h H1).
      apply H4.
      intro.
      rewrite comp_assoc.
      destruct (H1 c' proj').
      destruct (H2 c proj).
      rewrite <- H5...
     destruct (help_products_unique c' proj' h' H2).
     apply H4.
     intro.
     rewrite comp_assoc.
     destruct (H1 c' proj').
     destruct (H2 c proj).
     rewrite <- H7...
    Qed.

  End products.

  Class Producer: Type := produce: Π `(c: Index → X), Product c.

  Definition binary_product `{Producer} (x y: X): Product (λ b: bool => if b then x else y) := produce _.
  Definition empty_product `{Producer}: Product (λ f: False => match f with end) := produce _.

  Class Produces `{Producer}: Prop :=
    produces: Π `(c: Index → X), is_product' _ (produce c).

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
Implicit Arguments Produces [[Arrows0] [H] [CatComp0] [H1]]. (* todo: rename args *)
