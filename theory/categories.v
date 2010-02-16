Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra setoids.

Section functor_class.

  Context `{Category C} `{Category D} (map_obj: C -> D).

  Class Fmap: Type := fmap: forall {v w: C}, (v --> w) -> (map_obj v --> map_obj w).

  Class Functor `(Fmap): Prop :=
    { functor_morphism:> forall (a b: C), Setoid_Morphism (@fmap _ a b)
    ; preserves_id: forall a, fmap (cat_id: a --> a) == cat_id
    ; preserves_comp: forall x y z (f: y --> z) (g: x --> y),
        fmap (comp f g) == comp (fmap f) (fmap g) }.

End functor_class.

Section adjunction.

  Context `{Category A} `{Category X}
    (F: X -> A) `{!Functor F Fa} (* todo: we don't want to name Fa and Fg here *)
    (G: A -> X) `{!Functor G Ga}
   (φ: forall {x a}, (F x --> a) -> (x --> G a))
   `{forall x a, Bijective (φ x a)}.

  Implicit Arguments φ [[x] [a]].

  Class Adjunction: Prop :=
   { natural_left: forall (x: X) (a a': A) (k: a --> a'),
       pointwise_relation _ equiv (comp (fmap G k) ∘ φ) (@φ x _ ∘ comp k)
   ; natural_right: forall (x x': X) (a: A) (h: x' --> x),
       pointwise_relation _ equiv (flip comp h ∘ @φ _ a) (φ ∘ flip comp (fmap F h))
   }.

End adjunction.

Section id_functor.

  Context `{Category C}.

  Global Instance: Fmap id := fun _ _ => id.

  Global Instance id_functor: Functor (id: C -> C) _.
  Proof.
   intros.
   pose proof arrow_equiv.
   unfold id.
   constructor; try reflexivity.
   intros.
   apply id_setoid_morphism.
  Qed.

End id_functor.

Instance compose_functors
  `{@Functor Ao Aa Ae Aid Acomp Bo Ba Be Bid Bcomp AB_obj AB_arrow}
  `{@Functor Bo Ba _ _ _ Co Ca Ce Cid Ccomp BC_obj BC_arrow}:
    @Functor Ao Aa _ _ _ Co Ca _ _ _
      (BC_obj ∘ AB_obj) (fun _ _ => BC_arrow _ _ ∘ AB_arrow _ _).
Proof. (* todo: ugly *)
   constructor.
     intros.
     set (BC_arrow (AB_obj a) (AB_obj b)).
     set (AB_arrow a b).
     apply (@compose_setoid_morphisms _ _ _ _ _ _).
      apply _.
     subst a0.
     destruct H0.
     apply functor_morphism0.
    unfold Basics.compose.
    intros.
    destruct H, H0.
    destruct (functor_morphism1 (AB_obj a) (AB_obj a)).
    destruct (functor_morphism0 a a).
    unfold fmap.
    rewrite preserves_id0.
    rewrite preserves_id1.
    reflexivity.
   unfold Basics.compose.
   intros.
   destruct H, H0.
   destruct (functor_morphism0 x z).
   destruct (functor_morphism1 (AB_obj x) (AB_obj y)).
   destruct (functor_morphism1 (AB_obj x) (AB_obj z)).
   destruct (functor_morphism0 x y).
   unfold fmap.
   rewrite preserves_comp0.
   rewrite preserves_comp1.
   reflexivity.
  Qed. (* todo: clean up. those destructs should not be needed *)

Definition is_sole `{Equiv T} (P: T -> Prop) (x: T): Prop :=
  P x /\ forall y, P y -> y == x. (* todo: move *)

Section contents.

  Context `{Category X}.

  Class Mono {x y} (a: x --> y): Prop :=
    mono: forall z (f g: z --> x), comp a f == comp a g -> f == g.

  Section isomorphy.

    Definition iso_arrows {x y: X} (a: x --> y) (b: y --> x): Prop
      := comp a b == cat_id /\ comp b a == cat_id. (* todo: product *)

    Global Instance: HeteroSymmetric (@iso_arrows).
    Proof. unfold iso_arrows. repeat intro. intuition. Qed.

    Definition is_iso {x y: X} (a: x --> y): Prop := ex (iso_arrows a).

    Definition isos_unique (x y: X) (a: x --> y) (b b': y --> x): iso_arrows a b -> iso_arrows a b' -> b == b'.
    Proof. intros [P Q] [R S]. rewrite <- id_l. rewrite <- S, <- comp_assoc, P. apply id_r. Qed.

    Definition iso: Equiv X := fun x y => ex (uncurry (@iso_arrows x y)).
    Definition isoT: X -> X -> Type := fun x y => sig (uncurry (@iso_arrows x y)).

    Instance: Reflexive iso.
    Proof. repeat intro. exists (@cat_id _ _ _ x, @cat_id _ _ _ x). split; apply id_l. Qed.

    Instance: Symmetric iso.
    Proof. intros ? ? [[f f'] ?]. exists (f', f). unfold uncurry. apply (hetero_symmetric). assumption. Qed.

    Instance: Transitive iso.
    Proof with assumption.
     intros ? ? ? [[f f'] [U V]] [[g g'] [W Z]].
     exists (comp g f, comp f' g').
     split; simpl.
      rewrite <- comp_assoc, (comp_assoc g' f' f), U, id_l...
     rewrite <- comp_assoc, (comp_assoc f g g'), Z, id_l...
    Qed.

    Global Instance iso_equivalence: Equivalence iso.
    Global Instance iso_setoid: @Setoid X iso.

    Lemma arrows_between_isomorphic_objects (a b c d: X)
      (ab: a --> b) (ba: b --> a) (cd: c --> d) (dc: d --> c) (ac: a --> c) (bd: b --> d):
       iso_arrows ab ba -> iso_arrows cd dc ->
        comp ac ba == comp dc bd ->
        comp bd ab == comp cd ac.
    Proof. (* shows that you only need one half of the diagram to commute for the other half to commute as well*)
     intros.
     rewrite <- (id_l _ _ (comp bd ab)).
     destruct H1, H2.
     rewrite <- H2.
     rewrite <- comp_assoc.
     rewrite (comp_assoc ab bd dc).
     rewrite <- H3. clear H3.
     rewrite <- comp_assoc.
     rewrite H4.
     rewrite id_r.
     reflexivity.
    Qed.

    Program Definition refl_arrows (x: X): isoT x x
      := (@cat_id _ _ _ x, @cat_id _ _ _ x).
    Next Obligation. split; apply id_l. Qed.

  End isomorphy.

  Section initiality.

    Definition proves_initial {x: X} (f: forall y, x --> y): Prop := forall y f', f y == f'.

    Definition initial (x: X): Type := forall y: X, sig (fun a: x --> y => forall a': x --> y, a == a').

    Lemma initials_unique' (x x': X) (a: forall y, x --> y) (b: forall y, x' --> y):
      proves_initial a -> proves_initial b -> iso_arrows (a x') (b x).
    Proof with reflexivity.
     intros H1 H2. split.
      rewrite <- (H2 x' cat_id). rewrite <- H2...
     rewrite <- (H1 x cat_id). rewrite <- H1...
    Qed.

    Lemma initials_unique (x x': X) (a: initial x) (b: initial x'): iso_arrows (` (a x')) (` (b x)).
    Proof.
     split.
      destruct (b x') as [? e1]. rewrite <- e1. apply e1.
     destruct (a x) as [? e0]. rewrite <- e0. apply e0.
    Qed.

  End initiality.

  Section products.

    Context {I: Type} (component: I -> X).

    Record Product: Type := mkProduct
      { product_object:> X
      ; project: forall i, product_object --> component i
      ; factor: forall (c: X) (ccomp: forall i, c --> component i), c --> product_object }.

    Definition is_product (candidate: X) (proj: forall i, candidate --> component i)
      (h: forall (c: X) (ccomp: forall i, c --> component i), c --> candidate): Prop
        := forall c ccomp, is_sole (fun h' => forall i, ccomp i == comp (proj i) h') (h c ccomp).

    Definition is_product' (p: Product): Prop
        := forall c ccomp, is_sole (fun h' => forall i, ccomp i == comp (project p i) h') (factor p c ccomp).

(*    Class IsProduct (p: Product) := is_p: is_product p. *)
(*
    Record Product: Type := product
      { product_object:> X
      ; project: forall i, A product_object (component i)
      ; factor: forall (c: X) (ccomp: forall i, A c (component i)), A c product_object
      ; correct: is_product product_object project factor
      }.
*)
(*
    Existing Class Product.
*)
    Lemma help_products_unique (d: X) (proj: forall i, d --> component i) h:
      is_product d proj h ->
      is_sole (fun a: d --> d => forall i, proj i == comp (proj i) a) cat_id.
    Proof with intuition.
     intros.
     split.
      intros.
      symmetry.
      apply id_r.
     intros.
     destruct (H1 d proj).
     clear H1.
     rewrite (H4 y)...
     rewrite (H4 cat_id)...
     intros.
     symmetry.
     apply id_r.
    Qed.

    Lemma products_unique (c c': X) (proj: forall i, c --> component i) (proj': forall i, c' --> component i)
      h h':
      is_product _ proj h -> is_product _ proj' h' -> iso_arrows (h c' proj') (h' c proj).
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

  Class Producer: Type := produce: forall `(c: Index -> X), Product c.

  Definition binary_product `{Producer} (x y: X): Product (fun b: bool => if b then x else y) := produce _.
  Definition empty_product `{Producer}: Product (fun f: False => match f with end) := produce _.

  Class Produces `{Producer}: Prop :=
    produces: forall `(c: Index -> X), is_product' _ (produce c).

  Section freedom.

    Context `{Category B} (forget_obj: X -> B) `{!Functor forget_obj forget_arr} (S: B).

    Section candidate.

      Context (x: X) (inject: S --> forget_obj x).

      Definition proves_free (d: forall (y: X), (S --> forget_obj y) -> (x --> y)): Prop :=
        forall (y: X) (f: S --> forget_obj y),
         is_sole (fun b => comp (fmap forget_obj b) inject == f) (d y f).

      Definition free: Prop := ex proves_free.

    End candidate.

    Lemma frees_unique (x y: X) (f: S --> forget_obj x) (g: S --> forget_obj y)
      (d: forall (y: X), (S --> forget_obj y) -> (x --> y))
      (e: forall (z: X), (S --> forget_obj z) -> (y --> z)):
       proves_free x f d -> proves_free y g e ->
       iso_arrows (d y g) (e x f).
    Proof with auto.
     intros P Q. split.
      destruct (Q y g) as [? R].
      rewrite (R cat_id)...
       apply (R (comp (d y g) (e x f))).
       intros.
       rewrite preserves_comp.
       rewrite <- comp_assoc.
       destruct (Q x f) as [V _].
       rewrite V.
       destruct (P y g)...
       apply _.
      intros. rewrite preserves_id. apply id_l. apply _.
     destruct (P x f) as [? R].
     rewrite (R cat_id)...
      apply (R (comp (e x f) (d y g))).
      intros.
      rewrite preserves_comp.
      rewrite <- comp_assoc.
      destruct (P y g) as [V _].
      rewrite V.
      destruct (Q x f)...
      apply _.
     intros. rewrite preserves_id. apply id_l. apply _.
    Qed. (* todo: get rid of all those [apply _]'s *)

  End freedom.

End contents.

Implicit Arguments Producer [].
Implicit Arguments Produces [[Arrows0] [H] [CatComp0] [H1]]. (* todo: rename args *)
