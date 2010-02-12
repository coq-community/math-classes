Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra.

Section functor_class.

  Context `{Category X A} `{Category X' A'}.

  Record FunctorOps :=
    { functor_object:> X -> X'
    ; functor_arrow:> forall v w, A v w  -> A' (functor_object v) (functor_object w) }.

  Class Functor (map_obj: X -> X') (map_arr: forall v w, A v w  -> A' (map_obj v) (map_obj w)): Prop :=
    { functor_morphism:> forall a b, Setoid_Morphism (map_arr a b)
    ; preserves_id: forall a, @map_arr a a cat_id == cat_id
    ; preserves_comp: forall x y z (f: A y z) (g: A x y),
        map_arr _ _ (comp f g) == comp (map_arr _ _ f) (map_arr _ _ g)
    }.

  Class ForgetOps :=
    { forget_object: X -> X'
    ; forget_arrow: forall v w, A v w  -> A' (forget_object v) (forget_object w) }.

  Class ForgetFunctor `{ForgetOps}: Prop := forget_functor:> Functor forget_object forget_arrow. 

  (* Forget(/Ops) is currently just there for canonical names. At some point we may want
   a real specification of what it means to be forgetful. *)

End functor_class.

Inductive CatStructure: Type := { cat_object:> Type; cat_arrow:> cat_object -> cat_object -> Type }.

Section adjunction.

  Local Notation Functor F := (Functor F (functor_arrow F)).

  Context
   {A: CatStructure} `{Category A A}
   {X: CatStructure} `{Category X X}
   (F: @FunctorOps X X A A) (G: @FunctorOps A A X X)
   `{Functor F} `{Functor G}
   (φ: forall {x a}, A (F x) a -> X x (G a))
   `{forall x a, Bijective (φ x a)}.

  Implicit Arguments φ [[x] [a]].
  Implicit Arguments functor_arrow [X A X' A' [v] [w]].

  Class Adjunction: Prop :=
   { natural_left: forall x a a' (k: A a a'),
       pointwise_relation _ equiv (comp (functor_arrow G k) ∘ φ) (@φ x a' ∘ comp k)
   ; natural_right: forall x x' a (h: X x' x),
       pointwise_relation _ equiv (flip comp h ∘ @φ x a) (φ ∘ flip comp (functor_arrow F h))
   }.

End adjunction.

Instance id_functor: forall `{Category X A}, @Functor X A _ _ _ X A _ _ _ id (fun _ _ => id).
Proof.
 intros.
 pose proof arrow_equiv.
 unfold id.
 constructor; try reflexivity.
 intros.
 apply id_setoid_morphism.
 apply _.
Qed.

Instance compose_functors
  `{Functor Ao Aa Ae Aid Acomp Bo Ba Be Bid Bcomp AB_obj AB_arrow}
  `{Functor Bo Ba _ _ _ Co Ca Ce Cid Ccomp BC_obj BC_arrow}:
    @Functor Ao Aa _ _ _ Co Ca _ _ _
      (BC_obj ∘ AB_obj) (fun _ _ => BC_arrow _ _ ∘ AB_arrow _ _).
Proof.
   constructor.
     intros.
     set (BC_arrow (AB_obj a) (AB_obj b)).
     set (AB_arrow a b).
     apply (@compose_setoid_morphisms _ _ _ _ _ _).
      apply _.
     subst c.
     destruct H0.
     apply functor_morphism0.
    unfold Basics.compose.
    intros.
    destruct H, H0.
    destruct (functor_morphism1 (AB_obj a) (AB_obj a)).
    destruct (functor_morphism0 a a).
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
   rewrite preserves_comp0.
   rewrite preserves_comp1.
   reflexivity.
  Qed. (* todo: clean up. those destructs should not be needed *)


Definition is_sole `{Equiv T} (P: T -> Prop) (x: T): Prop :=
  P x /\ forall y, P y -> y == x. (* todo: move *)

Section contents.

  Context `{Category X A}.

  Class Mono {x y} (a: A x y): Prop :=
    mono: forall z (f g: A z x), comp a f == comp a g -> f == g.

  Section isomorphy.

    Definition iso_arrows {x y: X} (a: A x y) (b: A y x): Prop
      := comp a b == cat_id /\ comp b a == cat_id. (* todo: product *)

    Global Instance: HeteroSymmetric (@iso_arrows).
    Proof. unfold iso_arrows. repeat intro. intuition. Qed.

    Definition is_iso {x y: X} (a: A x y): Prop := ex (iso_arrows a).

    Definition isos_unique (x y: X) (a: A x y) (b b': A y x): iso_arrows a b -> iso_arrows a b' -> b == b'.
    Proof. intros [P Q] [R S]. rewrite <- id_l. rewrite <- S, <- comp_assoc, P. apply id_r. Qed.

    Definition iso: Equiv X := fun x y => ex (fun p: A x y * A y x => iso_arrows (fst p) (snd p)).

    Instance: Reflexive iso.
    Proof. repeat intro. exists (@cat_id _ _ _ x, @cat_id _ _ _ x). split; apply id_l. Qed.

    Instance: Symmetric iso.
    Proof. intros ? ? [[f f'] ?]. exists (f', f). apply (hetero_symmetric). assumption. Qed.

    Instance: Transitive iso.
    Proof with assumption.
     intros ? ? ? [[f f'] [U V]] [[g g'] [W Z]].
     exists (comp g f, comp f' g').
     split; simpl.
      rewrite <- comp_assoc, (comp_assoc g' f' f), U, id_l...
     rewrite <- comp_assoc, (comp_assoc f g g'), Z, id_l...
    Qed.

    Global Instance iso_equivalence: Equivalence iso.

    Lemma arrows_between_isomorphic_objects (a b c d: X)
      (ab: A a b) (ba: A b a)  (cd: A c d) (dc: A d c) (ac: A a c) (bd: A b d):
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

    Program Definition refl_arrows (x: X) : {p : A x x * A x x | iso_arrows (fst p) (snd p)}
      := (@cat_id _ _ _ x, @cat_id _ _ _ x).
    Next Obligation. split; apply id_l. Qed.

  End isomorphy.

  Section initiality.

    Definition proves_initial {x: X} (f: forall y: X, A x y): Prop := forall y f', f y == f'.

    Definition initial (x: X): Type := forall y: X, sig (fun a: A x y => forall a': A x y, a == a').

    Lemma initials_unique' (x x': X) (a: forall y, A x y) (b: forall y, A x' y):
      proves_initial a -> proves_initial b -> iso_arrows (a x') (b x).
    Proof with reflexivity.
     intros H1 H2. split.
      rewrite <- (H2 x' cat_id). rewrite <- H2...
     rewrite <- (H1 x cat_id). rewrite <- H1...
    Qed.

    Lemma initials_unique (x x': X) (a: initial x) (b: initial x'): iso_arrows (proj1_sig (a x')) (proj1_sig (b x)).
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
      ; project: forall i, A product_object (component i)
      ; factor: forall (c: X) (ccomp: forall i, A c (component i)), A c product_object }.

    Definition is_product (candidate: X) (proj: forall i, A candidate (component i))
      (h: forall (c: X) (ccomp: forall i, A c (component i)), A c candidate): Prop
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
    Lemma help_products_unique (d: X) (proj: forall i, A d (component i)) h:
      is_product d proj h ->
      is_sole (fun a: A d d => forall i, proj i == comp (proj i) a) cat_id.
    Proof.
     intros.
     split.
      intros.
      symmetry.
      apply id_r.
     intros.
     destruct (H1 d proj).
     clear H1.
     rewrite (H4 y).
      rewrite (H4 cat_id).
       reflexivity.
      intros.
      symmetry.
      apply id_r.
     assumption.
    Qed.

    Lemma products_unique (c c': X) (proj: forall i, A c (component i)) (proj': forall i, A c' (component i))
      h h':
      is_product _ proj h -> is_product _ proj' h' -> iso_arrows (h c' proj') (h' c proj).
    Proof.
     intro.
     intros.
     split.
      destruct (help_products_unique c proj h H1).
      apply H4.
      intro.
      rewrite comp_assoc.
      destruct (H1 c' proj').
      destruct (H2 c proj).
      rewrite <- H5.
      auto.
     destruct (help_products_unique c' proj' h' H2).
     apply H4.
     intro.
     rewrite comp_assoc.
     destruct (H1 c' proj').
     destruct (H2 c proj).
     rewrite <- H7.
     auto.
    Qed.

  End products.

  Class Producer: Type := produce: forall `(c: Index -> X), Product c.

  Definition binary_product `{Producer} (x y: X): Product (fun b: bool => if b then x else y) := produce _.
  Definition empty_product `{Producer}: Product (fun f: False => match f with end) := produce _.

  Class Produces `{Producer}: Prop :=
    produces: forall `(c: Index -> X), is_product' _ (produce c).

  Section freedom.

    Context `{Category B BA} (forget_obj: X->B)
     (forget_arr: forall x y, A x y -> BA (forget_obj x) (forget_obj y))
     `{!Functor forget_obj forget_arr} (S: B).

    Section candidate.

      Context (x: X) (inject: BA S (forget_obj x)).

      Definition proves_free (d: forall (y: X), BA S (forget_obj y) -> A x y): Prop :=
        forall (y: X) (f: BA S (forget_obj y)),
         is_sole (fun b => comp (forget_arr _ _ b) inject == f) (d y f).

      Definition free: Prop := ex proves_free.

    End candidate.

    Lemma frees_unique (x y: X) (f: BA S (forget_obj x)) (g: BA S (forget_obj y))
      (d: forall (y: X), (BA S (forget_obj y)) -> A x y)
      (e: forall (z: X), (BA S (forget_obj z)) -> A y z):
       proves_free x f d -> proves_free y g e ->
       iso_arrows (d y g) (e x f).
    Proof with auto.
     intros P Q. split.
      destruct (Q y g) as [? R].
      rewrite (R cat_id)...
       apply (R (comp (d y g) (e1 x f))).
       intros.
       rewrite preserves_comp.
       rewrite <- comp_assoc.
       destruct (Q x f) as [V _].
       rewrite V.
       destruct (P y g)...
      intros. rewrite preserves_id. apply id_l.
     destruct (P x f) as [? R].
     rewrite (R cat_id)...
      apply (R (comp (e1 x f) (d y g))).
      intros.
      rewrite preserves_comp.
      rewrite <- comp_assoc.
      destruct (P y g) as [V _].
      rewrite V.
      destruct (Q x f)...
     intros. rewrite preserves_id. apply id_l.
    Qed.

  End freedom.

End contents.

Implicit Arguments Producer [].

Implicit Arguments Produces [[e] [cc] [H1]]. (* todo: rename args *)
