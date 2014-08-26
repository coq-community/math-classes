Require Import
  abstract_algebra interfaces.functors theory.categories.

Record Object := object
  { obj:> Type
  ; Arrows_inst: Arrows obj
  ; Equiv_inst: ∀ x y: obj, Equiv (x ⟶ y)
  ; CatId_inst: CatId obj
  ; CatComp_inst: CatComp obj
  ; Category_inst: Category obj }.

Arguments object _ {Arrows_inst Equiv_inst CatId_inst CatComp_inst Category_inst}.
Existing Instance Arrows_inst.
Hint Extern 0 (Equiv (_ ⟶ _)) => eapply @Equiv_inst : typeclass_instances.
Existing Instance CatId_inst.
Existing Instance CatComp_inst.
Existing Instance Category_inst.
    (* Todo: Ask mattam for [Existing Instance foo bar bas.] *)

(* The above would be much more elegantly written as

  Inductive Object := object (obj: Type) `{Category obj}.

Unfortunately, that doesn't register the coercion and class instances. *)

Record Arrow (x y: Object): Type := arrow
  { map_obj:> obj x → obj y
  ; Fmap_inst: Fmap map_obj
  ; Functor_inst: Functor map_obj _ }.

Arguments arrow {x y} _ {Fmap_inst Functor_inst}.
Arguments map_obj {x y} _ _.
Existing Instance Fmap_inst.
Existing Instance Functor_inst.

Instance: Arrows Object := Arrow.
(* Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances. *)
  (* Matthieu is adding [Existing Instance (c: T).], which is nicer. *)

Section contents.
  Section more_arrows.
    Context (x y: Object).

    Global Program Instance e: Equiv (x ⟶ y) := λ a b,
      exists X: ∀ v, isoT _ _, ∀ (p q: x) (r: p ⟶ q),
       fmap a r ◎ snd (X p) = snd (X q) ◎ fmap b r.

    Let e_refl: Reflexive e.
    Proof.
     intro a.
     exists (λ v, refl_arrows (a v)).
     intros ???. simpl.
     rewrite left_identity, right_identity. reflexivity.
    Qed.

    Program Let sym_arrows (a b: x → y) (v: x) (p: isoT (a v) (b v)): isoT (b v) (a v)
        := (snd p, fst p).
    Next Obligation. destruct p. simpl in *. firstorder. Qed.

    Let e_sym: Symmetric e.
    Proof.
     intros ?? [x1 H].
     exists (λ v, sym_arrows _ _ _ (x1 v)). simpl.
     intros ???.
     pose proof (H p q r).
     destruct (x1 p), (x1 q). simpl in *.
     apply (arrows_between_isomorphic_objects _  _ _ _ _ _ _ _ _ _ u u0).
     assumption.
    Qed. (* todo: clean up *)

    Program Let trans_arrows (x0 y0 z: x → y) (v: x)
     (x1: sig (λ (p: (x0 v ⟶ y0 v) * _), uncurry iso_arrows p))
     (x2: sig (λ (p: (y0 v ⟶ z v) * _), uncurry iso_arrows p)): (* todo: use isoT *)
      isoT (x0 v) (z v) := (fst x2 ◎ fst x1, snd x1 ◎ snd x2).
    Next Obligation. Proof with assumption.
     destruct H as [? H1], H0 as [? H2]. unfold uncurry. simpl in *.
     split. rewrite <- associativity, (associativity a1 a2 a0), H0, left_identity...
     rewrite <- associativity, (associativity a0 a a1), H1, left_identity...
    Qed.

    Let e_trans: Transitive e.
    Proof.
     intros a b c [f H] [g H0].
     exists (λ v, trans_arrows _ _ _ _ (f v) (g v)).
     simpl. intros ? ? ?.
     generalize (H p q r), (H0 p q r).
     clear H H0. intros E E'.
     rewrite associativity, E, <- associativity, E', associativity.
     reflexivity.
    Qed.

    Global Instance: Setoid (x ⟶ y).
    Proof. split; assumption. Qed.
  End more_arrows.

  Instance obj_iso (x: Object): Equiv x := @iso x _ _ _ _.

  Typeclasses Transparent Arrows.
  Global Instance: ∀ (x y: Object) (a: x ⟶ y), Setoid_Morphism (map_obj a).
  Proof with try apply _.
   constructor...
   intros v w [[f g] [E F]].
   exists (fmap a f, fmap a g).
   unfold uncurry. destruct a. simpl in *.
   split; rewrite <- preserves_comp...
    rewrite E. apply preserves_id...
   rewrite F. apply preserves_id...
  Qed. (* Putting this in the "arrows" section above (where it belongs) triggers a Coq bug. *)

  Global Instance: CatId Object := λ _, arrow id.

  Global Program Instance: CatComp Object := λ _ _ _ x y, arrow (x ∘ y).

  Program Let proper_arrows (x y z: Object) (x0 y0: y ⟶ z) (x1 y1: x ⟶ y)
    (f: ∀ v, isoT (map_obj x0 v) (map_obj y0 v))
    (g: ∀ v, isoT (map_obj x1 v) (map_obj y1 v)) (v: x):
      isoT (map_obj x0 (map_obj x1 v)) (map_obj y0 (map_obj y1 v))
   := (fst (f (y1 v)) ◎ fmap x0 (fst (g v)), fmap x0 (snd (g v)) ◎ snd (f (y1 v))).
     (* Todo: Investigate why things go wrong without the underscores. *)
  Next Obligation. Proof with try apply _; intuition.
   destruct (f (y1 v)) as [? [e0 e1]].
   destruct (g v) as [? [e2 e3]].
   split; simpl in *.
    rewrite <- associativity.
    rewrite (associativity (fmap x0 _) (fmap x0 _) _).
    rewrite <- preserves_comp, e2, preserves_id, left_identity...
   rewrite <- associativity.
   rewrite (associativity _ _ (fmap x0 _)).
   rewrite e1, left_identity, <- preserves_comp, e3, preserves_id...
  Qed.

  Global Instance: ∀ x y z: Object, Proper ((=) ==> (=) ==> (=)) ((◎): (y ⟶ z) → (x ⟶ y) → (x ⟶ z)).
  Proof with try apply _.
   repeat intro.
   unfold e.
   destruct H.
   destruct H0.
   simpl in *.
   exists (proper_arrows x y z x0 y0 x1 y1 x2 x3).
   intros.
   simpl.
   pose proof (H0 p q r). clear H0.
   destruct (x3 p) as [[a a0] [e0 e1]], (x3 q) as [[a1 a2] [e2 e3]]. clear x3.
   simpl in *.
   change (
     fmap x0 (fmap x1 r) ◎ (fmap x0 a0 ◎ snd (` (x2 (y1 p)))) =
     fmap x0 a2 ◎ snd (` (x2 (y1 q))) ◎ fmap y0 (fmap y1 r)).
   pose proof (H (y1 p) (y1 q) (fmap y1 r)). clear H.
   destruct (x2 (y1 p)) as [[a3 a4] [e4 e5]], (x2 (y1 q)) as [[a5 a6] [e6 e7]]. clear x2.
   simpl in *.
   rewrite <- associativity, <- H0. clear H0.
   eapply (transitivity (y:=((fmap x0 (fmap x1 r) ◎ fmap x0 a0) ◎ a4))).
    repeat rewrite associativity. reflexivity.
   rewrite <- preserves_comp...
   rewrite H1.
   rewrite associativity.
   rewrite <- preserves_comp...
   reflexivity.
  Qed. (* todo: clean up! *)

  Program Let id_lr_arrows (x y: Object) (a: y ⟶ x) v: isoT (map_obj a v) (map_obj a v)
    := (cat_id, cat_id).
    (* We can't remove the map_obj here and elsewhere even though it's a coercion,
     because unification isn't smart enough to resolve and use that coercion. This is
     likely due to Coq bug #2229. *)
  Next Obligation. split; apply left_identity. Qed.

  Instance: ∀ x y: Object, LeftIdentity (comp x _ y) cat_id.
  Proof.
   intros ?? a.
   exists (id_lr_arrows _ _ a).
   intros ? ? ?. simpl. unfold compose, id.
   rewrite right_identity, left_identity. reflexivity.
  Qed.

  Instance: ∀ x y: Object, RightIdentity (comp x _ y) cat_id.
  Proof.
   intros ?? a.
   exists (id_lr_arrows _ _ a).
   intros ? ? ?. simpl. unfold compose, id.
   rewrite right_identity, left_identity. reflexivity.
  Qed.

  Section associativity.
    Variables (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).

    Program Definition associativity_arrows (v: w): isoT (c (b (a v))) (c (b (a v))) :=
      (fmap c (fmap b (fmap a cat_id)), fmap c (fmap b (fmap a cat_id))).
    Next Obligation. unfold uncurry. simpl. split; repeat rewrite preserves_id; try apply _; apply left_identity. Qed.
  End associativity.

  Instance: ArrowsAssociative Object.
    Proof.
     repeat intro.
     exists (associativity_arrows _ _ _ _ z0 y0 x0).
     simpl. intros ? ? ?. unfold compose.
     rewrite ! preserves_id; try apply _. (* todo: remove need for [try apply _] *)
     rewrite left_identity, right_identity. reflexivity.
    Qed.

  Global Instance: Category Object := {}.
End contents.
