Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Record Object := object
  { obj:> Type
  ; Arrows_inst: Arrows obj
  ; Equiv_inst: forall x y: obj, Equiv (x --> y)
  ; CatId_inst: CatId obj
  ; CatComp_inst: CatComp obj
  ; Category_inst: Category obj }.

Implicit Arguments object [[Arrows_inst] [Equiv_inst] [CatId_inst] [CatComp_inst] [Category_inst]].
Existing Instance Arrows_inst.
Existing Instance Equiv_inst.
Existing Instance CatId_inst.
Existing Instance CatComp_inst.
Existing Instance Category_inst.
    (* Todo: Ask mattam for [Existing Instance foo bar bas.] *)

(* The above would be much more elegantly written as

  Inductive Object := object (obj: Type) `{Category obj}.

Unfortunately, that doesn't register the coercion and class instances. *)

Record Arrow (x y: Object): Type := arrow
  { map_obj:> obj x -> obj y
  ; Fmap_inst: Fmap map_obj
  ; Functor_inst: Functor map_obj _ }.

Implicit Arguments arrow [[x] [y]].
Existing Instance Fmap_inst.
Existing Instance Functor_inst.

Hint Extern 4 (Arrows Object) => exact Arrow : typeclass_instances.
  (* Matthieu is adding [Existing Instance (c: T).], which is nicer. *)

Section contents.

  Instance hint (x y: Object) (a: x --> y) p q: Setoid_Morphism (fmap a: p --> q -> _).

  Implicit Arguments map_obj [[x] [y]].

  Section more_arrows. Context (x y: Object).

    Global Program Instance e: Equiv (x --> y) := fun a b =>
      exists X: forall _, isoT _ _, forall (p q: x) (r r': p --> q), r == r' ->
       comp (fmap a r) (snd (X p)) == comp (snd (X q)) (fmap b r').

    Let e_refl: Reflexive e.
    Proof.
     intro a.
     exists (fun v => refl_arrows (a v)).
     intros ???? E. simpl.
     rewrite E, id_l, id_r. reflexivity.
    Qed.

    Program Let sym_arrows (a b: x -> y) (v: x) (p: isoT (a v) (b v)): isoT (b v) (a v)
        := (snd p, fst p).

    Next Obligation. destruct p. simpl in *. firstorder. Qed.

    Let e_sym: Symmetric e.
    Proof.
     intros ?? [x1 H].
     exists (fun v => sym_arrows _ _ _ (x1 v)). simpl.
     intros ???? E.
     pose proof (H _ _ _ _ E) as H0.
     destruct (x1 p), (x1 q). simpl in *.
     rewrite E in H0 |- *.
     apply (arrows_between_isomorphic_objects _  _ _ _ _ _ _ _ _ _ u u0).
     assumption.
    Qed. (* todo: clean up *)

    Program Let trans_arrows (x0 y0 z: x -> y) (v: x)
     (x1: sig (fun (p: (x0 v --> y0 v) * _) => uncurry iso_arrows p))
     (x2: sig (fun (p: (y0 v --> z v) * _) => uncurry iso_arrows p)): (* todo: use isoT *)
      isoT (x0 v) (z v)  := (comp (fst x2) (fst x1), comp (snd x1) (snd x2)).

    Next Obligation. Proof with assumption.
     destruct H as [? H1], H0 as [? H2]. unfold uncurry. simpl in *.
     split. rewrite <- comp_assoc, (comp_assoc a0 a2 a1), H0, id_l...
     rewrite <- comp_assoc, (comp_assoc a1 a a0), H1, id_l...
    Qed.

    Let e_trans: Transitive e.
    Proof.
     intros ? ? z [f H] [g H0].
     exists (fun v => trans_arrows _ _ _ _ (f v) (g v)).
     simpl. intros ? ? ? ? U.
     generalize (H _ _ _ _ U), (H0 _ _ _ _ U).
     rewrite U. intros E E'.
     rewrite comp_assoc, E, <- comp_assoc, E', comp_assoc.
     reflexivity.
    Qed.

    Instance: Equivalence e.
    Global Instance: Setoid (x --> y).

  End more_arrows.

  Let obj_iso (x: Object): Equiv x := @iso x _ _ _ _.

  Global Instance: forall (x y: Object) (a: x --> y), Setoid_Morphism (map_obj a).
  Proof.
   constructor; try apply _.
   intros v w [[f g] [E F]].
   exists (fmap a f, fmap a g).
   unfold uncurry.
   destruct a. simpl in *. destruct Functor_inst0. (* this [destruct] shouldn't be needed *)
   split. rewrite <- preserves_comp. rewrite E. auto.
   rewrite <- preserves_comp. rewrite F. auto.
  Qed. (* Putting this in the "arrows" section above (where it belongs) triggers a Coq bug. *)

  Global Instance: CatId Object := fun _ => arrow id (fun _ _ => id) _.

  Global Program Instance: CatComp Object
    := fun x y z X X0 => arrow (compose X X0)
     (fun _ _ => compose (@Fmap_inst _ _ X _ _) (@Fmap_inst _ _ X0 _ _)) _.
       (* With the intermediate Arrow constant out of the way we should
        just be able to say "fmap X" and "fmap X0" here. *)

  Next Obligation.
   destruct x, y, z, X, X0. simpl.
   apply (compose_functors (BC_obj := map_obj0)). (* todo: why do we need this? *)
  Qed.

  Program Let proper_arrows (x y z: Object) (x0 y0: y --> z) (x1 y1: x --> y)
    (f: forall v, @isoT _ _ _ _ _ (map_obj x0 v) (map_obj y0 v))
    (g: forall v, @isoT _ _ _ _ _ (map_obj x1 v) (map_obj y1 v)) (v: x):
      @isoT _ _ _ _ _ (map_obj x0 (map_obj x1 v)) (map_obj y0 (map_obj y1 v))
   := (comp (fst (f (y1 v))) (fmap x0 (fst (g v))), comp (fmap x0 (snd (g v))) (snd (f (y1 v)))).
     (* Todo: Investigate why things go wrong without the underscores. *)

  Next Obligation. Proof with try apply _; intuition.
   destruct (f (y1 v)) as [? [e0 e1]].
   destruct (g v) as [? [e2 e3]].
   split; simpl in *.
    rewrite <- comp_assoc.
    rewrite (comp_assoc _ (fmap x0 _) (fmap x0 _)).
    rewrite <- preserves_comp, e2, preserves_id, id_l...
   rewrite <- comp_assoc.
   rewrite (comp_assoc (fmap x0 _) _ _).
   rewrite e1, id_l, <- preserves_comp, e3, preserves_id...
  Defined.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv) (comp: y --> z -> x --> y -> x --> z).
  Proof.
   repeat intro.
   unfold equiv.
   unfold e.
   destruct H.
   destruct H0.
   simpl in *.
   exists (proper_arrows x y z x0 y0 x1 y1 x2 x3).
   unfold compose.
   intros.
   simpl.
   pose proof (H0 _ _ _ _ H1). clear H0.
   revert H2.
   destruct (x3 p), (x3 q).
   simpl.
   clear x3.
   destruct x4, x5.
   destruct u, u0.
   simpl in *.
   unfold fmap.
   rewrite H1. clear r H1.
   intros.
   pose proof (H (y1 p) (y1 q) (Fmap_inst _ _ y1 _ _ r') (Fmap_inst _ _ y1 _ _ r') (reflexivity _)). clear H.
   destruct (x2 (y1 p)), (x2 (y1 q)).
   clear x2.
   destruct x3, x4, u, u0.
   simpl in *.
   destruct z.
   destruct Category_inst0.
   simpl in *.
   apply transitivity with (comp (fmap x0 a2) (comp a6 (fmap y0 (fmap y1 r')))).
    rewrite <- H5. clear H5.
    apply transitivity with (comp (comp (fmap x0 (fmap x1 r')) (fmap x0 a0)) a4).
     repeat rewrite comp_assoc. reflexivity.
    simpl in *.
    rewrite <- preserves_comp.
     Focus 2.
     clear.
     destruct x0.
     simpl.
     apply _.
    unfold fmap.
    rewrite H1.
    rewrite comp_assoc.
    change (comp (fmap x0 (comp a2 (fmap y1 r'))) a4 ==
      comp (comp (fmap x0 a2) (fmap x0 (fmap y1 r'))) a4).
    rewrite <- preserves_comp.
     reflexivity.
    destruct x0. apply _.
   repeat rewrite comp_assoc. reflexivity.
  Qed. (* todo: clean up! *)
 
  Program Let id_lr_arrows (x y: Object) (a: y --> x) v: isoT (map_obj a v) (map_obj a v)
    := (cat_id, cat_id).
    (* We can't remove the map_obj here and elsewhere even though it's a coercion,
     because unification isn't smart enough to resolve and use that coercion. This is
     likely due to Coq bug #2229. *)

  Next Obligation. split; apply id_l. Qed.

  Let id_l' (x y: Object) (a: y --> x): comp cat_id a == a.
  Proof.
   exists (id_lr_arrows _ _ a).
   intros ? ? ? ? E. simpl. unfold compose, id.
   rewrite id_r, id_l, <- E. reflexivity.
  Qed.

  Let id_r' (x y: Object) (a: x --> y): comp a cat_id == a.
  Proof.
   exists (id_lr_arrows _ _ a).
   intros ? ? ? ? E. simpl. unfold compose, id.
   rewrite id_r, id_l, <- E. reflexivity.
  Qed.

  Section comp_assoc.

    Variables (w x y z: Object) (a: w --> x) (b: x --> y) (c: y --> z).

    Program Let comp_assoc_arrows (v: w): isoT (c (b (a v))) (c (b (a v))) :=
      (fmap c (fmap b (fmap a cat_id)), fmap c (fmap b (fmap a cat_id))).
    Next Obligation. unfold uncurry. simpl. split; repeat rewrite preserves_id; try apply _; apply id_l. Qed.

    Lemma comp_assoc': comp c (comp b a) == comp (comp c b) a.
    Proof.
     exists comp_assoc_arrows.
     simpl. intros ? ? ? ? E. unfold compose.
     repeat rewrite preserves_id; try apply _. (* todo: remove need for [try apply _] *)
     rewrite id_l, id_r.
     unfold fmap. (* todo: shouldn't be necessary *)
     rewrite E. reflexivity.
    Qed.

  End comp_assoc.

  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r' } .

End contents.
