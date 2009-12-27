Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Record Object :=
  { obj: Type
  ; arr: obj -> obj -> Type
  ; arr_e: forall x y, Equiv (arr x y)
  ; id_inst: CatId obj arr
  ; comp_inst: CatComp obj arr
  ; cat_inst: Category obj arr }.

Definition object_from_instance X A `{Category X A}: Object := {| obj := X |}.

Implicit Arguments arr_e [[x] [y]].

Existing Instance arr_e.
Existing Instance id_inst.
Existing Instance comp_inst.
Existing Instance cat_inst.

Section contents. (* Delayed because there's no [Existing Global Instance]. Todo: Ask mattam why there isn't. *)

  Let obj_iso (x: Object): Equiv (obj x) := @iso (obj x) (arr x) _ _ _.

  Section arrows. Context (x y: Object).

    Record Arrow: Type :=
      { map_obj:> obj x -> obj y
      ; map_arr: forall v w, arr x v w -> arr y (map_obj v) (map_obj w)
      ; functor_inst: Functor map_obj map_arr
      ; map_arr_mor: forall a b, Setoid_Morphism (map_arr a b) := _ (* "hint" *)
      }.

    Global Instance e: Equiv Arrow := fun a b =>
      exists X: forall v, sig (fun p: arr y (a v) (b v) * arr y (b v) (a v) => iso_arrows (fst p) (snd p)),
       forall (p q: obj x) (r r': arr x p q), r == r' -> 
        comp (map_arr a _ _ r) (snd (proj1_sig (X p))) ==
        comp (snd (proj1_sig (X q))) (map_arr b _ _ r').
        (* the other half follows automatically *)

    Existing Instance functor_inst.
    Existing Instance map_arr_mor.

    Let e_refl: Reflexive e.
    Proof.
     repeat intro.
     exists (fun v => refl_arrows (x0 v)).
     intros.
     simpl.
     rewrite H.
     apply transitivity with (map_arr x0 p q r'). (* can't use [transitivity] tactic here, looks like a bug. todo: isolate *)
      apply id_r.
     symmetry. apply id_l.
    Qed.

    Program Let sym_arrows x0 y0 (v: obj x) (p:
      {p : arr y (x0 v) (y0 v) * arr y (y0 v) (x0 v) | iso_arrows (fst p) (snd p)}):
      {p : arr y (y0 v) (x0 v) * arr y (x0 v) (y0 v) | iso_arrows (fst p) (snd p)}
        := (snd p, fst p).

    Next Obligation. firstorder. Qed.

    Let e_sym: Symmetric e.
    Proof.
     repeat intro.
     destruct H.
     exists (fun v: obj x => sym_arrows _ _ _ (x1 v)).
     simpl.
     intros.
     pose proof (H p q r r' H0).
     clear H.
     destruct (x1 p), (x1 q).
     destruct x2, x3. simpl in *. clear x1.
     revert H1.
     rewrite H0.
     generalize (map_arr x0 _ _ r') (map_arr y0 _ _ r').
     intros.
     apply (arrows_between_isomorphic_objects _  _ _ _ _ _ _ _ _ _ i i0).
     assumption.
    Qed. (* todo: clean up *)

    Program Let trans_arrows x0 y0 z (v: obj x)
     (x1: {p : arr y (x0 v) (y0 v) * arr y (y0 v) (x0 v) | iso_arrows (fst p) (snd p)})
     (x2: {p : arr y (y0 v) (z v) * arr y (z v) (y0 v) | iso_arrows (fst p) (snd p)}):
      {p : arr y (x0 v) (z v) * arr y (z v) (x0 v) | iso_arrows (fst p) (snd p)}
        := (comp (fst x2) (fst x1), comp (snd x1) (snd x2)).
    Next Obligation. Proof with assumption.
     destruct H as [? H1], H0 as [? H2]. simpl in *.
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

    Global Instance: Equivalence e.

  End arrows.

  Existing Instance functor_inst.
  Existing Instance map_arr_mor.

  Implicit Arguments map_arr [[x] [y] [v] [w]].
  Implicit Arguments map_obj [[x] [y]].

  Global Instance: forall (a: Arrow x y), Setoid_Morphism (map_obj a).
  Proof.
   constructor; try apply _.
   intros v w [[f g] [E F]].
   exists (map_arr a f, map_arr a g).
   simpl in *.
   destruct a. destruct functor_inst0. simpl.
   split. rewrite <- preserves_comp. rewrite E. auto.
   rewrite <- preserves_comp. rewrite F. auto.
  Qed. (* Putting this in the "arrows" section above (where it belongs) triggers a Coq bug. *)
    (* Todo: clean up. *)

  Global Instance id': CatId Object Arrow := fun _ => Build_Arrow _ _ id (fun _ _ => id) _.

  Global Program Instance comp': CatComp Object Arrow
    := fun x y z X X0 => Build_Arrow x z (compose X X0) (fun _ _ => compose (map_arr X) (map_arr X0)) _.

  Next Obligation.
   constructor; repeat intro.
     apply (@compose_setoid_morphisms (arr x a b) (arr y (X0 a) (X0 b)) (arr z (X (X0 a)) (X (X0 b))) _ _ _).
      apply _.
     apply (@functor_morphism _ _ _ _ _ _ _ _ _ _ _ _ (functor_inst _ _ X)).
    unfold compose. do 2 rewrite preserves_id. reflexivity. 
   unfold compose. do 2 rewrite preserves_comp. reflexivity.
  Qed. (* todo: this is still too verbose. look into it *)

  Program Let proper_arrows (x y z: Object) (x0 y0: Arrow y z) (x1 y1: Arrow x y)
    (f: forall v, {p : arr _ (x0 v) (y0 v) * arr _ (y0 v) (x0 v) | iso_arrows (fst p) (snd p)})
    (g: forall v, {p : arr _ (x1 v) (y1 v) * arr _ (y1 v) (x1 v) | iso_arrows (fst p) (snd p)}) (v: obj x):
      {p : arr z (x0 (x1 v)) (y0 (y1 v)) * arr z (y0 (y1 v)) (x0 (x1 v)) | iso_arrows (fst p) (snd p)}
   := (comp (fst (f (y1 v))) (map_arr x0 (fst (g v))), comp (map_arr x0 (snd (g v))) (snd (f (y1 v)))).

  Next Obligation. Proof.
   destruct (f (y1 v)) as [[a a0] [e0 e1]].
   destruct (g v) as [[a1 a2] [e2 e3]].
   split; simpl in *.
    rewrite <- comp_assoc.
    rewrite (comp_assoc a0 (map_arr x0 a2) (map_arr x0 a1)).
    rewrite <- preserves_comp, e2, preserves_id, id_l.
    assumption.
   rewrite <- comp_assoc.
   rewrite (comp_assoc (map_arr x0 a1) a a0).
   rewrite e1, id_l, <- preserves_comp, e3, preserves_id.
   reflexivity.
  Defined.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv) (comp' x y z).
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
   destruct i, i0.
   simpl in *.
   rewrite H1. clear r H1.
   intros.
   pose proof (H (y1 p) (y1 q) (map_arr y1 r') (map_arr y1 r') (reflexivity _)). clear H.
   destruct (x2 (y1 p)), (x2 (y1 q)).
   clear x2.
   destruct x3, x4, i, i0.
   simpl in *.
   destruct z.
   destruct cat_inst0.
   simpl in *.
   apply transitivity with (comp (map_arr x0 a2) (comp a6 (map_arr y0 (map_arr y1 r')))).
    rewrite <- H5. clear H5.
    apply transitivity with (comp (comp (map_arr x0 (map_arr x1 r')) (map_arr x0 a0)) a4).
     repeat rewrite comp_assoc. reflexivity.
    simpl in *.
    rewrite <- preserves_comp.
    rewrite H1.
    rewrite comp_assoc.
    rewrite <- preserves_comp.
    reflexivity.
   repeat rewrite comp_assoc. reflexivity.
  Qed. (* todo: clean up! *)
 
  Program Let id_lr_arrows x y (a: Arrow y x) (v: obj y):
    {p: arr x (a v) (a v) * arr x (a v) (a v) | iso_arrows (fst p) (snd p)}
      := (cat_id, cat_id).
  
  Next Obligation. split; apply id_l. Qed.

  Let id_l' x y (a: Arrow y x): comp cat_id a == a.
  Proof.
   exists (id_lr_arrows _ _ a).
   intros ? ? ? ? E. simpl. unfold compose, id. rewrite id_r, id_l, E. reflexivity.
  Qed.

  Let id_r' x y (a: Arrow x y): comp a cat_id == a.
  Proof.
   exists (id_lr_arrows _ _ a).
   intros ? ? ? ? E. simpl. unfold compose, id. rewrite id_r, id_l, E. reflexivity.
  Qed.

  Program Let comp_assoc_arrows (w x y z: Object) (a: Arrow w x) (b: Arrow x y) (c0: Arrow y z) (v: obj w):
      {p: arr z (c0 (b (a v))) (c0 (b (a v))) * arr z (c0 (b (a v))) (c0 (b (a v))) | iso_arrows (fst p) (snd p)} :=
    (map_arr c0 (map_arr b (map_arr a (cat_id: arr _ v v))), map_arr c0 (map_arr b (map_arr a (cat_id: arr _ v v)))).
  Next Obligation. split; repeat rewrite preserves_id; apply id_l. Qed.

  Let comp_assoc' w x y z (a: Arrow w x) (b: Arrow x y) (c: Arrow y z): comp c (comp b a) == comp (comp c b) a.
  Proof.
   exists (comp_assoc_arrows _ _ _ _ a b c).
   simpl. intros. unfold compose.
   repeat rewrite preserves_id.
   rewrite id_l, id_r, H. reflexivity.
  Qed.

  Global Instance cat: Category Object Arrow := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r' } .

End contents.
