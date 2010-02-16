Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra ChoiceFacts theory.categories.
Require categories.cat.

Axiom dependent_functional_choice: DependentFunctionalChoice.

Section contents.

  Context {I: Type} (O: I -> Type)
    `{forall i, Arrows (O i)}
    `{forall i (x y: O i), Equiv (x --> y)}
    `{forall i, CatId (O i)} `{forall i, CatComp (O i)}
    `{forall i, Category (O i)}.

  Definition Object := forall i, O i.
  Global Instance pa: Arrows Object := fun x y => forall i, x i --> y i. (* todo: make nameless *)

  Global Instance: CatId Object := fun _ _ => cat_id.
  Global Instance: CatComp Object := fun _ _ _ d e i => comp (d i) (e i).
  Global Instance e (x y: Object): Equiv (x --> y) := fun f g => forall i, f i == g i.

  Global Instance: forall x y: Object, Setoid (x --> y).
  Proof with auto.
   constructor.
     repeat intro. reflexivity.
    repeat intro. symmetry...
   intros ? ? ? E ? i. rewrite (E i)...
  Qed.

  Global Instance: Category Object.
  Proof with try reflexivity.
   constructor. apply _.
      intros ? ? ? x y E x' y' F i.
      change (comp (x i) (x' i) == comp (y i) (y' i)).
      rewrite (E i), (F i)...
     repeat intro. apply comp_assoc.
    repeat intro. apply id_l.
   repeat intro. apply id_r.
  Qed.

  Let product_object := cat.object Object.

  Notation ith_obj i := (cat.object (O i)).

  Program Definition project i: cat.object Object --> ith_obj i :=
    cat.arrow (fun d => d i) (fun _ _ a => a i) _.
  Next Obligation. Proof. (* functorial *)
   constructor; intros; try reflexivity.
   constructor; try apply _.
   intros ? ? E. apply E.
  Qed.

  Section factors.

    Variables (C: cat.Object) (X: forall i, C --> ith_obj i).

    Let ith_functor i := cat.Functor_inst _ _ (X i).
    Let hint_b i := @functor_morphism _ _ _ _ _ _ _ _ _ _ _ _ (ith_functor i).
      (* These are necessary because of limitations in current unification.
       Todo: re-investigate with new proof engine. *)

    Program Definition factor: C --> product_object
      := cat.arrow (fun (c: C) i => X i c) (fun (x y: C) (c: x --> y) i => fmap (X i) c) _.
    Next Obligation. Proof with try reflexivity; intuition. (* functorial *)
     constructor; intros.
       constructor; try apply _.
       intros ? ? E ?.
       change (fmap (X i) x == fmap (X i) y).
       rewrite E...
      intro. unfold fmap at 1. rewrite preserves_id... destruct X...
     intro. unfold fmap at 1. rewrite preserves_comp... destruct X...
    Qed. (* todo: those [destruct X]'s shouldn't be necessary *)

    Lemma s: is_sole (fun h' => forall i, X i == comp (project i) h') factor.
    Proof with try reflexivity; intuition.
     split.
      intro.
      exists (fun v => refl_arrows (X i v)).
      simpl. unfold compose. intros ? ? ? ? E.
      rewrite id_r, id_l, E...
     intros alt alt_factors.
     generalize (dependent_functional_choice I _ _ alt_factors). clear alt_factors.
     unfold isoT in *.
     simpl.
     intros [x H4].
     unfold equiv.
     unfold cat.e.
     unfold compose in H4.
     set (P := fun v => prod (alt v --> (fun i => (X i) v)) ((fun i => (X i) v) --> alt v)).
     set (d := fun v => (fun i => snd (` (x i v)), fun i => fst (` (x i v))): P v).
     assert (forall v, uncurry iso_arrows (d v)) as Q.
      split; simpl; intro.
       change (comp (snd (` (x i v))) (fst (` (x i v))) == cat_id).
       destruct (x i v) as [? []]...
      change (comp (fst (` (x i v))) (snd (` (x i v))) == cat_id).
      destruct (x i v) as [? []]...
     exists (fun v => exist (uncurry iso_arrows) _ (Q v)).
     intros p q r r' rr' i.
     simpl.
     
     unfold comp.
     unfold CatComp_instance_0. (* todo: no! *)
     pose proof (H4 i p q r r' rr'). clear H4.
     destruct (x i p) as [aa0 i0].
     destruct (x i q) as [a1a2 i1].
     simpl in *.
     unfold uncurry in *.
     unfold iso_arrows in *.
     destruct (cat.Functor_inst _ _ alt).
     simpl in *.
     assert (fmap alt r == fmap alt r').
      rewrite rr'...
     rewrite (H4 i). clear H4.
     rewrite rr' in H5.
     unfold compose in x, aa0, a1a2.
     simpl in *.
     unfold fmap.
     set (cat.Fmap_inst _ _ alt).
     rewrite <- (id_l _ _ (comp (f p q r' i) (fst aa0))).
     transitivity (comp (comp (fst a1a2) (snd a1a2)) (comp (f p q r' i) (fst aa0))).
      apply comp_proper...
     apply transitivity with (comp (fst a1a2) (comp (comp (snd a1a2) (cat.Fmap_inst _ _ alt p q r' i)) (fst aa0))).
      rewrite comp_assoc.
      repeat rewrite (comp_assoc _ _)... (* todo: why must we specify the implicits? *)
     simpl.
     rewrite <- H5.
     repeat rewrite <- (comp_assoc _ _).
     rewrite (proj2 i0), id_r...
    Qed. (* WARNING: Uses DependentFunctionalChoice. (Todo: reflect.) *)
      (* todo: awful proof. clean up! *)

  End factors.

(* Can't do due to universe inconsistency:
  Lemma yep: is_product (fun i => ith_obj i) product_object project factor.
  Proof. intro. apply s. Qed. 
*)

  Global Instance mono (X Y: Object): forall (a: X --> Y), (forall i, @Mono _ _ (H0 _) (H2 i) _ _ (a i)) -> Mono a.
  Proof. firstorder. Qed. (* todo: why so ugly all of a sudden? *)

  (* todo: register a Producer for Cat *)

End contents.
