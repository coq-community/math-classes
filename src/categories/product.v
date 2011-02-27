Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra ChoiceFacts interfaces.functors 
  theory.categories categories.cat.

Axiom dependent_functional_choice: DependentFunctionalChoice.

Section contents.

  Context {I: Type} (O: I → Type)
    `{∀ i, Arrows (O i)}
    `{∀ i (x y: O i), Equiv (x ⟶ y)}
    `{∀ i, CatId (O i)} `{∀ i, CatComp (O i)}
    `{∀ i, Category (O i)}.

  Definition Object := ∀ i, O i.
  Global Instance pa: Arrows Object := λ x y, ∀ i, x i ⟶ y i. (* todo: make nameless *)

  Global Instance: CatId Object := λ _ _, cat_id.
  Global Instance: CatComp Object := λ _ _ _ d e i, d i ◎ e i.
  Global Instance e (x y: Object): Equiv (x ⟶ y) := λ f g, ∀ i, f i = g i.

  Global Instance: ∀ x y: Object, Setoid (x ⟶ y).

  Global Instance: Category Object.
  Proof with try reflexivity.
   constructor. apply _.
      intros ? ? ? x y E x' y' F i.
      change (x i ◎ x' i = y i ◎ y' i).
      rewrite (E i), (F i)...
     repeat intro. apply comp_assoc.
    repeat intro. apply id_l. (* todo: Use left_identity *)
   repeat intro. apply id_r.
  Qed.

  Let product_object := cat.object Object.

  Notation ith_obj i := (cat.object (O i)).

  Program Definition project i: cat.object Object ⟶ ith_obj i :=
    cat.arrow (λ d, d i) (λ _ _ a, a i) _.
  Next Obligation. Proof. (* functorial *)
   constructor; intros; try reflexivity; try apply _.
   constructor; try apply _.
   intros ? ? E. apply E.
  Qed.

  Section factors.

    Variables (C: cat.Object) (X: ∀ i, C ⟶ ith_obj i).

    Let ith_functor i := cat.Functor_inst _ _ (X i).
      (* todo: really necessary? *)

    Program Definition factor: C ⟶ product_object
      := cat.arrow (λ (c: C) i, X i c) (λ (x y: C) (c: x ⟶ y) i, fmap (X i) c) _.
    Next Obligation. Proof with try reflexivity; intuition. (* functorial *)
     constructor; intros; try apply _.
       constructor; try apply _.
       intros ? ? E ?.
       change (fmap (X i) x = fmap (X i) y).
       rewrite E...
      intro. unfold fmap at 1. rewrite preserves_id... destruct X...
     intro. unfold fmap at 1. rewrite preserves_comp... destruct X...
    Qed. (* todo: those [destruct X]'s shouldn't be necessary *)

    Lemma s: is_sole (λ h', ∀ i, X i = project i ◎ h') factor.
    Proof with try reflexivity; intuition.
     split.
      intro.
      exists (λ v, refl_arrows (X i v)).
      simpl. unfold compose. intros ? ? ?.
      rewrite right_identity, left_identity...
     intros alt alt_factors.
     generalize (dependent_functional_choice I _ _ alt_factors). clear alt_factors.
     unfold isoT in *.
     simpl.
     intros [x H4].
     unfold equiv.
     unfold cat.e.
     unfold compose in H4.
     set (P := λ v, prod (alt v ⟶ (λ i, (X i) v)) ((λ i, (X i) v) ⟶ alt v)).
     set (d := λ v, (λ i, snd (` (x i v)), λ i, fst (` (x i v))): P v).
     assert (∀ v, uncurry iso_arrows (d v)) as Q.
      split; simpl; intro.
       change (snd (` (x i v)) ◎ fst (` (x i v)) = cat_id).
       destruct (x i v) as [? []]...
      change (fst (` (x i v)) ◎ snd (` (x i v)) = cat_id).
      destruct (x i v) as [? []]...
     exists (λ v, exist (uncurry iso_arrows) _ (Q v)).
     intros p q r i.
     simpl.
     unfold comp.
     unfold CatComp_instance_0. (* todo: no! *)
     pose proof (H4 i p q r). clear H4.
     destruct (x i p) as [aa0 i0].
     destruct (x i q) as [a1a2 i1].
     simpl in *.
     unfold uncurry in *.
     unfold iso_arrows in *.
     destruct (cat.Functor_inst _ _ alt).
     simpl in *.
     assert (fmap alt r = fmap alt r).
      intuition.
     simpl in *.
     rewrite (H4 i). clear H4.
     unfold compose in x, aa0, a1a2.
     simpl in *.
     unfold fmap.
     simpl.
     set (cat.Fmap_inst _ _ alt) in |- *.
     rewrite <- (left_identity (f p q r i ◎ fst aa0)).
     transitivity ((fst a1a2 ◎ snd a1a2) ◎ (f p q r i ◎ fst aa0)).
      apply comp_proper...
     apply transitivity with ((fst a1a2) ◎ (((snd a1a2) ◎ (cat.Fmap_inst _ _ alt p q r i)) ◎ (fst aa0))).
      repeat rewrite associativity...
     simpl.
     rewrite <- H5.
     repeat rewrite <- (associativity _ _).
     rewrite (proj2 i0), right_identity...
    Qed. (* WARNING: Uses DependentFunctionalChoice. (Todo: reflect.) *)
      (* todo: awful proof. clean up! *)

  End factors.

  (* At the time of this writing (Coq trunk 12801), attempting to state the above in terms
  of the nice product-relates interfaces from theory/categories results in universe
  inconsistency errors that I have isolated and reported as Coq bug #2252. *)

  Global Instance mono (X Y: Object): ∀ (a: X ⟶ Y), (∀ i, @Mono _ _ (H0 _) (H2 i) _ _ (a i)) → Mono a.
  Proof. firstorder. Qed. (* todo: why so ugly all of a sudden? *)

End contents.
