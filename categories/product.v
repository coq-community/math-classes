Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra ChoiceFacts theory.categories.
Require categories.cat.

Axiom dependent_functional_choice: DependentFunctionalChoice.

Section contents.

  Context (I: Type) (O: I -> Type) (A: forall i, O i -> O i -> Type)
    {ei: forall i (x y: O i), Equiv (A i x y)}
    `{forall i, CatId (O i) (A i)} `{forall i, CatComp (O i) (A i)}
    {c: forall i, Category (O i) (A i)}.

  Definition Object := forall i, O i.
  Definition Arrow := fun x y: Object => forall i, A i (x i) (y i).

  Global Instance: CatId Object Arrow := fun _ _ => cat_id.
  Global Instance comp': CatComp Object Arrow := fun _ _ _ d e i => comp (d i) (e i).
  Global Instance e x y: Equiv (Arrow x y) := fun f g => forall i, f i == g i.

  Let ith_cat i := cat.object_from_instance (O i) (A i).

  Let hint c0 i := @cat.map_arr_mor c0 (ith_cat i).
    (* todo: should not be needed *)

  Global Instance: forall x y, Equivalence (e x y).
  Proof with auto.
   constructor.
     repeat intro. reflexivity.
    repeat intro. symmetry...
   intros ? ? ? E ? i. rewrite (E i)...
  Qed.

  Global Instance cat: Category Object Arrow.
  Proof with try reflexivity.
   constructor. apply _.
      intros ? ? ? x y E x' y' F i.
      change (comp (x i) (x' i) == comp (y i) (y' i)).
      rewrite (E i), (F i)...
     repeat intro. apply comp_assoc.
    repeat intro. apply id_l.
   repeat intro. apply id_r.
  Qed.

  Definition product_obj: cat.Object := cat.object_from_instance Object Arrow.

  Program Definition project (i: I): cat.Arrow product_obj (ith_cat i) :=
    cat.arrow product_obj (ith_cat i) (fun d => d i) (fun _ _ a => a i) _.
  Next Obligation. Proof. (* functorial *)
   constructor; intros; try reflexivity.
   constructor; try apply _.
   intros ? ? E. apply E.
  Qed.

  Section factors.

    Variables (c0: cat.Object) (X: forall i, cat.Arrow c0 (ith_cat i)).

    Implicit Arguments cat.map_arr [[x] [y] [v] [w]].

    Program Definition factor: categories.cat.Arrow c0 product_obj
      := cat.arrow _ product_obj (fun X0 _ => X _ X0) (fun _ _ X0 i => cat.map_arr (X i) X0) _.
    Next Obligation. Proof with reflexivity. (* functorial *)
     pose proof (fun i => cat.functor_inst _ _ (X i)). (* shouldn't be necessary *)
     constructor; intros.
       constructor; try apply _.
       intros ? ? E ?. rewrite E...
      intro. rewrite preserves_id...
     intro. rewrite preserves_comp...
    Qed.

    Let hint' := cat.map_arr_mor.

    Lemma s: is_sole (fun h' => forall i, X i == comp (project i) h') factor.
    Proof with try reflexivity.
     split.
      intro.
      exists (fun v => refl_arrows (X i v)).
      simpl. unfold compose. intros ? ? ? ? E.
      rewrite id_r, id_l, E...
     intros alt alt_factors.
     generalize (dependent_functional_choice I _ _ alt_factors). clear alt_factors.
     unfold equiv, cat.e. simpl. unfold compose.
     intros [x H2].
     set (P := fun v => prod (Arrow (alt v) (fun i : I => (X i) v)) (Arrow (fun i : I => (X i) v) (alt v))).
     set (d := fun v => (fun i => snd (proj1_sig (x i v)), fun i => fst (proj1_sig (x i v))): P v).
     assert (forall v, iso_arrows (fst (d v)) (snd (d v))) as Q.
      split; simpl; intro.
       change (comp (snd (proj1_sig (x i v))) (fst (proj1_sig (x i v))) == cat_id).
       destruct (x i v) as [? Q]. apply Q. (* Using Coq trunk 12609 this line was just [apply x], but that broke in subsequent revisions. :-( *)
      change (comp (fst (proj1_sig (x i v))) (snd (proj1_sig (x i v))) == cat_id).
      destruct (x i v) as [? Q]. apply Q. (* As above. *)
     exists (fun v => exist (fun p => iso_arrows (fst p) (snd p)) _ (Q v)).
     intros p q r r' rr' i.
     simpl.
     change (comp (cat.map_arr alt r i) (fst (proj1_sig (x i p))) == comp (fst (proj1_sig (x i q))) (cat.map_arr (X i) r')).
     pose proof (H2 i p q r r' rr'). clear H2.
     destruct (x i p) as [aa0 i0].
     destruct (x i q) as [a1a2 i1].
     simpl in *.
     assert (cat.map_arr alt r == cat.map_arr alt r').
      rewrite rr'...
     rewrite (H2 i). clear H2.
     rewrite rr' in H1.
     rewrite <- (id_l _ _  (comp (cat.map_arr alt r' i) (fst aa0))).
     rewrite <- (proj1 i1).
     apply transitivity with (comp (fst a1a2) (comp (comp (snd a1a2) (cat.map_arr alt r' i)) (fst aa0))).
      rewrite comp_assoc.
      repeat rewrite (comp_assoc _ _)... (* todo: why must we specify the implicits? *)
     rewrite <- H1.
     repeat rewrite <- (comp_assoc _ _).
     rewrite (proj2 i0), id_r...
    Qed. (* WARNING: Uses DependentFunctionalChoice. (Todo: reflect.) *)

  End factors.

  Lemma yep: is_product ith_cat product_obj project factor.
  Proof. intro. apply s. Qed. 

  Global Instance mono: forall (a: Arrow X Y), (forall i, Mono (a i)) -> Mono a.
  Proof. firstorder. Qed.

  (* todo: register a Producer for Cat *)

End contents.
