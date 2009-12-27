Set Automatic Introduction.

Require Import
  RelationClasses List Morphisms
  universal_algebra abstract_algebra canonical_names
  theory.categories.
Require categories.ua_variety.

Section contents. Variable et: EquationalTheory.

  Let op_type := op_type (sign_atomics et).

  (* The initial object will consists of arity-0 terms with a congruence incorporating the variety's laws.
   For this we simply take universal_algebra's Term type, but exclude variables by taking False
   as the variable index type: *)

  Let Term := Term et False.
  Let Term0 a := Term (constant _ a).

  (* Operations are implemented as App-tree builders, so that [o a b] yields [App (App (Op o) a) b]. *)

  Fixpoint app_tree {o}: Term o -> op_type Term0 o :=
    match o with
    | constant _ => id
    | function _ _ => fun x y => app_tree (App _ _ _ _ x y)
    end.
  
  Instance: Implementation et Term0 := fun x => app_tree (Op _ _ x).

  (* We define term equivalence on all operation types: *)

  Inductive e: forall o, Equiv (Term o) :=
    | e_refl o: Reflexive (e o)
    | e_trans o: Transitive (e o)
    | e_sym o: Symmetric (e o)
    | e_sub o h x y a b: e _ x y -> e _ a b -> e _ (App _ _ h o x a) (App _ _ h o y b) 
    | e_law (s: EqEntailment et): et_laws et s -> forall (v: Vars et Term0 nat),
      (forall x, In x (entailment_premises _ s) -> e _ (eval et v (fst (projT2 x))) (eval et v (snd (projT2 x)))) ->
        e _ (eval et v (fst (projT2 (entailment_conclusion _ s)))) (eval et v (snd (projT2 (entailment_conclusion _ s)))).

  Existing Instance e.
  Existing Instance e_refl.
  Existing Instance e_sym.
  Existing Instance e_trans.

  (* .. and then take the specialization at arity 0 for Term0: *)

  Instance e0: forall a, Equiv (Term0 a) := fun a => e (constant _ a).

  (* e (and hence e0) is an equivalence relation by definition: *)

  Instance: forall o, Equivalence (e o).
  Proof. constructor; apply _. Qed.

  Instance: forall a, Equivalence (e0 a).
  Proof. unfold e0. intro. apply _. Qed.

  (* The implementation is proper: *)

  Instance app_tree_proper: forall o, Proper (equiv ==> equiv)%signature (@app_tree o).
  Proof with auto.
   induction o; repeat intro...
   apply IHo, e_sub...
  Qed.

  Instance: Propers et Term0.
  Proof. intro. apply app_tree_proper. reflexivity. Qed.

  (* Better still, the laws hold: *)

  Lemma laws_hold s (L: et_laws et s):
    forall vars, @eval_stmt _ _ _ _ vars s.
  Proof with simpl in *; intuition.
   intros.
   rewrite boring_eval_entailment.
   destruct s. simpl in *. intros.
   apply (e_law _ L vars). clear L.
   induction entailment_premises... subst...
  Qed.

  (* And with that, we have our object: *)

  Definition v: Variety et := MkVariety et Term0 _ _ _ _ laws_hold.

  (* To show initiality, we begin by constructing arrows to arbitrary other objects: *)

  Section for_another_object.

    Variable w: Variety et.

    (* We can evaluate terms of arbitrary optype in w: *)

    Definition novars: forall x, Vars et x False.
     unfold Vars.
     intuition.
    Defined.

    Definition eval_nocst {o}: Term o -> op_type w o := @eval et w _ False o (novars w).

    Fixpoint subst {o} (v: Vars et Term0 nat) (t: universal_algebra.Term et nat o): Term o :=
      match t with
      | Var x y => v y x
      | App x y z r => App _ _ x y (subst v z) (subst v r)
      | Op o => Op _ _ o
      end.

    Lemma subst_eval o (v: Vars et Term0 nat) (t: universal_algebra.Term _ _ o):
      @eval _ w _ _ _ (fun x y => eval_nocst (v x y)) t ==
      eval_nocst (subst v t).
    Proof with auto.
     set (fun x y => eval_nocst (v0 x y)).
     induction t.
       simpl.
       reflexivity.
      simpl.
      apply IHt1.
      assumption.
     simpl.
     unfold op.
     apply (variety_propers _ w).
    Qed.

    Fixpoint gel {o}: op_type Term0 o -> Term o -> Prop :=
      match o with
      | constant a => fun x y => x = y
      | function d _ => fun x y => forall z: Term0 _, @gel _ (x z) (App _ _ _ _ y z)
      end.

    Lemma gel_impl_term a (t: Term a): gel (app_tree t) t.
    Proof.
     induction a; simpl. reflexivity.
     intros. apply IHa.
    Qed.

    Lemma subst_eval'
     (x : sign_atomics et)
     (t : universal_algebra.Term0 et x)
     (v0 : Vars et Term0 nat):
      eval et v0 t = subst v0 t.
    Proof.
     pattern x, t.
     apply indu.
       simpl.
       intros.
       apply H0.
       assumption.
      simpl.
      intros.
      reflexivity.
     intros.
     assert (gel (eval et v0 (Op et nat o)) (subst v0 (Op et nat o))).
      simpl.
      apply gel_impl_term.
     revert H.
     generalize (Op et nat o).
     intro.
     induction (et o).
      simpl.
      intro.
      assumption.
     simpl.
     intros.
     apply IHo0.
     simpl.
     rewrite H0.
     apply H.
    Qed.

    Lemma prep_eval (x: sign_atomics et) (t: universal_algebra.Term0 et x) (v0: Vars et Term0 nat):
      eval_nocst (eval et v0 t) == 
      @eval _ w _ _ _ (fun x y => eval_nocst (v0 x y)) t.
    Proof.
     rewrite subst_eval.
     rewrite (subst_eval' x t v0).
     reflexivity.
    Qed.

    Definition morph a: v a -> w a := @eval_nocst _.

    Instance prep_proper: Proper (equiv ==> equiv) (@eval_nocst o).
    Proof.
     intro.
     intro.
     intro.
     intro.
     induction H.
         induction x.
           intuition.
          simpl.
          apply IHx1.
          assumption.
         simpl.
         apply (variety_propers _ w o).
       transitivity (eval_nocst y); assumption.
       symmetry. assumption.
      simpl.
      apply IHe1.
      assumption.
     simpl.
     unfold Vars in v0.
     pose proof (variety_laws et w s H (fun a n => eval_nocst (v0 a n))).
     clear H.
     destruct s.
     simpl in *.
     rewrite boring_eval_entailment in H2.
     simpl in H2.
     rewrite prep_eval.
     rewrite prep_eval.
     apply H2. clear H2.
     clear entailment_conclusion.
     induction entailment_premises.
      simpl. auto.
     simpl in *.
     split; try intuition.
     clear IHentailment_premises.
     rewrite <- prep_eval.
     rewrite <- prep_eval.
     apply H1.
     left.
     reflexivity.
    Qed.

    Instance prep_mor: forall a, Setoid_Morphism (@eval_nocst (constant _ a)).
     intro.
     constructor; try apply _.
    Qed.

    Instance homo: @HomoMorphism et Term0 w _ (variety_equiv et w) _ _ (fun _ => eval_nocst).
     constructor.
      intro. apply prep_mor.
     unfold op.
     unfold Implementation_instance_0.
     simpl.
     intro.
     assert (eval_nocst (Op _ _ o) == variety_op _ w o).
      simpl.
      apply (variety_propers _ w o).
     revert H.
     generalize (Op _ False o).
     generalize (variety_op et w o).
     intros.
     induction (et o).
      simpl.
      assumption.
     simpl.
     intros.
     apply IHo1.
     simpl.
     apply H.
     reflexivity.
    Qed.

    Program Definition bla: ua_variety.Arrow et v w := fun _ => eval_nocst.

    Definition uniq: forall y, bla == y.
     intro.
     unfold equiv.
     unfold ua_variety.e.
     simpl.
     unfold Morphisms.pointwise_relation.
     intros.
     destruct y.
     simpl in *.
     pattern b, a.
     apply indu.
       simpl.
       intros.
       apply H0.
       assumption.
      intuition.
     intros.
     pose proof (@preserves et Term0 w _ _ _ _ x h o).
     unfold op in H.
     unfold Implementation_instance_0 in H.
     change (Preservation et Term0 w x (app_tree (Op _ _ o)) (@eval_nocst _ (Op _ _ o))) in H.
     revert H.
     generalize (Op _ False o).
     intros t H.
     induction (et o).
      simpl.
      symmetry.
      assumption.
     simpl.
     intros.
     apply IHo0.
     clear IHo0.
     simpl in H.
     simpl.
     assert (app_tree (App _ _ o0 a0 t v0) == app_tree (App _ _ o0 a0 t v0)).
      apply app_tree_proper.
      unfold equiv.
      reflexivity.
     apply (@Preservation_proper et Term0 w _ _ _ _ x h _ _ o0
      (app_tree (App _ _ o0 a0 t v0)) (app_tree (App _ _ o0 a0 t v0)) H1
      (eval_nocst t (eval_nocst v0)) (eval_nocst t (x a0 v0))).
      2: apply H.
     pose proof (@prep_proper _ t t (reflexivity _)).
     apply H2.
     assumption.
    Qed.

  End for_another_object.

  Lemma the: @proves_initial (Variety et) (ua_variety.Arrow et) _ v bla.
   unfold proves_initial.
   intro.
   apply uniq.
  Qed.

  (* Todo: This module requires heavy cleanup. *)
  (* Todo: Show decidability of equality (likely quite tricky). Without that, we cannot use any of this to
   get a canonical model of the naturals/integers, because such models must be decidable. *)

End contents.
