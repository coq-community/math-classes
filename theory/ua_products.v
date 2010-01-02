Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program
  universal_algebra categories.ua_variety theory.categories.

Section contents.

  Context (et: EquationalTheory) {I: Type} (v: I -> Variety et).

  Let carrier: sorts et -> Type := fun sort => forall i: I, v i sort.

  Instance e sort: Equiv (carrier sort) := fun x y => forall i, x i == y i.

  Instance: forall sort, Equivalence (e sort).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ?. symmetry. apply E.
   intros ? y ? ? ? i. transitivity (y i); firstorder.
  Qed.

  Fixpoint rec_impl o: (forall i, op_type (sorts et) (v i) o) -> op_type (sorts et) carrier o :=
    match o return (forall i, op_type (sorts et) (v i) o) -> op_type (sorts et) carrier o with
    | constant _ => id
    | function _ g => fun X X0 => rec_impl g (fun i => X i (X0 i))
    end.

  Instance rec_impl_proper: forall o, Proper ((fun x y => forall i, x i == y i) ==> equiv) (rec_impl o).
  Proof with auto.
   induction o; simpl. repeat intro...
   intros ? ? H x0 y0 ?. apply IHo.
   intros. apply H. change (x0 i == y0 i)...
  Qed.

  Instance: Implementation et carrier := fun o => rec_impl (et o) (fun i => variety_op _ (v i) o).

  Instance proper_implementation: Propers (et_sig et) carrier.
  Proof. intro. apply rec_impl_proper. intro. apply (variety_propers _ (v i)). Qed.

  Fixpoint nqe {t}: op_type (sorts et) carrier t -> (forall i, op_type _ (v i) t) -> Prop :=
   match t with
   | constant x => fun f g => forall i, f i == g i
   | function _ _ => fun f g => forall tuple, nqe (f tuple) (fun i => g i (tuple i))
   end. (* todo: rename *)

  Instance nqe_proper t: Proper (equiv ==> (fun x y => forall i, x i == y i) ==> iff) (@nqe t).
  Proof with auto; try reflexivity.
   induction t; simpl; intros ? ? P ? ? E.
    intuition. rewrite <- (P i), <- E... rewrite (P i), E...
   split; intros U tuple;
    apply (IHt (x tuple) (y tuple) (P tuple tuple (reflexivity _))
      (fun u => x0 u (tuple u)) (fun u => y0 u (tuple u)))...
    intro. apply E...
   intro. apply E...
  Qed.

  Lemma nqe_always {t} (term: Term _ nat t) vars:
    nqe (eval et vars term) (fun i => eval et (fun sort n => vars sort n i) term).
  Proof.
   induction term; simpl in *.
     reflexivity.
    set (k := (fun i : I =>
        eval et (fun (sort: sorts et) (n : nat) => vars sort n i) term1
          (eval et vars term2 i))).
    cut (nqe (eval et vars term1 (eval et vars term2)) k).
     set (p := fun i : I => eval et (fun (sort : sorts et) (n : nat) => vars sort n i) term1
       (eval et (fun (sort : sorts et) (n : nat) => vars sort n i) term2)).
     assert (op_type_equiv (sorts et) carrier t
        (eval et vars term1 (eval et vars term2))
        (eval et vars term1 (eval et vars term2))).
      apply sig_type_refl.
       intro. apply _.
      apply _.
     apply (nqe_proper t (eval et vars term1 (eval et vars term2)) (eval et vars term1 (eval et vars term2)) H k p).
     subst p k.
     simpl.
     intro.
     pose proof (eval_proper et _ (fun (sort : sorts et) (n : nat) => vars sort n i) (fun (sort : sorts et) (n : nat) => vars sort n i) (reflexivity _) term1 term1 eq_refl).
     apply H0.
     apply IHterm2.
    apply IHterm1.
   change (nqe (rec_impl (et o) (fun i : I => variety_op _ (v i) o)) (fun i : I => variety_op _ (v i) o)).
   generalize (fun x => variety_op _ (v x) o).
   induction (et o); simpl. reflexivity.
   intros. apply IHo0.
  Qed.

  Lemma component_equality_to_product t
    (A A': op_type _ carrier t)
    (B B': forall i, op_type _ (v i) t):
    (forall i, B i == B' i) -> nqe A B -> nqe A' B' -> A == A'.
  Proof with auto.
   induction t; simpl in *; intros BE ABE ABE'.
    intro. rewrite ABE, ABE'...
   intros x y H.
   apply (IHt (A x) (A' y) (fun i => B i (x i)) (fun i => B' i (y i)))...
   intros. apply BE, H.
  Qed.

  Program Definition product: Variety et := MkVariety et carrier _ _ _ _ _.

  Next Obligation. Proof with auto. (* todo: prove as lemma *)

   pose proof (fun i => variety_laws _ _ _ H (fun sort n =>  vars sort n i)). clear H.
   assert (forall i : I, eval_stmt (et_sig et)
     (fun (sort : sorts (et_sig et)) (n : nat) => vars sort n i)
     (entailment_as_conjunctive_statement (et_sig et) s)).
    intros.
    rewrite <- boring_eval_entailment.
    apply (H0 i).
   clear H0.
   rewrite boring_eval_entailment.
   destruct s.
   simpl in *.
   destruct entailment_conclusion.
   simpl in *.
   destruct i.
   simpl.
   intro.
   apply component_equality_to_product with
       (fun i => eval et (fun sort n => vars sort n i) t) (fun i => eval et (fun sort n => vars sort n i) t0).
     intro.
     apply H. clear H. simpl.
     induction entailment_premises... simpl in *.
     intuition.
     rewrite <- (nqe_always (fst (projT2 a)) vars i).
     rewrite <- (nqe_always (snd (projT2 a)) vars i).
     apply H.
    apply nqe_always.
   apply nqe_always.
  Qed. (* todo: clean up! also, we shouldn't have to go through boring.. *)

  Program Definition project (i: I): Arrow et product (v i) := fun _ c => c i.

  Next Obligation.
   constructor.
    constructor; try apply _.
    firstorder.
   intro.
   unfold op, Implementation_instance_0. (* todo: no! *)
   set (select_op := fun i0 : I => variety_op _ (v i0) o).
   replace (variety_op _ (v i) o) with (select_op i) by reflexivity.
   clearbody select_op.
   revert select_op.
   induction (operation_type (et_sig et) o). simpl. reflexivity.
   intros. intro. apply IHo0.
  Qed.

  Program Definition factor c (component_arrow: forall i, Arrow et c (v i)): Arrow et c product :=
    fun a X i => component_arrow i a X.

  Next Obligation. Proof.
   constructor.
    constructor; try apply _.
    intros ? ? E i.
    destruct (proj2_sig (component_arrow i)).
    rewrite E. reflexivity.
   set (fun i => proj1_sig (component_arrow i)).
   intro.
   change (Preservation (et_sig et) (variety_atomics _ c) carrier
     (fun (a0 : sorts (et_sig et)) (X : variety_atomics _ c a0) (i : I) =>
     v0 i a0 X) (op (et_sig et) o) (op (et_sig et) o)).
   set (fun i => @preserves _ _ _ _ _ _ _ _ (proj2_sig (component_arrow i)) o).
   clearbody p.
   change (forall (i : I),
       Preservation (et_sig et) (variety_atomics _ c) (variety_atomics _ (v i)) (v0 i) (op (et_sig et) o) (op (et_sig et) o)) in p.
   clearbody v0.
   unfold op, Implementation_instance_0 in *.
   set (fun i : I => variety_op _ (v i) o).
   change (forall i : I,
      Preservation (et_sig et) (variety_atomics _ c) (variety_atomics _ (v i))
       (v0 i) (variety_op _ c o) (o0 i)) in p.
   clearbody o0.
   revert p.
   generalize (variety_op _ c o).
   revert o0.
   induction (operation_type (et_sig et) o); simpl; auto.
  Qed.

  Theorem yep: is_product v product project factor.
  Proof.
   split. repeat intro. reflexivity.
   repeat intro.
   simpl.
   symmetry.
   apply H.
  Qed.

End contents.

(* Todo: Lots of cleanup. *)
