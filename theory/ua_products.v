Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program
  universal_algebra theory.categories.
Require setoids.

Section algebras.

  Context
    (sig: Signature) (I: Type) (carriers: I -> sorts sig -> Type)
    `(forall i s, Equiv (carriers i s))
    `{forall i, AlgebraOps sig (carriers i)}
    `{forall i, Algebra sig (carriers i)}.

  Definition carrier: sorts sig -> Type := fun sort => forall i: I, carriers i sort.

  Fixpoint rec_impl o: (forall i, op_type (sorts sig) (carriers i) o) -> op_type (sorts sig) carrier o :=
    match o return (forall i, op_type (sorts sig) (carriers i) o) -> op_type (sorts sig) carrier o with
    | constant _ => id
    | function _ g => fun X X0 => rec_impl g (fun i => X i (X0 i))
    end.

  Instance rec_impl_proper: forall o, Proper (equiv ==> equiv) (rec_impl o).
  Proof with auto.
   induction o; simpl. repeat intro...
   intros ? ? Y x0 y0 ?. apply IHo.
   intros. intro. apply Y. change (x0 i == y0 i)...
  Qed.

  Global Instance product_ops: AlgebraOps sig carrier := fun o => rec_impl (sig o) (fun i => algebra_op sig o).

  Instance: forall o: sig, Proper equiv (algebra_op sig o: op_type (sorts sig) carrier (sig o)).
  Proof. intro. apply rec_impl_proper. intro. apply (algebra_propers _). Qed.

  Instance product_e sort: Equiv (carrier sort) := equiv. (* hint; shouldn't be needed *)

  Global Instance product_algebra: Algebra sig carrier.

  Lemma preservation i o: Preservation sig carrier (carriers i) (fun _ v => v i) (algebra_op sig o) (algebra_op sig o).
   unfold product_ops, algebra_op.
   set (select_op := fun i0 : I => H0 i0 o).
   replace (H0 i o) with (select_op i) by reflexivity.
   clearbody select_op.
   revert select_op.
   induction (operation_type sig o). simpl. reflexivity.
   intros. intro. apply IHo0.
  Qed.

  Lemma algebra_projection_morphisms i: @HomoMorphism sig carrier (carriers i) _ _ _ _ (fun a v => v i). 
  Proof.
   constructor; try apply _.
    intro. apply (@setoids.projection_morphism I (fun i => carriers i a) (fun i => _ i _: Equiv (carriers i a))).
    intro. apply _.
   apply preservation.
  Qed.

End algebras.

Section varieties.

  Context
    (et: EquationalTheory)
    (I: Type) (carriers: I -> sorts et -> Type)
    `(forall i s, Equiv (carriers i s))
    `(forall i, AlgebraOps et (carriers i))
    `(forall i, Variety et (carriers i)).

  Notation carrier := (carrier et I carriers).
  Let carrier_e := product_e et I carriers _.

  Fixpoint nqe {t}: op_type (sorts et) carrier t -> (forall i, op_type _ (carriers i) t) -> Prop :=
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
     apply (nqe_proper t (eval et vars term1 (eval et vars term2)) (eval et vars term1 (eval et vars term2)) H2 k p).
     subst p k.
     simpl.
     intro.
     pose proof (eval_proper et _ (fun (sort : sorts et) (n : nat) => vars sort n i) (fun (sort : sorts et) (n : nat) => vars sort n i) (reflexivity _) term1 term1 eq_refl).
     apply H3.
     apply IHterm2.
    apply IHterm1.
   change (nqe (rec_impl et _ _ (et o) (fun i : I => @algebra_op _ (carriers i) _ o)) (fun i : I => @algebra_op _ (carriers i) _ o)).
   generalize (fun i: I => @algebra_op et (carriers i) _ o).
   induction (et o); simpl. reflexivity.
   intros. apply IHo0.
  Qed.

  Lemma component_equality_to_product t
    (A A': op_type _ carrier t)
    (B B': forall i, op_type _ (carriers i) t):
    (forall i, B i == B' i) -> nqe A B -> nqe A' B' -> A == A'.
  Proof with auto.
   induction t; simpl in *; intros BE ABE ABE'.
    intro. rewrite ABE, ABE'...
   intros x y U.
   apply (IHt (A x) (A' y) (fun i => B i (x i)) (fun i => B' i (y i)))...
   intros. apply BE, U.
  Qed.

  Lemma laws_hold s: et_laws et s -> forall vars, eval_stmt et vars s.
  Proof.
   intros.
   pose proof (fun i => variety_laws s H2 (fun sort n =>  vars sort n i)). clear H2.
   assert (forall i : I, eval_stmt (et_sig et)
     (fun (sort : sorts (et_sig et)) (n : nat) => vars sort n i)
     (entailment_as_conjunctive_statement (et_sig et) s)).
    intros.
    rewrite <- boring_eval_entailment.
    apply (H3 i).
   clear H3.
   rewrite boring_eval_entailment.
   destruct s.
   simpl in *.
   destruct entailment_conclusion.
   simpl in *.
   destruct i.
   simpl in *.
   intro.
   apply component_equality_to_product with
       (fun i => eval et (fun sort n => vars sort n i) t) (fun i => eval et (fun sort n => vars sort n i) t0).
     intro.
     apply H2. clear H2. simpl.
     induction entailment_premises... simpl in *.
     intuition.
     simpl.
     rewrite <- (nqe_always (fst (projT2 a)) vars i).
     rewrite <- (nqe_always (snd (projT2 a)) vars i).
     intuition.
      apply H3.
     apply IHentailment_premises.
     apply H3.
    apply nqe_always.
   apply nqe_always.
  Qed. (* todo: clean up! also, we shouldn't have to go through boring.. *)

  Global Instance product_variety: @Variety et carrier carrier_e _.
   constructor. apply product_algebra. intro i. apply _.
   apply laws_hold.
  Qed.

End varieties.

Require categories.variety.

Section categorical.

  Context
    (et: EquationalTheory)
    (I: Type) (carriers: I -> variety.Object et).

  Definition product: variety.Object et.
   apply (@variety.object et (fun s => forall i: I, carriers i s)
     (product_e et I carriers (fun i => variety.variety_equiv et (carriers i)))
    (@product_ops et I carriers (fun i => variety.variety_op et (carriers i))) ).
   apply (@product_variety et I carriers).
   apply (fun _ => _).
  Defined.

  Program Definition project (i: I): product --> carriers i := fun _ c => c i.

  Next Obligation.
   apply (@algebra_projection_morphisms et I carriers
     (fun x => @variety.variety_equiv et (carriers x)) (fun x => variety.variety_op et (carriers x)) ).
   intro. apply _.
  Qed.

  Program Definition factor c (component_arrow: forall i, c --> carriers i): c --> product :=
    fun a X i => component_arrow i a X.

  Next Obligation. Proof.
   constructor; try apply _.
     constructor; try apply _.
     intros ? ? E i.
     destruct (proj2_sig (component_arrow i)).
     rewrite E. reflexivity.
    admit.
   apply (@product_algebra et I carriers).
   intro. apply _.
  Qed.

  Theorem yep: is_product carriers product project factor.
  Proof.
   split. repeat intro. reflexivity.
   repeat intro.
   simpl.
   symmetry.
   apply H.
  Qed.

End categorical.

(* Todo: Lots of cleanup. *)
