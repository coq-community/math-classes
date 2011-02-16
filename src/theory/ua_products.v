Require Import
  Morphisms Setoid abstract_algebra Program
  universal_algebra ua_homomorphisms 
  theory.categories categories.variety.
Require setoids.

Section algebras.

  Context
    (sig: Signature) (I: Type) (carriers: I → sorts sig → Type)
    `(∀ i s, Equiv (carriers i s))
    `{∀ i, AlgebraOps sig (carriers i)}
    `{∀ i, Algebra sig (carriers i)}.

  Definition carrier: sorts sig → Type := λ sort, ∀ i: I, carriers i sort.

  Fixpoint rec_impl o: (∀ i, op_type (carriers i) o) → op_type carrier o :=
    match o return (∀ i, op_type (carriers i) o) → op_type carrier o with
    | ne_list.one _ => id
    | ne_list.cons _ g => λ X X0, rec_impl g (λ i, X i (X0 i))
    end.

  Let u (s: sorts sig): Equiv (forall i : I, carriers i s).
   apply setoids.product_equiv.
   intro. apply _.
  Defined.

  Instance rec_impl_proper: ∀ o,
    Proper (@setoids.product_equiv I _ (fun _ => op_type_equiv _ _ _) ==> (=)) (rec_impl o).
  Proof with auto.
   induction o; simpl. repeat intro...
   intros ? ? Y x0 y0 ?. apply IHo.
   intros. intro. apply Y. change (x0 i = y0 i)...
  Qed.

  Global Instance product_ops: AlgebraOps sig carrier := λ o, rec_impl (sig o) (λ i, algebra_op o).

  Instance: ∀ o: sig, Proper (=) (algebra_op o: op_type carrier (sig o)).
  Proof. intro. apply rec_impl_proper. intro. apply (algebra_propers _). Qed.

  Instance product_e sort: Equiv (carrier sort) := (=). (* hint; shouldn't be needed *)

  Global Instance product_algebra: Algebra sig carrier.

  Lemma preservation i o: Preservation sig carrier (carriers i) (λ _ v, v i) (algebra_op o) (algebra_op o).
   unfold product_ops, algebra_op.
   set (select_op := λ i0 : I, H0 i0 o).
   replace (H0 i o) with (select_op i) by reflexivity.
   clearbody select_op.
   revert select_op.
   induction (operation_type sig o). simpl. reflexivity.
   intros. intro. apply IHo0.
  Qed.

  Lemma algebra_projection_morphisms i: @HomoMorphism sig carrier (carriers i) _ _ _ _ (λ a v, v i). 
  Proof.
   constructor; try apply _.
    intro. apply (@setoids.projection_morphism I (λ i, carriers i a) (λ i, _ i _: Equiv (carriers i a))).
    intro. apply _.
   apply preservation.
  Qed.

End algebras.

Section varieties.

  Context
    (et: EquationalTheory)
    (I: Type) (carriers: I → sorts et → Type)
    `(∀ i s, Equiv (carriers i s))
    `(∀ i, AlgebraOps et (carriers i))
    `(∀ i, InVariety et (carriers i)).

  Notation carrier := (carrier et I carriers).
  Let carrier_e := product_e et I carriers _.

  Fixpoint nqe {t}: op_type carrier t → (∀ i, op_type (carriers i) t) → Prop :=
   match t with
   | ne_list.one _ => λ f g, ∀ i, f i = g i
   | ne_list.cons _ _ => λ f g, ∀ tuple, nqe (f tuple) (λ i, g i (tuple i))
   end. (* todo: rename *)

  Instance nqe_proper t: Proper ((=) ==> (λ x y, ∀ i, x i = y i) ==> iff) (@nqe t).
  Proof with auto; try reflexivity.
   induction t; simpl; intros ? ? P ? ? E.
    intuition. rewrite <- (P i), <- E... rewrite (P i), E...
   split; intros U tuple;
    apply (IHt (x tuple) (y tuple) (P tuple tuple (reflexivity _))
      (λ u, x0 u (tuple u)) (λ u, y0 u (tuple u)))...
    intro. apply E...
   intro. apply E...
  Qed.

  Lemma nqe_always {t} (term: Term _ nat t) vars:
    nqe (eval et vars term) (λ i, eval et (λ sort n, vars sort n i) term).
  Proof.
   induction term; simpl in *.
     reflexivity.
    set (k := (λ i : I,
        eval et (λ (sort: sorts et) (n : nat), vars sort n i) term1
          (eval et vars term2 i))).
    cut (nqe (eval et vars term1 (eval et vars term2)) k).
     set (p := λ i : I, eval et (λ (sort : sorts et) (n : nat), vars sort n i) term1
       (eval et (λ (sort : sorts et) (n : nat), vars sort n i) term2)).
     assert (op_type_equiv (sorts et) carrier t
        (eval et vars term1 (eval et vars term2))
        (eval et vars term1 (eval et vars term2))).
      apply sig_type_refl.
       intro. apply _.
      apply eval_proper; try apply _.
        apply product_algebra.
        intro. apply _.
       reflexivity.
      reflexivity.
     apply (nqe_proper t (eval et vars term1 (eval et vars term2)) (eval et vars term1 (eval et vars term2)) H2 k p).
     subst p k.
     simpl.
     intro.
     pose proof (eval_proper et _ (λ (sort : sorts et) (n : nat), vars sort n i) (λ (sort : sorts et) (n : nat), vars sort n i) (reflexivity _) term1 term1 eq_refl).
     apply H3.
     apply IHterm2.
    apply IHterm1.
   change (nqe (rec_impl et _ _ (et o) (λ i : I, @algebra_op _ (carriers i) _ o)) (λ i : I, @algebra_op _ (carriers i) _ o)).
   generalize (λ i: I, @algebra_op et (carriers i) _ o).
   induction (et o); simpl. reflexivity.
   intros. apply IHo0.
  Qed.

  Lemma component_equality_to_product t
    (A A': op_type carrier t)
    (B B': ∀ i, op_type (carriers i) t):
    (∀ i, B i = B' i) → nqe A B → nqe A' B' → A = A'.
  Proof with auto.
   induction t; simpl in *; intros BE ABE ABE'.
    intro. rewrite ABE, ABE'...
   intros x y U.
   apply (IHt (A x) (A' y) (λ i, B i (x i)) (λ i, B' i (y i)))...
   intros. apply BE, U.
  Qed.

  Lemma laws_hold s: et_laws et s → ∀ vars, eval_stmt et vars s.
  Proof.
   intros.
   pose proof (λ i, variety_laws s H2 (λ sort n, vars sort n i)). clear H2.
   assert (∀ i : I, eval_stmt (et_sig et)
     (λ (sort : sorts (et_sig et)) (n : nat), vars sort n i)
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
       (λ i, eval et (λ sort n, vars sort n i) t) (λ i, eval et (λ sort n, vars sort n i) t0).
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

  Global Instance product_variety: InVariety et carrier (e:=carrier_e).
  Proof.
   constructor. apply product_algebra. intro i. apply _.
   apply laws_hold.
  Qed.

End varieties.

Require categories.variety.

Section categorical.

  Context
    (et: EquationalTheory).

  Global Instance: Producer (variety.Object et) := λ I carriers,
    {| variety.variety_carriers := λ s, ∀ i, carriers i s
    ; variety.variety_proof := product_variety et I _ _ _ (fun H => variety.variety_proof et (carriers H)) |}.
      (* todo: clean up *)

  Section for_a_given_c. Context (I: Type) (c: I → variety.Object et).

  Global Program Instance: ElimProduct c (product c) := λ i _ c, c i.

  Next Obligation.
   apply (@algebra_projection_morphisms et I c
     (λ x, @variety.variety_equiv et (c x)) (λ x, variety.variety_op et (c x)) ).
   intro. apply _.
  Qed.

  Global Program Instance: IntroProduct c (product c) := λ _ h a X i, h i a X.

  Next Obligation. Proof with intuition.
   repeat constructor; try apply _.
     intros ?? E ?. destruct h. simpl. rewrite E...
    intro.
    pose proof (λ i, @preserves _ _ _ _ _ _ _ _ (proj2_sig (h i)) o).
    unfold product_ops, algebra_op.
    set (λ i, variety.variety_op et (c i) o).
    set (variety.variety_op et H o) in *.
    change (∀i : I, Preservation et H (c i) (` (h i)) o1 (o0 i)) in H0.
    clearbody o0 o1. revert o0 o1 H0.
    induction (et o); simpl...
   apply (@product_algebra et I c)...
  Qed.

  Global Instance: Product c (product c).
  Proof.
   split; repeat intro. reflexivity.
   symmetry. simpl. apply H.
  Qed.

  End for_a_given_c.

  Global Instance: HasProducts (variety.Object et).

End categorical.

(* Todo: Lots of cleanup. *)
