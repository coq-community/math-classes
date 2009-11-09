
Require Import
  Morphisms Setoid List CanonicalNames CatStuff Program.

Inductive Signature: Type := { sign_op:> Set; arity:> sign_op -> nat }.

(* op_type translates arities into operation types (e.g. 2 is mapped to A->A->A). *)

Fixpoint op_type A (n: nat): Type :=
  match n with
  | 0 => A
  | S n' => A -> op_type A n'
  end.

(* Extensional equality for operations of arbitrary arity: *)

Definition op_type_equiv `{e: Equiv A}: forall n, Equiv (op_type A n) :=
 fix F (n: nat) :=
  match n return Equiv (op_type A n) with
  | 0 => equiv
  | S n' => (equiv ==> F n')%signature
  end.

Existing Instance op_type_equiv.

(* op_type_equiv is /almost/ an equivalence relation. Note that is is /not/ readily reflexive. *)

Instance sig_type_trans `{e: Equiv A} `{!Reflexive e} `{!Transitive e}: Transitive (op_type_equiv n).
Proof. induction n. assumption. simpl. intros x y z. unfold equiv, respectful. eauto. Qed.

Instance sig_type_sym `{e: Equiv A} `{!Symmetric e}: Symmetric (op_type_equiv n).
Proof with try assumption. induction n... simpl. intro. unfold respectful. symmetry. apply H. symmetry... Qed.

(* Given maps between A and B, there are maps between op_type A and op_type B: *)

Section map_op.

  Context {A B: Type} `{!Equiv A} `{!Equiv B} (f: A -> B) (g: B -> A)
    `{!Proper (equiv ==> equiv) f} `{!Proper (equiv ==> equiv) g}.

  Fixpoint map_op {n: nat}: op_type A n -> op_type B n :=
      match n return op_type A n -> op_type B n with
      | 0 => fun x => f x
      | S n' => fun x => fun y => map_op (x (g y))
      end.

  Global Instance map_op_proper: Proper (equiv ==> equiv) (@map_op n).
  Proof.
   induction n; simpl; repeat intro. firstorder.
   apply IHn, (H (g x0) (g y0)). firstorder.
  Qed.

End map_op.

Section for_signature. Variable sign: Signature.

  Class Implementation A := op: forall o, op_type A (sign o).

  Class Propers A `{Equiv A} `{Implementation A} := propers:> forall o: sign, Proper (op_type_equiv (sign o)) (op o).

  Inductive Term: nat -> Set :=
    | Var (v: nat): Term 0
    | App n: Term (S n) -> Term 0 -> Term n
    | Op (o: sign): Term (sign o).

  Inductive Statement: Type := Eq (a b: Term 0) | Impl (a b: Statement) | Ext (P: Prop).

  Section for_map. Context `{ea: Equiv A} `{eb: Equiv B} `{Implementation A} `{Implementation B} (f: A -> B).

    Fixpoint Preservation {n: nat}: op_type A n -> op_type B n -> Prop :=
      match n return op_type A n -> op_type B n -> Prop with
      | 0 => fun o o' => f o == o'
      | S n' => fun o o' => forall x, Preservation (o x) (o' (f x))
      end.

    Class HomoMorphism: Prop :=
      { homo_proper:> Proper (equiv ==> equiv) f
      ; preserves: forall (o: sign), Preservation (op o) (op o) }.

    Instance Preservation_proper `{HomoMorphism} `{!Equivalence ea} `{!Equivalence eb} n:
      Proper (op_type_equiv n ==> op_type_equiv n ==> iff) (@Preservation n).
    Proof.
     induction n.
      repeat intro.
      simpl in *. split; intro.
       rewrite <- H2, <- H3. assumption.
      rewrite H2, H3. assumption.
     repeat intro.
     split; repeat intro; simpl;
      apply (IHn (x x1) (y x1) (H2 x1 x1 (reflexivity _)) (x0 (f x1)) (y0 (f x1)) (H3 (f x1) (f x1) (reflexivity _)));
      apply (H4 x1).
    Qed.

  End for_map.

  Section eval. Context A `{ea: Equiv A} `{!Equivalence ea} `{!Implementation A} `{!Propers A}.

    Fixpoint eval {n: nat} (vars: nat -> A) (t: Term n) {struct t}: op_type A n :=
      match t in Term n return op_type A n with
      | Var v => vars v
      | Op o => op o
      | App n f a => eval vars f (eval vars a)
      end.

    Global Instance eval_proper (n: nat): Proper (pointwise_relation _ equiv ==> eq ==> equiv) (@eval n).
    Proof with auto.
     do 7 intro. subst.
     induction y0.
       apply H...
      apply IHy0_1...
     apply propers.
    Qed.

    Definition eval_stmt (vars: nat -> A): Statement -> Prop :=
      fix F (s: Statement) :=
      match s with
      | Eq a b => eval vars a == eval vars b
      | Impl a b => F a -> F b
      | Ext P => P
      end.

    Global Instance eval_stmt_proper: Proper (pointwise_relation _ equiv ==> eq ==> iff) eval_stmt.
    Proof with auto.
     intros v v' ve s s' se. subst.
     induction s'; simpl.
       split; intro.
        rewrite <- ve...
       rewrite ve...
      firstorder.
     intuition.
    Qed.

  End eval.

  Section category. Variable E: Statement -> Prop.

    Record Variety: Type := MkVariety
      { variety_carrier:> Type
      ; variety_equiv: Equiv variety_carrier
      ; variety_op:> Implementation variety_carrier
      ; variety_equivalence: Equivalence variety_equiv
      ; variety_propers: Propers variety_carrier
      ; variety_laws: forall s, E s -> forall vars, eval_stmt _ vars s
     }.

    Existing Instance variety_equivalence.
    Existing Instance variety_op.
    Existing Instance variety_propers.
    Existing Instance variety_equiv.

    Definition Arrow (X Y: Variety): Type := sig (@HomoMorphism X _ Y _ _ _).

    Global Program Instance: CatId Variety Arrow := fun o => id.

    Next Obligation.
     constructor. apply _.
     unfold id.
     intro.
     generalize (@op o _ o0). intro.
     induction (sign o0); simpl; intuition.
    Qed.

    Global Program Instance: CatComp Variety Arrow := fun x y z => fun f g v => (`f) ((`g) v).

    Next Obligation. Proof with reflexivity.
     destruct f. destruct g.
     constructor. repeat intro. simpl. rewrite H...
     intros. simpl.
     generalize (preserves x1 o) (preserves x0 o).
     generalize (@op z _ o) (@op y _ o) (@op x _ o).
     induction (sign o); simpl; intros. rewrite H. assumption.
     apply (IHn (o0 (x0 (x1 x2))) (o1 (x1 x2))); auto.
    Qed.

    Global Instance o_equiv: Equiv Variety := eq.

    Global Instance a_equiv (x y: Variety): Equiv (Arrow x y) := fun a a' => pointwise_relation _ equiv (proj1_sig a) (proj1_sig a').

    Global Instance homo_cat: Category Variety Arrow.
    Proof with auto.
     constructor; try apply _.
         intros.
         unfold a_equiv.
         destruct x. destruct y.
         constructor; repeat intro.
           reflexivity.
          symmetry...
         transitivity ((proj1_sig y) a)...
        repeat intro.
        unfold equiv in *.
        unfold a_equiv in *.
        unfold pointwise_relation in *.
        simpl.
        destruct x. destruct y. destruct z. destruct x0. destruct y0. destruct x1. destruct y1.
        unfold equiv in *.
        simpl in *.
        unfold pointwise_relation in *.
        intros.
        rewrite H0.
        apply H.
       intros.
       destruct w. destruct y. destruct z. destruct x. intro. reflexivity.
      intros. destruct x. destruct y. intro. reflexivity.
     intros. destruct x. destruct y. intro. reflexivity.
    Qed.

  End category.

  Section for_isomorphic_implementations.

    Context A B `{ea: Equiv A} `{eb: Equiv B} `{!Equivalence ea} `{!Equivalence eb} `{Implementation A} `{Implementation B}
      `{!Propers A} `{!Propers B}
      (ab: A->B) (ba: B->A)
      `(@HomoMorphism _ _ _ _ _ _ ab) `(@HomoMorphism _ _ _ _ _ _ ba)
      (iso_l: forall x, ba (ab x) == x) (iso_r: forall x, ab (ba x) == x).

    Lemma iso_vars_l (v: nat -> A): pointwise_relation _ equiv v (fun i => ba (ab (v i))).
    Proof. repeat intro. rewrite iso_l. reflexivity. Qed.

    Lemma iso_vars_r (v: nat -> B): pointwise_relation _ equiv v (fun i => ab (ba (v i))).
    Proof. repeat intro. rewrite iso_r. reflexivity. Qed.

    (* Evaluating a term in one implementation is "the same" as evaluating it in the other. *)

    Lemma carry_eval n (t: Term n) (v: nat -> B): eval _ (fun i => ba (v i)) t == map_op ba ab (eval _ v t).
    Proof with auto.
     induction t; simpl in *; intros.
       reflexivity.
      set (y := eval B v t2).
      assert (eval B v t1 y == eval B v t1 (ab (ba y))).
       clearbody y.
       assert (y == ab (ba y)). symmetry. apply iso_r.
       assert (pointwise_relation nat equiv v v). intro. reflexivity.
       apply (eval_proper B (Datatypes.S n) v v H4)...
      assert (map_op ba ab (eval B v t1 y) == map_op ba ab (eval B v t1 (ab (ba y)))).
       apply (@map_op_proper B A _ _ ba ab _ _ n)...
      transitivity (map_op ba ab (eval B v t1 (ab (ba y))))...
       apply IHt1.
       subst y.
       apply IHt2.
      symmetry...
     pose proof (@propers A _ _ _ o).
     pose proof (@propers B _ _ _ o).
     pose proof (@preserves A _ B _ _ _ ab _ o).
     revert H3 H4 H5.
     clear v.
     generalize (@op A H o) (@op B H0 o).
     induction (sign o).
      simpl.
      intros.
      rewrite <- iso_l. rewrite H5. reflexivity.
     simpl.
     repeat intro.
     apply IHn.
       apply H3. reflexivity.
      apply H4. reflexivity.
     assert (ab x == ab y). rewrite H6. reflexivity.
     apply (Preservation_proper ab _ _ _ (H3 x x (reflexivity _)) _ _ (H4 (ab x) (ab y) H7)).
     apply H5.
    Qed. (* todo: clean up *)

    (* Similarly, evaluating a statement in one implementation is "the same" as evaluating it in the other. *)

    Lemma carry_stmt_with (s: Statement) (v: nat -> A):
      eval_stmt A v s <-> eval_stmt B (fun i => ab (v i)) s.
    Proof with auto.
     intros.
     induction s; simpl.
       split; intros.
        rewrite <- (iso_r (eval B (fun i => ab (v i)) a)).
        rewrite <- (iso_r (eval B (fun i => ab (v i)) b)).
        rewrite <- (carry_eval 0 a (fun i => ab (v i))).
        rewrite <- (carry_eval 0 b (fun i => ab (v i))).
        rewrite <- iso_vars_l.
        rewrite H3.
        reflexivity.
       rewrite iso_vars_l.
       do 2 rewrite carry_eval.
       simpl. rewrite H3. reflexivity.
      firstorder.
     intuition.
    Qed.

    Lemma carry_stmt (s: Statement): (forall v, eval_stmt A v s) -> (forall v, eval_stmt B v s).
    Proof. intros. rewrite iso_vars_r. rewrite <- carry_stmt_with. apply H3. Qed.

  End for_isomorphic_implementations.

End for_signature.

Existing Instance variety_op.
Existing Instance variety_equivalence.
Existing Instance variety_equiv.
Existing Instance variety_propers.

Module notations.
  Global Infix "===" := (Eq _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
