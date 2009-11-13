Require Import
  Morphisms Setoid List CanonicalNames CatStuff Program.

Section pointwise_dependent_relation. Context A (B: A -> Type) (R: forall a, relation (B a)).

  Definition pointwise_dependent_relation: relation (forall a, B a) :=
    fun f f' => forall a, R _ (f a) (f' a).

  Global Instance pdr_equiv `{forall a, Equivalence (R a)}: Equivalence pointwise_dependent_relation.
  Proof. firstorder. Qed.

End pointwise_dependent_relation. (* todo: move elsewhere *)

Section with_atomic. Variable Atomic: Set.

  Inductive OpType: Set :=
    | constant (a: Atomic)
    | function (a: Atomic) (g: OpType).

  Definition op_type (T: Atomic -> Type): OpType -> Type :=
    fix F (t: OpType): Type :=
      match t with
      | constant a => T a
      | function a g => T a -> F g
      end.

  Section with_atomic_inter. Variable T: Atomic -> Type.

    Definition op_type_equiv
       `{e: forall A, Equiv (T A)}: forall o: OpType, Equiv (op_type T o) :=
     fix F (o: OpType): Equiv (op_type T o) :=
      match o return Equiv (op_type T o) with
      | constant A => e A
      | function A g => (e A ==> F g)%signature
      end.

    Existing Instance op_type_equiv.

    (* op_type_equiv is /almost/ an equivalence relation. Note that is is /not/ readily reflexive. *)

    Global Instance sig_type_trans `{e: forall A, Equiv (T A)} `{forall A, Reflexive (e A)} `{forall A, Transitive (e A)}: Transitive (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.

    Global Instance sig_type_sym `{e: forall A, Equiv (T A)} `{forall A, Symmetric (e A)}: Symmetric (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.

    Lemma sig_type_refl `{e: forall A, Equiv (T A)} `{forall a, Reflexive (e a)} (o: OpType) a (x: op_type T (function a o)) y:
      Proper equiv x ->
      op_type_equiv o (x y) (x y).
    Proof.
     intros.
     apply (H0 y y).
     reflexivity.
    Qed.

  End with_atomic_inter.

  Existing Instance op_type_equiv.

  Section map_op.

    (* Given maps between two sets of atomics, there are maps between the corresponding op_types*)

    Context {A B: Atomic -> Type} `{forall a, Equiv (A a)} `{forall a, Equiv (B a)}
     (ab: forall a, A a -> B a) (ba: forall a, B a -> A a)
     `{forall a, Proper (equiv ==> equiv) (ab a)}
     `{forall a, Proper (equiv ==> equiv) (ba a)}.

    Fixpoint map_op {o: OpType}: op_type A o -> op_type B o :=
      match o return op_type A o -> op_type B o with
      | constant u => ab u
      | function u v => fun x => fun y => map_op (x (ba u y))
      end.

    Global Instance map_op_proper o: Proper (op_type_equiv A o ==> op_type_equiv B o) (@map_op o).
    Proof. induction o; simpl; firstorder. Qed.

  End map_op.

End with_atomic.

Inductive Signature: Type :=
  { sign_op:> Set
  ; sign_atomics: Set
  ; sign_sig:> sign_op -> OpType sign_atomics }.

Section for_signature. Variable sign: Signature.

  Class Implementation (A: sign_atomics sign -> Type) := op: forall o, op_type _ A (sign o).

  Class Propers (A: sign_atomics sign -> Type) `{forall a, Equiv (A a)} `{Implementation A} :=
    propers:> forall o: sign, Proper (op_type_equiv _ A (sign o)) (op o).

  Inductive Term: OpType (sign_atomics sign) -> Set :=
    | Var (v: nat) (a: sign_atomics sign): Term (constant _ a)
    | App (t: OpType (sign_atomics sign)) y:  Term (function _ y t) -> Term (constant _ y) -> Term t
    | Op (o: sign): Term (sign o).

  Inductive Statement: Type := Eq t (a b: Term (constant _ t)) | Impl (a b: Statement) | Ext (P: Prop).

  Section for_map.
    Context (A: sign_atomics sign -> Type) (B: sign_atomics sign -> Type)
      `{ea: forall a, Equiv (A a)} `{eb: forall a, Equiv (B a)}
      `{!Implementation A} `{!Implementation B} (f: forall a, A a -> B a).

    Implicit Arguments f [[a]].

    Fixpoint Preservation {n: OpType (sign_atomics sign)}: op_type _ A n -> op_type _ B n -> Prop :=
      match n return op_type _ A n -> op_type _ B n -> Prop with
      | constant d => fun o o' => f o == o'
      | function x y => fun o o' => forall x, Preservation (o x) (o' (f x))
      end.

    Class HomoMorphism: Prop :=
      { homo_proper:> forall a, Proper (equiv ==> equiv) (@f a)
      ; preserves: forall (o: sign), Preservation (op o) (op o) }.

    Global Instance Preservation_proper `{HomoMorphism}
      `{!forall a, Equivalence (ea a)} `{!forall a, Equivalence (eb a)} n:
      Proper (op_type_equiv _ A n ==> op_type_equiv _ B n ==> iff) (@Preservation n).
    Proof.
     induction n.
      repeat intro.
      simpl in *. split; intro.
       rewrite <- H2, <- H3. assumption.
      rewrite H2, H3. assumption.
     repeat intro.
     split; simpl; repeat intro;
      apply (IHn (x x1) (y x1) (H2 x1 x1 (reflexivity _)) (x0 (f x1)) (y0 (f x1)) (H3 (f x1) (f x1) (reflexivity _)));
      apply (H4 x1).
    Qed.

  End for_map.

  Section Vars.

    Context (A: sign_atomics sign -> Type) `{e: forall a, Equiv (A a)} `{forall a, Equivalence (e a)}.

    Definition Vars := forall a, nat -> A a.

    Global Instance: Equiv Vars :=
     @pointwise_dependent_relation (sign_atomics sign) (fun a => nat -> A a)
      (fun _ => pointwise_relation _ equiv).

    Global Instance: Equivalence (equiv: relation Vars).

  End Vars.

  Section eval.

    Context 
     `{ea: forall a, Equiv (A a)} `{!forall a, Equivalence (ea a)} `{!Implementation A} `{@Propers A ea _}.

    Fixpoint eval {n: OpType (sign_atomics sign)} (vars: Vars A) (t: Term n) {struct t}:
        op_type _ A n :=
      match t in Term n return op_type _ A n with
      | Var v a => vars a v
      | Op o => op o
      | App n a f p => eval vars f (eval vars p)
      end.

    Let bla := op_type_equiv (sign_atomics sign) A.

    Global Instance eval_proper (n: OpType (sign_atomics sign)):
      Proper (equiv ==> eq ==> equiv) (@eval n).
    Proof with auto.
     do 7 intro. subst.
     induction y0.
       apply H1...
      apply IHy0_1...
     apply propers.
    Qed.

    Definition eval_stmt (vars: Vars A): Statement -> Prop :=
      fix F (s: Statement) :=
      match s with
      | Eq _ a b => eval vars a == eval vars b
      | Impl a b => F a -> F b
      | Ext P => P
      end.

    Global Instance eval_stmt_proper: Proper (equiv ==> eq ==> iff) eval_stmt.
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
      { variety_atomics:> sign_atomics sign -> Type
      ; variety_equiv: forall a, Equiv (variety_atomics a)
      ; variety_op:> Implementation variety_atomics
      ; variety_equivalence: forall a, Equivalence (variety_equiv a)
      ; variety_propers: Propers variety_atomics
      ; variety_laws: forall s, E s -> forall vars: forall a, nat -> variety_atomics a,
          @eval_stmt variety_atomics variety_equiv variety_op vars s
     }.

    Existing Instance variety_equivalence.
    Existing Instance variety_op.
    Existing Instance variety_propers.
    Existing Instance variety_equiv.

    Definition Arrow (X Y: Variety): Type := sig (@HomoMorphism X Y _ _ _ _).

    Global Program Instance: CatId Variety Arrow := fun _ _ => id.

    Next Obligation.
     constructor. intro. apply _.
     unfold id. intro.
     generalize (@op (variety_atomics H) (variety_op H) o). intro.
     induction (sign_sig sign o); simpl; intuition.
    Qed.

    Global Program Instance: CatComp Variety Arrow := fun x y z => fun f g v a => (`f) _ ((`g) v a).

    Next Obligation. Proof with reflexivity.
     destruct f. destruct g.
     constructor. repeat intro. simpl.
      pose proof (@homo_proper x y _ _ _ _ x1 _ a).
      pose proof (@homo_proper y z _ _ _ _ x0 _ a).
      rewrite H...
     intros. simpl.
     generalize (preserves _ _ x1 o) (preserves _ _ x0 o).
     generalize (@op z _ o) (@op y _ o) (@op x _ o).
     induction (sign o); simpl; intros. 
      pose proof (@homo_proper x y _ _ _ _ x1 _ a).
      pose proof (@homo_proper y z _ _ _ _ x0 _ a).
      rewrite H. assumption.
     apply (@IHo0 (o1 (x0 _ (x1 _ x2))) (o2 (x1 _ x2))); auto.
    Qed.

    Global Instance o_equiv: Equiv Variety := eq.

    Global Instance a_equiv (x y: Variety): Equiv (Arrow x y)
      := fun a a' => forall b, pointwise_relation _ equiv (proj1_sig a b) (proj1_sig a' b).

    Global Instance homo_cat: Category Variety Arrow.
    Proof with auto.
     constructor; try apply _.
         intros.
         unfold a_equiv.
         destruct x. destruct y.
         constructor; repeat intro.
           reflexivity.
          symmetry...
          apply H.
         transitivity ((proj1_sig y) b a)...
          apply H.
         apply H0.
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
        pose proof (@homo_proper _ _ _ _ _ _ x _ b).
        rewrite H0.
        apply H.
       intros.
       destruct w. destruct y. destruct z. destruct x. intro. reflexivity.
      intros. destruct x. destruct y. intro. intro. reflexivity.
     intros. destruct x. destruct y. intro. intro. reflexivity.
    Qed.

  End category.

  Section for_isomorphic_implementations.

    Context (A B: sign_atomics sign -> Type)
      `{ea: forall a, Equiv (A a)}
      `{eb: forall a, Equiv (B a)}
      `{forall a, Equivalence (ea a)} `{forall a, Equivalence (eb a)} `{Implementation A} `{Implementation B}
      `{!Propers A} `{!Propers B}
      (ab: forall a, A a -> B a) (ba: forall a, B a -> A a)
      `(@HomoMorphism A B ea eb _ _ ab) `(@HomoMorphism _ _ _ _ _ _ ba)
      (iso_l: forall a x, ba a (ab a x) == x) (iso_r: forall a x, ab a (ba a x) == x).

    Implicit Arguments ab [[a]].
    Implicit Arguments ba [[a]].

      (* Let us help out poor old instance resolution a bit: *)
    Let ab_proper := homo_proper A B (@ab).
    Let ba_proper:= homo_proper B A (@ba).
    Let eval_proper_a := @eval_proper A ea H1 Propers0.
    Let eval_proper_b := @eval_proper B eb H2 Propers1.

    Lemma iso_vars_l (v: Vars A): v == (fun _ i => ba (ab (v _ i))).
    Proof. repeat intro. rewrite iso_l. reflexivity. Qed.

    Lemma iso_vars_r (v: Vars B): v == (fun _ i => ab (ba (v _ i))).
    Proof. repeat intro. rewrite iso_r. reflexivity. Qed.

    (* Evaluating a term in one implementation is "the same" as evaluating it in the other. *)

    Instance blaya o: Equiv (op_type (sign_atomics sign) A o) :=
      op_type_equiv (sign_atomics sign) A o.
    Instance blaya' o: Equiv (op_type (sign_atomics sign) B o) :=
      op_type_equiv (sign_atomics sign) B o.

    Instance: Transitive (blaya o).
    Proof. intro. apply _. Qed. (* this really shouldn't be necessary *)

    Lemma carry_eval n (t: Term n) (v: Vars B): 
      @eval A _ _ (fun _ i => ba (v _ i)) t == map_op _ (@ba) (@ab) (eval v t).
    Proof with auto.
     induction t; simpl in *; intros.
       reflexivity.
      set (eval (fun (a : sign_atomics sign) (i : nat) => ba (v a i)) t2).
      pose proof (@eval_proper A ea H1 Propers0 (function (sign_atomics sign) y t1) (fun a i => ba (v a i))
        (fun a i => ba (v a i)) (reflexivity _) t2 t2 (reflexivity _): 
          Proper (ea y ==> op_type_equiv (sign_atomics sign) A t1)%signature o).
      rewrite (IHt2 v).
      subst o.
      pose proof (IHt1 v (ba (eval v t3)) (ba (eval v t3))).
      simpl in H6.
      rewrite H6.
       set (homo_proper A B (@ab)).
       set (homo_proper B A (@ba)).
       set (@map_op_proper (sign_atomics sign) B A _ _ (@ba) (@ab) p0 p).
       unfold equiv.
       apply (@map_op_proper (sign_atomics sign) B A _ _ (@ba) (@ab))...
       pose proof (@eval_proper B eb H2 Propers1 _ v v (reflexivity _) t2 t2 (reflexivity _): Proper equiv (eval v t2)).
       rewrite (iso_r _ (eval v t3)).
       apply sig_type_refl...
       intro. apply _.
      reflexivity.
     pose proof (@propers A _ _ _ o).
     pose proof (@propers B _ _ _ o).
     pose proof (@preserves A B _ _ _ _ (@ab) _ o).
     revert H5 H6 H7.
     clear v.
     generalize (@op A H1 o) (@op B H2 o).
     induction (sign o).
      simpl.
      intros.
      rewrite <- iso_l.
      pose proof (@homo_proper B A _ _ _ _ (@ba) _ a (ab o0) o1).
      apply H8 in H7.
      assumption. (* weird *)
     simpl.
     unfold Proper. unfold respectful.
     repeat intro.
     unfold blaya.
     apply IHo0.
       apply H5. reflexivity.
      apply H6. reflexivity.
     assert (op_type_equiv (sign_atomics sign) A o0 (o1 x) (o1 y)).
      apply H5. assumption.
     apply (@Preservation_proper A B ea eb H1 H2 (@ab) H3 _ _ o0 (o1 x) (o1 y) H9 (o2 (ab y)) (o2 (ab y)))...
     change (o2 (ab y) == o2 (ab y)).
     apply H6.
     reflexivity.
    Qed. (* todo: clean up *)

    (* Similarly, evaluating a statement in one implementation is "the same" as evaluating it in the other. *)

    Lemma carry_stmt_with (s: Statement) (v: Vars A):
      eval_stmt v s <-> @eval_stmt B _ _ (fun _ i => ab (v _ i)) s.
    Proof with auto.
     intros.
     induction s; simpl.
       split; intros.
        rewrite <- (iso_r _ (eval (fun a0 i => ab (v a0 i)) a)).
        rewrite <- (iso_r _ (eval (fun a0 i => ab (v a0 i)) b)).
        rewrite <- (carry_eval _ a (fun d i => ab (v d i))).
        rewrite <- (carry_eval _ b (fun d i => ab (v d i))).
        rewrite <- iso_vars_l.
        rewrite H5.
        reflexivity.
       rewrite iso_vars_l.
       do 2 rewrite carry_eval.
       simpl. rewrite H5. reflexivity.
      firstorder.
     intuition.
    Qed.

    Lemma carry_stmt (s: Statement): (forall v, @eval_stmt A _ _ v s) -> (forall v, @eval_stmt B _ _ v s).
    Proof. intros. rewrite iso_vars_r. rewrite <- carry_stmt_with. apply H5. Qed.

  End for_isomorphic_implementations.

End for_signature.

Existing Instance variety_op.
Existing Instance variety_equivalence.
Existing Instance variety_equiv.
Existing Instance variety_propers.

Module op_type_notations.
  Global Infix "-=>" := (function _) (at level 95, right associativity).
End op_type_notations.

Module notations.
  Global Infix "===" := (Eq _ _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
