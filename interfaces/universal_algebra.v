Set Automatic Introduction.

Require Import
  Morphisms Setoid Program List
  abstract_algebra theory.categories util.

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

  Definition prop (T : Atomic -> Type) (P : forall a : Atomic, T a -> Prop) :=
    fix F (o0 : OpType) : op_type T o0 -> Prop :=
      match o0 with
      | constant a => P a
      | function a g => fun X => forall x, F g (X x)
      end.

  Definition gen_op_type (Arg Res: Atomic -> Type): OpType -> Type :=
    fix F (t: OpType): Type :=
      match t with
      | constant a => Res a
      | function a g => Arg a -> F g
      end. (* used in initiality proof for w *)

  Section with_atomic_inter. Variable T: Atomic -> Type.

    Definition op_type_equiv
       `{e: forall A, Equiv (T A)}: forall o: OpType, Equiv (op_type T o) :=
     fix F (o: OpType): Equiv (op_type T o) :=
      match o return Equiv (op_type T o) with
      | constant A => e A
      | function A g => (e A ==> F g)%signature
      end.

    Definition gen_op_type_equiv (T': Atomic -> Type)
       `{e: forall A, Equiv (T A)}
       (he: forall A, T A -> T' A -> Prop) :=
     fix F (o: OpType): op_type T o -> gen_op_type T T' o -> Prop :=
      match o return op_type T o -> gen_op_type T T' o -> Prop with
      | constant A => he A
      | function A g => fun x y => forall i j, i == j -> F g (x i) (y j) (*(e A ==> F g)%signature*)
      end.

    Definition gen_op_type_equiv' (T': Atomic -> Type)
       `{e: forall A, Equiv (T A)}
       (he: forall A, T A -> T' A -> Prop) :=
     fix F (o: OpType): op_type T o -> gen_op_type T' T o -> Prop :=
      match o return op_type T o -> gen_op_type T' T o -> Prop with
      | constant A => e A
      | function A g => fun x y => forall i j, he _ i j -> F g (x i) (y j) (*(e A ==> F g)%signature*)
      end.

    Global Existing Instance op_type_equiv.

    (* op_type_equiv is /almost/ an equivalence relation. Note that it is /not/ readily reflexive. *)

    Global Instance sig_type_trans `{e: forall A, Equiv (T A)}
      `{forall A, Reflexive (e A)} `{forall A, Transitive (e A)}: Transitive (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.

      (* curiously, having symmetry is also sufficient enough to get transitivity: *)
    Global Instance sig_type_trans' `{e: forall A, Equiv (T A)}
       `{forall A, Symmetric (e A)}
       `{forall A, Transitive (e A)}: Transitive (op_type_equiv o).
    Proof.
     induction o.
     apply H0.
     repeat intro.
     transitivity (y y0). apply (H1 x0 _ H3).
     apply H2.
     transitivity x0; [symmetry |]; assumption.
    Qed.

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

  Context {A B: Atomic -> Type} {e: forall a, Equiv (B a)} `{forall b, Equivalence (e b)} 
   (ab: forall a, A a -> B a) (ba: forall a, B a -> A a) 
   `(iso: forall a (x: B a), ab a (ba a x) == x).

  Lemma map_iso o (x: op_type B o) (xproper: Proper equiv x): map_op ab ba (map_op ba ab x) == x.
  Proof with auto; try reflexivity.
   induction o; simpl; intros...
   repeat intro.
   change (map_op ab ba (map_op ba ab (x (ab a (ba a x0)))) == x y).
   transitivity (x (ab a (ba a x0))).
    apply IHo, xproper...
   apply xproper. rewrite iso, H0...
  Qed.

End with_atomic.

Inductive Signature: Type :=
  { sign_op:> Set
  ; sign_atomics: Set
  ; sign_sig:> sign_op -> OpType sign_atomics }.

Section for_signature. Variable sign: Signature.

  Class Implementation (A: sign_atomics sign -> Type) := op: forall o, op_type _ A (sign o).

  Class Propers (A: sign_atomics sign -> Type) `{forall a, Equiv (A a)} `{Implementation A} :=
    propers:> forall o: sign, Proper (op_type_equiv _ A (sign o)) (op o).

  Inductive Term (V: Set): OpType (sign_atomics sign) -> Set :=
    | Var (v: V) (a: sign_atomics sign): Term V (constant _ a)
    | App (t: OpType (sign_atomics sign)) y: Term V (function _ y t) -> Term V (constant _ y) -> Term V t
    | Op (o: sign): Term V (sign o).

  Implicit Arguments Var [[V]].

  Let T := Term nat.
  Definition Identity t := prod (T t) (T t).
  Definition Term0 sort := T (constant _ sort).
  Definition Identity0 sort := Identity (constant _ sort).
    (* While Identity0 is the one we usually have in mind, the generalized version for arbitrary op_types
     is required to make induction proofs work. The same is (more or less) true for Term/Term0. *)

  Definition mkIdentity0 {sort}: T (constant _ sort) -> T (constant _ sort) -> Identity0 sort := pair.

  Inductive Statement: Type :=
    | Eq t (i: Identity t)
    | Impl (a b: Statement)
    | Conj (a b: Statement)
    | Ext (P: Prop).

  (* Note: The statements above are too liberal (i.e. not equational) to support product varieties. *)

  Record Entailment (P: Type): Type := { entailment_premises: list P; entailment_conclusion: P }.

  Definition EqEntailment := Entailment (sigT Identity0).

  Definition identity_as_eq (s: sigT Identity0): Statement := Eq _ (projT2 s).
  Coercion identity_as_entailment sort (e: Identity0 sort): EqEntailment := Build_Entailment _ nil (existT _ _ e).

  Coercion entailment_as_statement (e: EqEntailment): Statement :=
     (fold_right Impl (identity_as_eq (entailment_conclusion _ e)) (map identity_as_eq (entailment_premises _ e))).

  Definition boring_entailment_as_statement (e: EqEntailment): Statement :=
    Impl (fold_right Conj (Ext True) (map identity_as_eq (entailment_premises _ e))) 
      (identity_as_eq (entailment_conclusion _ e)).


  Fixpoint propje V (P: forall a, Term V (constant _ a) -> Prop) {ot}: Term V ot -> Prop :=
    match ot with
    | constant x => P x
    | function x y => fun z => forall v, P _ v -> propje V P (App V _ _ z v)
    end.

  Lemma indu V (P: forall a, Term V (constant _ a) -> Prop):
    (forall o a (t: Term V (constant _ a)) (t0: Term V (function (sign_atomics sign) a o)),
       P _ t -> propje V P t0 -> propje V P (App _ _ _ t0 t)) ->
    (forall v a, P _ (Var v a)) ->
    (forall o, propje V P (Op _ o)) ->
    forall a (t: Term V (constant _ a)), P a t.
  Proof.
   intros.
   cut (propje V P t). intuition.
   induction t; simpl; intuition.
  Qed.
    (* Todo: Rename and explain propje/indu. *)

  Section for_map.

    Context (A: sign_atomics sign -> Type) (B: sign_atomics sign -> Type)
      `{ea: forall a, Equiv (A a)} `{eb: forall a, Equiv (B a)}
      `{!Implementation A} `{!Implementation B} (f: forall a, A a -> B a).

    Implicit Arguments f [[a]].

    Fixpoint Preservation {n: OpType (sign_atomics sign)}: op_type _ A n -> op_type _ B n -> Prop :=
      match n with
      | constant d => fun o o' => f o == o'
      | function x y => fun o o' => forall x, Preservation (o x) (o' (f x))
      end.

    Class HomoMorphism: Prop :=
      { homo_proper:> forall a, Setoid_Morphism (@f a)
      ; preserves: forall (o: sign), Preservation (op o) (op o) }.

    Global Instance Preservation_proper `{HomoMorphism}
      `{!forall a, Equivalence (ea a)} `{!forall a, Equivalence (eb a)} n:
      Proper (op_type_equiv _ A n ==> op_type_equiv _ B n ==> iff) (@Preservation n).
    Proof with auto.
     induction n; simpl; intros x y E x' y' E'.
      split; intro F. rewrite <- E, <- E'... rewrite E, E'...
     split; simpl; intros; apply (IHn _ _ (E _ _ (reflexivity _)) _ _ (E' _ _ (reflexivity _)))...
    Qed.

  End for_map.

  Section Vars.

    Context (A: sign_atomics sign -> Type) (V: Set) `{e: forall a, Equiv (A a)} `{forall a, Equivalence (e a)}.

    Definition Vars := forall a, V -> A a.

    Global Instance: Equiv Vars :=
     @pointwise_dependent_relation (sign_atomics sign) (fun a => V -> A a)
      (fun _ => pointwise_relation _ equiv).

    Global Instance: Equivalence (equiv: relation Vars).

  End Vars.

  Section eval.

    Context
     `{ea: forall a, Equiv (A a)} `{!forall a, Equivalence (ea a)} `{!Implementation A} `{@Propers A ea _}.

    Fixpoint eval {V} {n: OpType (sign_atomics sign)} (vars: Vars A V) (t: Term V n) {struct t}:
        op_type _ A n :=
      match t in Term _ n return op_type _ A n with
      | Var v a => vars a v
      | Op o => op o
      | App n a f p => eval vars f (eval vars p)
      end.
 
    Let bla := op_type_equiv (sign_atomics sign) A.

    Global Instance eval_proper {V} (n: OpType (sign_atomics sign)):
      Proper (equiv ==> eq ==> equiv) (@eval V n).
    Proof with auto.
     intros x y E a _ [].
     induction a.
       apply E...
      apply IHa1...
     apply propers.
    Qed.

    Definition eval_stmt (vars: Vars A nat): Statement -> Prop :=
      fix F (s: Statement) :=
      match s with
      | Eq _ i => eval vars (fst i) == eval vars (snd i)
      | Impl a b => F a -> F b
      | Ext P => P
      | Conj a b => F a /\ F b
      end.

    Global Instance eval_stmt_proper: Proper (equiv ==> eq ==> iff) eval_stmt.
    Proof with auto.
     intros v v' ve s s' se. subst.
     induction s'; simpl; intuition.
      transitivity (eval v (fst i)).
       rewrite <- ve.
       unfold equiv.
       unfold bla.
       apply eval_proper...
       reflexivity.
      transitivity (eval v (snd i))...
      apply eval_proper...
     transitivity (eval v' (fst i)).
      apply eval_proper...
     rewrite H1.
     apply eval_proper...
     symmetry...
    Qed. (* todo: clean up *)

    Definition boring_eval_entailment (vars: Vars A nat) (e: EqEntailment):
      eval_stmt vars e <-> eval_stmt vars (boring_entailment_as_statement e).
    Proof. destruct e. simpl. induction entailment_premises0; simpl; intuition. Qed.

  End eval.

End for_signature.

Record EquationalTheory :=
  { et_sig:> Signature
  ; et_laws:> EqEntailment et_sig -> Prop }.

Record Variety (et: EquationalTheory): Type := MkVariety
  { variety_atomics:> sign_atomics et -> Type
  ; variety_equiv: forall a, Equiv (variety_atomics a)
  ; variety_op:> Implementation et variety_atomics
  ; variety_equivalence: forall a, Equivalence (variety_equiv a)
  ; variety_propers: Propers et variety_atomics
  ; variety_laws: forall s: EqEntailment et, et_laws et s -> forall vars: forall a, nat -> variety_atomics a,
      @eval_stmt et variety_atomics variety_equiv variety_op vars s
 }.

Existing Instance variety_equivalence.
Existing Instance variety_op.
Existing Instance variety_propers.
Existing Instance variety_equiv.

Module op_type_notations.
  Global Infix "-=>" := (function _) (at level 95, right associativity).
End op_type_notations.

Module notations.
  Global Infix "===" := (mkIdentity0 _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
