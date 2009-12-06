Require Import
  Morphisms Setoid abstract_algebra Program util.

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

    (* op_type_equiv is /almost/ an equivalence relation. Note that it is /not/ readily reflexive. *)

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

Existing Instance op_type_equiv.

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

  Inductive Statement: Type :=
    | Eq t (a b: Term (constant _ t))
    | Impl (a b: Statement)
    | Conj (a b: Statement)
    | Ext (P: Prop).

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
    Proof with auto.
     induction n; simpl; intros x y E x' y' E'.
      split; intro F. rewrite <- E, <- E'... rewrite E, E'...
     split; simpl; intros; apply (IHn _ _ (E _ _ (reflexivity _)) _ _ (E' _ _ (reflexivity _)))...
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
     intros n x y E a _ [].
     induction a.
       apply E...
      apply IHa1...
     apply propers.
    Qed.

    Definition eval_stmt (vars: Vars A): Statement -> Prop :=
      fix F (s: Statement) :=
      match s with
      | Eq _ a b => eval vars a == eval vars b
      | Impl a b => F a -> F b
      | Ext P => P
      | Conj a b => F a /\ F b
      end.

    Global Instance eval_stmt_proper: Proper (equiv ==> eq ==> iff) eval_stmt.
    Proof with auto.
     intros v v' ve s s' se. subst.
     induction s'; simpl; intuition.
      rewrite <- ve...
     rewrite ve...
    Qed.

  End eval.

End for_signature.

Record EquationalTheory :=
  { et_sig:> Signature
  ; et_laws:> Statement et_sig -> Prop }.

Section for_equational_theory. Variable et: EquationalTheory.

  Record Variety: Type := MkVariety
    { variety_atomics:> sign_atomics et -> Type
    ; variety_equiv: forall a, Equiv (variety_atomics a)
    ; variety_op:> Implementation et variety_atomics
    ; variety_equivalence: forall a, Equivalence (variety_equiv a)
    ; variety_propers: Propers et variety_atomics
    ; variety_laws: forall s, et_laws et s -> forall vars: forall a, nat -> variety_atomics a,
        @eval_stmt et variety_atomics variety_equiv variety_op vars s
   }.

  Existing Instance variety_equivalence.
  Existing Instance variety_op.
  Existing Instance variety_propers.
  Existing Instance variety_equiv.

  Definition Arrow (X Y: Variety): Type :=
    sig (@HomoMorphism et X Y (variety_equiv X) (variety_equiv Y) _ _).

  Global Program Instance: CatId Variety Arrow := fun _ _ => id.

  Next Obligation.
   constructor. intro. apply _.
   unfold id. intro.
   generalize (@op et (variety_atomics H) (variety_op H) o). intro.
   induction (sign_sig et o); simpl; intuition.
  Qed.

  Global Program Instance: CatComp Variety Arrow := fun x y z => fun f g v a => (`f) _ ((`g) v a).

  Next Obligation. Proof with reflexivity.
   destruct f. destruct g.
   constructor; repeat intro; simpl.
    pose proof (@homo_proper et x y (variety_equiv x) (variety_equiv y) _ _ x1 _ a).
    pose proof (@homo_proper et y z (variety_equiv y) (variety_equiv z) _ _ x0 _ a).  
    rewrite H... 
   generalize (@preserves et (variety_atomics x) (variety_atomics y) (variety_equiv x) (variety_equiv y) _ _ x1 h0 o).
   generalize (@preserves et (variety_atomics y) (variety_atomics z) (variety_equiv y) (variety_equiv z) _ _ x0 h o).
   generalize (@op _ z _ o) (@op _ y _ o) (@op _ x _ o).
   induction (et o); simpl; intros.
    pose proof (@homo_proper _ x y (variety_equiv x) (variety_equiv y) _ _ x1 _ a).
    pose proof (@homo_proper _ y z (variety_equiv y) (variety_equiv z) _ _ x0 _ a).
    rewrite H0. assumption.
   apply (@IHo0 (o1 (x0 _ (x1 _ x2))) (o2 (x1 _ x2))); auto.
  Qed.

  Global Instance o_equiv: Equiv Variety := eq.

  Global Instance a_equiv (x y: Variety): Equiv (Arrow x y)
    := fun a a' => forall b, pointwise_relation _ equiv (proj1_sig a b) (proj1_sig a' b).

  Global Instance homo_cat: Category Variety Arrow.
  Proof with auto.
   constructor; try apply _; intros.
       unfold a_equiv.
       destruct x. destruct y.
       constructor; repeat intro.
         reflexivity.
        symmetry...
        apply H.
       unfold pointwise_relation in *.
       transitivity (proj1_sig y b a)...
      repeat intro.
      simpl.
      destruct x. destruct y. destruct z. destruct x0. destruct y0. destruct x1. destruct y1.
      unfold equiv, a_equiv, pointwise_relation in *.
      simpl in *.
      intros.
      pose proof (@homo_proper _ _ _ _ _ _ _ x _ b).
      rewrite H0.
      apply H.
     destruct w. destruct y. destruct z. destruct x. intro. reflexivity.
    destruct x. destruct y. intro. intro. reflexivity.
   destruct x. destruct y. intro. intro. reflexivity.
  Qed.

End for_equational_theory.

Existing Instance variety_equivalence.
Existing Instance variety_op.
Existing Instance variety_propers.
Existing Instance variety_equiv.

Module op_type_notations.
  Global Infix "-=>" := (function _) (at level 95, right associativity).
End op_type_notations.

Module notations.
  Global Infix "===" := (Eq _ _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
