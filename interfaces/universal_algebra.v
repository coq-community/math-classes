Set Automatic Introduction.

Require Import
  Morphisms Setoid Program List
  abstract_algebra theory.categories util.

Record Entailment (P: Type): Type := { entailment_premises: list P; entailment_conclusion: P }.

Section with_sorts. Variable Sorts: Set.

  (* For single-sorted algebras, Sorts will typically be unit. *)

  (* OpType describes the type of an operation in an algebra. Note that higher order function types are excluded: *)

  Inductive OpType: Set :=
    | constant (a: Sorts)
    | function (a: Sorts) (g: OpType).

  Section with_sort_realizations. Variable Sort: Sorts -> Type.

    (* Given a Type for each sort, we can map the operation type descriptions to real function types: *)

    Fixpoint op_type (o: OpType): Type :=
      match o with
      | constant a => Sort a
      | function a g => Sort a -> op_type g
      end.

    (* We use extensional equivalence for such generated function types: *)

    Context `{e: forall s, Equiv (Sort s)}.

    Fixpoint op_type_equiv o: Equiv (op_type o) :=
      match o with
      | constant A => e A
      | function A g => (e A ==> op_type_equiv g)%signature
      end.

    Global Existing Instance op_type_equiv. (* There's no [Global Instance Fixpoint]. *)

    Global Instance sig_type_sym `{forall s, Symmetric (e s)}: Symmetric (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.
    
    (* We need either reflexivity or symmetry of e in order to get transitivity of op_type_equiv: *)

    Global Instance sig_type_trans `{forall s, Reflexive (e s)} `{forall s, Transitive (e s)}: Transitive (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.

    Global Instance sig_type_trans' `{forall s, Symmetric (e s)} `{forall s, Transitive (e s)}: Transitive (op_type_equiv o).
    Proof with auto.
     induction o; simpl...
     intros x y ? ? H2 x0 y0 ?.
     transitivity (y y0)...
     apply H2.
     transitivity x0; [symmetry |]...
    Qed.

      (* This is the closest i've been able to get to reflexivity thus far: *)
    Lemma sig_type_refl `{forall a, Reflexive (e a)} (o: OpType) a (x: op_type (function a o)) y:
      Proper equiv x ->
      op_type_equiv o (x y) (x y).
    Proof. intro H0. apply H0. reflexivity. Qed.

  End with_sort_realizations.

  Section map_op.

    (* Given maps between two realizations of the sorts, there are maps between the corresponding op_types*)

    Context {A B: Sorts -> Type}
      `{forall a, Equiv (A a)} `{forall a, Equiv (B a)}
      (ab: forall a, A a -> B a)
      (ba: forall a, B a -> A a)
      `{forall a, Proper (equiv ==> equiv) (ab a)}
      `{forall a, Proper (equiv ==> equiv) (ba a)}.

    Fixpoint map_op {o: OpType}: op_type A o -> op_type B o :=
      match o return op_type A o -> op_type B o with
      | constant u => ab u
      | function _ _ => fun x y => map_op (x (ba _ y))
      end.

    Global Instance map_op_proper o: Proper (op_type_equiv A o ==> op_type_equiv B o) (@map_op o).
    Proof. induction o; simpl; firstorder. Qed.
      (* todo: can't we make this nameless? *)

  End map_op.

  (* If the maps between the sorts are eachother's inverse, then so are the two generated op_type maps: *)

  Context {A B: Sorts -> Type} {e: forall a, Equiv (B a)} `{forall b, Equivalence (e b)} 
   (ab: forall a, A a -> B a) (ba: forall a, B a -> A a) 
   `(iso: forall a (x: B a), ab a (ba a x) == x).

  Lemma map_iso o (x: op_type B o) (xproper: Proper equiv x): map_op ab ba (map_op ba ab x) == x.
  Proof with auto; try reflexivity.
   induction o; simpl; intros...
   intros x0 y H0.
   change (map_op ab ba (map_op ba ab (x (ab a (ba a x0)))) == x y).
   transitivity (x (ab a (ba a x0))).
    apply IHo, xproper...
   apply xproper. rewrite iso, H0...
  Qed.

End with_sorts.

Inductive Signature: Type :=
  { sorts: Set
  ; operation:> Set
  ; operation_type:> operation -> OpType sorts }.

(* We now introduce additional things in order to let us eventually define equational theories and varieties. *)

Section for_signature. Variable sign: Signature.

  Let sorts := sorts sign.
  Let OpType := OpType sorts.

  (* An implementation of a signature for a given realization of the sorts is simply a function (of the right type) for each operation: *)

  Class Implementation (A: sorts -> Type) := op: forall o, op_type _ A (sign o).

  (* And we'll usually want to work with proper implementations: *)

  Class Propers (A: sorts -> Type) `{forall a, Equiv (A a)} `{Implementation A} :=
    propers:> forall o: sign, Proper equiv (op o). (* This equiv is op_type_equiv defined above. *)

  (* As an aside: given two implementations in different realizations of the sorts, and a map between
   them for each sort, we can say what it means for that map to preserve the algebra's operations,
   i.e. what it takes for it to be a homomorphism: *)

  Section for_map.

    Context (A B: sorts -> Type)
      `{ea: forall a, Equiv (A a)} `{eb: forall a, Equiv (B a)}
      `{!Implementation A} `{!Implementation B} (f: forall a, A a -> B a).

    Implicit Arguments f [[a]].

    Fixpoint Preservation {n: OpType}: op_type _ A n -> op_type _ B n -> Prop :=
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

  (* Proceeding on our way toward equational theories and varieties, we define terms: *)

  Inductive Term (V: Set): OpType -> Set :=
    | Var (v: V) (a: sorts): Term V (constant _ a)
    | App (t: OpType) y: Term V (function _ y t) -> Term V (constant _ y) -> Term V t
    | Op (o: sign): Term V (sign o).

  Implicit Arguments Var [[V]].

  (* Term has OpType as an index, which means we can have terms with function
   types (no surprise there). However, often we want to prove properties that only speak of
   terms of arity 0 (that is, terms of type [Term (constant _ sort)] for some sort): *)

  Definition Term0 v sort := Term v (constant _ sort).

  Section applications_ind.

    Context (V: Set) (P: forall a, Term0 V a -> Prop).

    (* To be able to prove such a P by induction, we must first transform it into a statement
     about terms of all arities. Roughly speaking, we do this by saying
     [forall x0...xN, P (App (... (App f x0) ...) xN)] for a term f of arity N. *)

    Fixpoint applications {ot}: Term V ot -> Prop :=
      match ot with
      | constant x => P x
      | function x y => fun z => forall v, P _ v -> applications (App V _ _ z v)
      end.

    (* To prove P/applications by induction, we can then use: *)

    Lemma applications_ind:
      (forall o a t t', P a t -> applications t' -> applications (App _ o a t' t)) ->
      (forall v a, P _ (Var v a)) ->
      (forall o, applications (Op _ o)) ->
      forall a t, P a t.
    Proof with intuition. intros. cut (applications t)... induction t; simpl... Qed.

  End applications_ind.

  (* We parameterized Term over the index set for variables, because we will
   wants terms /with/ variables when speaking of identities in equational theories,
   but will want terms /without/ variables when constructing initial objects
   in variety categories generically in theory/ua_initial (which we get by taking
   False as the variable index set). *)
   
  Definition T := Term nat.
  Definition T0 := Term0 nat.

  Definition Identity t := prod (T t) (T t).
  Definition Identity0 sort := Identity (constant _ sort).
    (* While Identity0 is the one we usually have in mind, the generalized version for arbitrary op_types
     is required to make induction proofs work. *)

  Definition mkIdentity0 {sort}: T (constant _ sort) -> T (constant _ sort) -> Identity0 sort := pair.

  (* The laws in an equational theory will be entailments of identities for any of the sorts: *)

  Definition EqEntailment := Entailment (sigT Identity0).

  (* We also introduce a more general class of statements that we use to conveniently transfer
   statements between different models of a variety: *)

  Inductive Statement: Type :=
    | Eq t (i: Identity t)
    | Impl (a b: Statement)
    | Conj (a b: Statement)
    | Ext (P: Prop).

  (* Statements are a strict generalization of EqEntailments. We cannot use the former for the laws,
   though, because they are too liberal (i.e. not equational) to support product varieties.
   We do have two injections: *)

  Definition identity_as_eq (s: sigT Identity0): Statement := Eq _ (projT2 s).
  Coercion identity_as_entailment sort (e: Identity0 sort): EqEntailment := Build_Entailment _ nil (existT _ _ e).

  Coercion entailment_as_statement (e: EqEntailment): Statement :=
     (fold_right Impl (identity_as_eq (entailment_conclusion _ e)) (map identity_as_eq (entailment_premises _ e))).

  Definition entailment_as_conjunctive_statement (e: EqEntailment): Statement :=
    Impl (fold_right Conj (Ext True) (map identity_as_eq (entailment_premises _ e))) 
      (identity_as_eq (entailment_conclusion _ e)).

  (* The first one (the coercion) converts an entailment of the form (A, B, C |- D) into a statement of
   the form (A -> B -> C -> D), while the second converts the same entailment into a statement of
   the form ((A /\ B /\ C) -> D). Both have their uses in induction proofs. *)

  (* To be able to state that laws hold in a model of a variety, we must be able to evaluate terms
   using the model's implementation and using arbitrary variable assignments: *)

  Section Vars.

    Context (A: sorts -> Type) (V: Set) `{e: forall a, Equiv (A a)} `{forall a, Equivalence (e a)}.

    Definition Vars := forall a, V -> A a.

    Global Instance: Equiv Vars :=
     @pointwise_dependent_relation sorts (fun a => V -> A a)
      (fun _ => pointwise_relation _ equiv).

    Global Instance: Equivalence (equiv: relation Vars).

  End Vars.

  Definition no_vars x: Vars x False := fun _ => False_rect _.

  (* Given an assignment mapping variables to closed terms, we can close open terms: *)

  Fixpoint close {V} {o} (v: Vars (fun x => Term False (constant _ x)) V) (t: Term V o): Term False o :=
    match t in Term _ o return Term False o with
    | Var x y => v y x
    | App x y z r => App _ x y (close v z) (close v r)
    | Op o => Op _ o
    end.

  Section eval.

    Context
     `{ea: forall a, Equiv (A a)} `{!forall a, Equivalence (ea a)} `{!Implementation A} `{@Propers A ea _}.

    Fixpoint eval {V} {n: OpType} (vars: Vars A V) (t: Term V n) {struct t}: op_type _ A n :=
      match t in Term _ n return op_type _ A n with
      | Var v a => vars a v
      | Op o => op o
      | App n a f p => eval vars f (eval vars p)
      end.
 
    Global Instance eval_proper {V} (n: OpType):
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
       apply eval_proper... symmetry...
      transitivity (eval v (snd i))...
      apply eval_proper...
     transitivity (eval v' (fst i)).
      apply eval_proper...
     rewrite H1.
     apply eval_proper... symmetry...
    Qed.

    Definition boring_eval_entailment (vars: Vars A nat) (e: EqEntailment):
      eval_stmt vars e <-> eval_stmt vars (entailment_as_conjunctive_statement e).
    Proof. destruct e. simpl. induction entailment_premises0; simpl; intuition. Qed.

  End eval.

End for_signature.

(* And with that, we define equational theories and varieties: *)

Record EquationalTheory :=
  { et_sig:> Signature
  ; et_laws:> EqEntailment et_sig -> Prop }.

Record Variety (et: EquationalTheory): Type := MkVariety
  { variety_atomics:> sorts et -> Type
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
