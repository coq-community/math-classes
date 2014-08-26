Require
  theory.setoids ne_list.
Require Import
  List
  abstract_algebra util jections.
Require Export
  ua_basic.

Section for_signature.
  Variable σ: Signature.

  Notation OpType := (OpType (sorts σ)).

  Inductive Term (V: Type): OpType → Type :=
    | Var: V → ∀ a, Term V (ne_list.one a)
    | App t y: Term V (ne_list.cons y t) → Term V (ne_list.one y) → Term V t
    | Op o: Term V (σ o).

  Arguments Var {V} _ _.

  Fixpoint map_var `(f: V → W) `(t: Term V o): Term W o :=
    match t in Term _ o return Term W o with
    | Var v s => Var (f v) s
    | App _ _ _ x y => App _ _ _ (map_var f x) (map_var f y)
    | Op _ s => Op _ s
    end.

  (* Term has OpType as an index, which means we can have terms with function
   types (no surprise there). However, often we want to prove properties that only speak
   of nullary terms: *)

  Definition Term0 v sort := Term v (ne_list.one sort).

  Section applications_ind.
    Context V (P: ∀ {a}, Term0 V a → Type).

    Arguments P {a} _.

    (* Proving such properties for nullary terms directly using Term's induction principle is
    problematic because it requires a property over terms of /any/ arity. Hence, we must first
     transform P into a statement about terms of all arities. Roughly speaking, we do this by
     saying [∀ x0...xN, P (App (... (App f x0) ...) xN)] for a term f of arity N. *)

    Fixpoint applications {ot}: Term V ot → Type :=
      match ot with
      | ne_list.one x => @P x
      | ne_list.cons x y => λ z, ∀ v, P v → applications (App V _ _ z v)
      end.

    (* To prove P/applications by induction, we can then use: *)

    Lemma applications_rect:
      (∀ v a, P (Var v a)) →
      (∀ o, applications (Op _ o)) →
      (∀ a (t: Term0 V a), P t).
    Proof.
     intros X0 X1 ??.
     cut (applications t).
      intros. assumption.
     induction t; simpl.
       apply X0.
      apply IHt1; exact IHt2.
     apply X1.
    Defined. (* todo: write as term *)

  End applications_ind.

  (* We parameterized Term over the index set for variables, because we will
   wants terms /with/ variables when speaking of identities in equational theories,
   but will want terms /without/ variables when constructing initial objects
   in variety categories generically in theory/ua_initial (which we get by taking
   False as the variable index set). *)

  Definition T := Term nat.
  Definition T0 := Term0 nat.

  Definition Identity t := prod (T t) (T t).
  Definition Identity0 sort := Identity (ne_list.one sort).
    (* While Identity0 is the one we usually have in mind, the generalized version for arbitrary op_types
     is required to make induction proofs work. *)

  Definition mkIdentity0 {sort}: T (ne_list.one sort) → T (ne_list.one sort) → Identity0 sort := pair.

  (* The laws in an equational theory will be entailments of identities for any of the sorts: *)

  Record Entailment (P: Type): Type := { entailment_premises: list P; entailment_conclusion: P }.

  Definition EqEntailment := Entailment (sigT Identity0).

  (* We also introduce a more general class of statements that we use to conveniently transfer
   statements between different models of a variety: *)

  Inductive Statement: Type :=
    | Eq t (i: Identity t)
    | Impl (a b: Statement)
    | Conj (a b: Statement)
    | Disj (a b: Statement)
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
   the form (A → B → C → D), while the second converts the same entailment into a statement of
   the form ((A ∧ B ∧ C) → D). Both have their uses in induction proofs. *)

  (* To be able to state that laws hold in a model of a variety, we must be able to evaluate terms
   using the model's implementation and using arbitrary variable assignments: *)

  Section Vars.
    Context (A: sorts σ → Type) (V: Type) `{e: ∀ a, Equiv (A a)} `{∀ a, Equivalence (e a)}.

    Definition Vars := ∀ a, V → A a.

    Global Instance ua_vars_equiv: Equiv Vars :=
     @pointwise_dependent_relation (sorts σ) (λ a, V → A a)
      (λ _, pointwise_relation _ (=)).

    Global Instance: Equivalence ((=): relation Vars) := {}.
  End Vars.

  Definition no_vars x: Vars x False := λ _, False_rect _.

  (* Given an assignment mapping variables to closed terms, we can close open terms: *)

  Fixpoint close {V} {o} (v: Vars (λ x, Term False (ne_list.one x)) V) (t: Term V o): Term False o :=
    match t in Term _ o return Term False o with
    | Var x y => v y x
    | App _ x y z r => App _ x y (close v z) (close v r)
    | Op _ o => Op _ o
    end.

  Section eval.
    Context `{Algebra σ A}.

    Fixpoint eval {V} {n: OpType} (vars: Vars A V) (t: Term V n) {struct t}: op_type A n :=
      match t with
      | Var v a => vars a v
      | Op _ o => algebra_op o
      | App _ n a f p => eval vars f (eval vars p)
      end.

    Global Instance eval_proper {V} (n: OpType):
      Proper ((=) ==> eq ==> (=)) (@eval V n).
    Proof with auto.
     intros x y E a _ [].
     induction a.
       apply E...
      apply IHa1...
     simpl.
     apply algebra_propers.
    Qed.

    Global Instance eval_strong_proper {V} (n: OpType):
      Proper ((pointwise_dependent_relation (sorts σ) _
        (λ _, pointwise_relation V eq)) ==> eq ==> eq) (@eval V n).
    Proof with auto.
     intros x y E a _ [].
     unfold pointwise_dependent_relation in E.
     unfold pointwise_relation in E.
     induction a; simpl.
       apply E...
      congruence.
     reflexivity.
    Qed.

    Hint Extern 4 (Equiv (Term _ _)) => exact eq: typeclass_instances.
    Hint Extern 4 (Equiv (Term0 _ _)) => exact eq: typeclass_instances.

    Instance: ∀ V n v, Setoid_Morphism (@eval V (ne_list.one n) v).
    Proof.
     constructor; try apply _.
      unfold Setoid. apply _.
     destruct H0. apply _.
    Qed.

    Fixpoint app_tree {V} {o}: Term V o → op_type (Term0 V) o :=
      match o with
      | ne_list.one _ => id
      | ne_list.cons _ _ => λ x y, app_tree (App _ _ _ x y)
      end.
(*
    Instance: AlgebraOps σ (Term0 V) := λ _ x => app_tree (Op _ x).
      (* todo: these two are now duplicate with open_terms *)

    Instance: Algebra σ (Term0 V).
    Proof.
     constructor.
      intro. unfold Setoid. apply _.
     intro.
     change (Proper (=) (app_tree (Op V o))).
     generalize (Op V o).
     induction (operation_type σ o). reflexivity.
     simpl. repeat intro. subst. apply IHo0.
    Qed.
*)
    Lemma eval_map_var `(f: V → W) v s (t: Term V s):
      eval v (map_var f t) ≡ eval (λ s, v s ∘ f) t.
    Proof.
     induction t; simpl.
       reflexivity.
      congruence.
     reflexivity.
    Qed.

    Definition eval_stmt (vars: Vars A nat): Statement → Prop :=
      fix F (s: Statement) :=
       match s with
       | Eq _ i => eval vars (fst i) = eval vars (snd i)
       | Impl a b => F a → F b
       | Ext P => P
       | Conj a b => F a ∧ F b
       | Disj a b => F a ∨ F b
       end.

    Global Instance eval_stmt_proper: Proper ((=) ==> eq ==> iff) eval_stmt.
    Proof with auto.
     intros v v' ve s s' se. subst.
     induction s'; simpl; try solve [intuition].
     split; intros E.
      transitivity (eval v (fst i)).
       apply eval_proper... symmetry...
      transitivity (eval v (snd i))...
      apply eval_proper...
     transitivity (eval v' (fst i)).
      apply eval_proper...
     rewrite E.
     apply eval_proper...
    Qed.

    Definition boring_eval_entailment (vars: Vars A nat) (ee: EqEntailment):
      eval_stmt vars ee ↔ eval_stmt vars (entailment_as_conjunctive_statement ee).
    Proof. destruct ee. simpl. induction entailment_premises0; simpl; intuition. Qed.

  End eval.
End for_signature.

(* Avoid eager application *)
Remove Hints ua_vars_equiv : typeclass_instances.
Hint Extern 0 (Equiv (Vars _ _ _)) => eapply @ua_vars_equiv : typeclass_instances.

(* And with that, we define equational theories and varieties: *)

Record EquationalTheory :=
  { et_sig:> Signature
  ; et_laws:> EqEntailment et_sig → Prop }.

Class InVariety
  (et: EquationalTheory)
  (carriers: sorts et → Type)
  {e: ∀ a, Equiv (carriers a)}
  `{!AlgebraOps et carriers}: Prop :=
  { variety_algebra:> Algebra et carriers
  ; variety_laws: ∀ s, et_laws et s → ∀ vars, eval_stmt et vars s }.

Module op_type_notations.
  Global Infix "-=>" := (ne_list.cons) (at level 95, right associativity).
End op_type_notations. (* todo: get rid of *)

Module notations.
  Global Infix "===" := (mkIdentity0 _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
