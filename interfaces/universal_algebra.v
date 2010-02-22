Set Automatic Introduction.

Require Import
  Morphisms Setoid Program List
  abstract_algebra theory.categories util monads setoids.

Record Entailment (P: Type): Type := { entailment_premises: list P; entailment_conclusion: P }.

Section with_sorts. Variable Sorts: Set.

  (* For single-sorted algebras, Sorts will typically be unit. *)

  (* OpType describes the type of an operation in an algebra. Note that higher order function types are excluded: *)

  Inductive OpType: Set :=
    | constant (a: Sorts)
    | function (a: Sorts) (g: OpType).

  Section with_sort_realizations. Variable Sort: Sorts → Type.

    (* Given a Type for each sort, we can map the operation type descriptions to real function types: *)

    Fixpoint op_type (o: OpType): Type :=
      match o with
      | constant a => Sort a
      | function a g => Sort a → op_type g
      end.

    (* We use extensional equivalence for such generated function types: *)

    Context `{e: Π s, Equiv (Sort s)}.

    Fixpoint op_type_equiv o: Equiv (op_type o) :=
      match o with
      | constant A => e A
      | function A g => (e A ==> op_type_equiv g)%signature
      end.

    Global Existing Instance op_type_equiv. (* There's no [Global Instance Fixpoint]. *)

    Global Instance sig_type_sym `{Π s, Symmetric (e s)}: Symmetric (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.
    
    (* We need either reflexivity or symmetry of e in order to get transitivity of op_type_equiv: *)

    Global Instance sig_type_trans `{Π s, Reflexive (e s)} `{Π s, Transitive (e s)}: Transitive (op_type_equiv o).
    Proof. induction o; simpl; firstorder. Qed.

    Global Instance sig_type_trans' `{Π s, Symmetric (e s)} `{Π s, Transitive (e s)}: Transitive (op_type_equiv o).
    Proof with auto.
     induction o; simpl...
     intros x y ? ? H2 x0 y0 ?.
     transitivity (y y0)...
     apply H2.
     transitivity x0; [symmetry |]...
    Qed.

      (* This is the closest i've been able to get to reflexivity thus far: *)
    Lemma sig_type_refl `{Π a, Reflexive (e a)} (o: OpType) a (x: op_type (function a o)) y:
      Proper equiv x → op_type_equiv o (x y) (x y).
    Proof. intro H0. apply H0. reflexivity. Qed.

(*
    Lemma sig_type_refl' (o: OpType) a (x: op_type (function a o)):
      Proper equiv x → op_type_equiv _ x x.
    Proof. intro H0. apply H0. Qed.
*)

  End with_sort_realizations.

  Section map_op.

    (* Given maps between two realizations of the sorts, there are maps between the corresponding op_types*)

    Context {A B: Sorts → Type}
      `{Π a, Equiv (A a)} `{Π a, Equiv (B a)}
      (ab: Π a, A a → B a)
      (ba: Π a, B a → A a)
      `{Π a, Proper (equiv ==> equiv) (ab a)}
      `{Π a, Proper (equiv ==> equiv) (ba a)}.

    Fixpoint map_op {o: OpType}: op_type A o → op_type B o :=
      match o return op_type A o → op_type B o with
      | constant u => ab u
      | function _ _ => λ x y => map_op (x (ba _ y))
      end.

    Global Instance map_op_proper o: Proper (op_type_equiv A o ==> op_type_equiv B o) (@map_op o).
    Proof. induction o; simpl; firstorder. Qed.
      (* todo: can't we make this nameless? *)

  End map_op.

  (* If the maps between the sorts are eachother's inverse, then so are the two generated op_type maps: *)

  Context {A B: Sorts → Type} {e: Π a, Equiv (B a)} `{Π b, Equivalence (e b)} 
   (ab: Π a, A a → B a) (ba: Π a, B a → A a) 
   `(iso: Π a (x: B a), ab a (ba a x) = x).

  Lemma map_iso o (x: op_type B o) (xproper: Proper equiv x): map_op ab ba (map_op ba ab x) = x.
  Proof with auto; try reflexivity.
   induction o; simpl; intros...
   intros x0 y H0.
   change (map_op ab ba (map_op ba ab (x (ab a (ba a x0)))) = x y).
   transitivity (x (ab a (ba a x0))).
    apply IHo, xproper...
   apply xproper. rewrite iso, H0...
  Qed.

End with_sorts.

Inductive Signature: Type :=
  { sorts: Set
  ; operation:> Set
  ; operation_type:> operation → OpType sorts }.

(* We now introduce additional things in order to let us eventually define equational theories and varieties. *)

Section for_signature. Variable sign: Signature.

  (* Let sorts := sorts sign.  -- cleaner but causes problems, test case presented to mattam *)
  Let OpType := OpType (sorts sign).

  (* An implementation of a signature for a given realization of the sorts is simply a function (of the right type) for each operation: *)

  Class AlgebraOps (A: sorts sign → Type) := algebra_op: Π o, op_type _ A (sign o).

  Class Algebra
      (carriers: sorts sign → Type)
      {e: Π a, Equiv (carriers a)}
      `{AlgebraOps carriers}: Prop :=
    { algebra_setoids:> Π a, Setoid (carriers a)
    ; algebra_propers:> Π o: sign, Proper equiv (algebra_op o)
    }.

  (* As an aside: given two implementations in different realizations of the sorts, and a map between
   them for each sort, we can say what it means for that map to preserve the algebra's operations,
   i.e. what it takes for it to be a homomorphism: *)

  Section for_map.

    Context (A B: sorts sign → Type)
      `{ea: Π a, Equiv (A a)} `{eb: Π a, Equiv (B a)}
      `{ai: AlgebraOps A} `{bi: AlgebraOps B}.

    Section with_f. Context (f: Π a, A a → B a).

    Implicit Arguments f [[a]].

    Fixpoint Preservation {n: OpType}: op_type _ A n → op_type _ B n → Prop :=
      match n with
      | constant d => λ o o' => f o = o'
      | function x y => λ o o' => Π x, Preservation (o x) (o' (f x))
      end.

    Class HomoMorphism: Prop :=
      { homo_proper:> Π a, Setoid_Morphism (@f a)
      ; preserves: Π (o: sign), Preservation (ai o) (bi o)
      ; homo_source_algebra: Algebra A
      ; homo_target_algebra: Algebra B
      }.

    Context `{Π i, Equivalence (ea i)} `{Π i, Equivalence (eb i)} `{Π a, Setoid_Morphism (@f a)}.

    Global Instance Preservation_proper n:
      Proper (op_type_equiv _ _ _ ==> op_type_equiv _ B n ==> iff) (@Preservation n).
        (* todo: use equiv in the signature and see why things break *)
    Proof with auto.
     induction n; simpl; intros x y E x' y' E'.
      split; intro F. rewrite <- E, <- E'... rewrite E, E'...
     split; simpl; intros; apply (IHn _ _ (E _ _ (reflexivity _)) _ _ (E' _ _ (reflexivity _)))...
    Qed.

    Global Instance Preservation_proper'' n:
      Proper (eq ==> op_type_equiv _ B n ==> iff) (@Preservation n).
        (* todo: use equiv in the signature and see why things break *)
    Proof with auto.
     induction n; simpl; intros x y E x' y' E'.
      split; intro F. rewrite <- E, <- E'... rewrite E, E'...
     split; simpl; intros.
      subst.
      apply (IHn (y x0) (y x0) eq_refl (y' (f x0)) (x' (f x0)) ).
       symmetry.
       apply E'.
       reflexivity.
      apply H2.
     subst.
     apply (IHn (y x0) (y x0) eq_refl (y' (f x0)) (x' (f x0)) ).
      symmetry.
      apply E'.
      reflexivity.
     apply H2.
    Qed. (* todo: evil, get rid of *)

    End with_f.

    Lemma Preservation_proper' (f g: Π a, A a → B a)
     `{Π i, Equivalence (ea i)} `{Π i, Equivalence (eb i)} `{Π a, Setoid_Morphism (@f a)}:
      (Π a (x: A a), f a x = g a x) → (Π (n: OpType) x y, Proper equiv x → Proper equiv y →
        @Preservation f n x y →
        @Preservation g n x y).
    Proof.
     induction n.
      simpl.
      intros.
      rewrite <- H5.
      symmetry.
      intuition.
     simpl.
     intros.
     apply IHn.
       apply H3. reflexivity.
      apply H4. reflexivity.
     assert (y (g a x0) = y (f a x0)).
      apply H4.
      symmetry.
      apply H2.
     apply (Preservation_proper'' f n (x x0) (x x0) eq_refl _ _ H6).
     apply H5.
    Qed.

    Lemma HomoMorphism_Proper: Proper ((λ f g => Π a x, f a x = g a x) ==> iff) HomoMorphism.
      (* todo: use pointwise_thingy *)
    Proof with try apply _; intuition.
     constructor; intros [? ? ? ?]; simpl in *.
      repeat constructor...
       repeat intro.
       do 2 rewrite <- H.
       rewrite H0...
      apply (Preservation_proper' x y H (sign o) (ai o) (bi o))...
     repeat constructor...
      repeat intro.
      do 2 rewrite H.
      rewrite H0...
     assert (Π (a : sorts sign) (x0 : A a), y a x0 = x a x0). symmetry. apply H.
     apply (Preservation_proper' y x H0 (sign o) (ai o) (bi o))...
    Qed.

  End for_map.

  Global Instance id_homomorphism A
    `{Π a, Equiv (A a)} {ao: AlgebraOps A} `{!Algebra A}: HomoMorphism _ _ (λ _ => id).
  Proof with try apply _; intuition.
   constructor; intros...
   generalize (ao o).
   induction (sign o); simpl...
   reflexivity.
  Qed.

  Global Instance compose_homomorphisms A B C f g
    `{Π a, Equiv (A a)} `{Π a, Equiv (B a)} `{Π a, Equiv (C a)}
    {ao: AlgebraOps A} {bo: AlgebraOps B} {co: AlgebraOps C}
    {gh: HomoMorphism A B g} {fh: HomoMorphism B C f}: HomoMorphism A C (λ a => f a ∘ g a).
  Proof with try apply _; auto.
   pose proof (homo_source_algebra _ _ g).
   pose proof (homo_target_algebra _ _ g).
   pose proof (homo_target_algebra _ _ f).
   constructor; intros...
   generalize (ao o) (bo o) (co o) (preserves _ _ g o) (preserves _ _ f o).
   induction (sign o); simpl; intros; unfold compose.
    rewrite H5...
   apply (IHo0 _ (o2 (g _ x)))...
  Qed.

  (* Proceeding on our way toward equational theories and varieties, we define terms: *)

  Inductive Term (V: Type): OpType → Type :=
    | Var (v: V) (a: sorts sign): Term V (constant _ a)
    | App (t: OpType) y: Term V (function _ y t) → Term V (constant _ y) → Term V t
    | Op (o: sign): Term V (sign o).

  Implicit Arguments Var [[V]].

  (* Term has OpType as an index, which means we can have terms with function
   types (no surprise there). However, often we want to prove properties that only speak of
   terms of arity 0 (that is, terms of type [Term (constant _ sort)] for some sort): *)

  Definition Term0 v sort := Term v (constant _ sort).

  Section applications_ind.

    Context (V: Type) (P: Π a, Term0 V a → Prop).

    (* To be able to prove such a P by induction, we must first transform it into a statement
     about terms of all arities. Roughly speaking, we do this by saying
     [Π x0...xN, P (App (... (App f x0) ...) xN)] for a term f of arity N. *)

    Fixpoint applications {ot}: Term V ot → Prop :=
      match ot with
      | constant x => P x
      | function x y => λ z => Π v, P _ v → applications (App V _ _ z v)
      end.

    (* To prove P/applications by induction, we can then use: *)

    Lemma applications_ind:
      (Π o a t t', P a t → applications t' → applications (App _ o a t' t)) →
      (Π v a, P _ (Var v a)) →
      (Π o, applications (Op _ o)) →
      (Π a t, P a t).
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

  Definition mkIdentity0 {sort}: T (constant _ sort) → T (constant _ sort) → Identity0 sort := pair.

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
   the form (A → B → C → D), while the second converts the same entailment into a statement of
   the form ((A ∧ B ∧ C) → D). Both have their uses in induction proofs. *)

  (* To be able to state that laws hold in a model of a variety, we must be able to evaluate terms
   using the model's implementation and using arbitrary variable assignments: *)

  Section Vars.

    Context (A: sorts sign → Type) (V: Type) `{e: Π a, Equiv (A a)} `{Π a, Equivalence (e a)}.

    Definition Vars := Π a, V → A a.

    Global Instance: Equiv Vars :=
     @pointwise_dependent_relation (sorts sign) (λ a => V → A a)
      (λ _ => pointwise_relation _ equiv).

    Global Instance: Equivalence (equiv: relation Vars).

  End Vars.

  Definition no_vars x: Vars x False := λ _ => False_rect _.

  (* Given an assignment mapping variables to closed terms, we can close open terms: *)

  Fixpoint close {V} {o} (v: Vars (λ x => Term False (constant _ x)) V) (t: Term V o): Term False o :=
    match t in Term _ o return Term False o with
    | Var x y => v y x
    | App x y z r => App _ x y (close v z) (close v r)
    | Op o => Op _ o
    end.

  Section eval.

    Context `{Algebra A}.

    Fixpoint eval {V} {n: OpType} (vars: Vars A V) (t: Term V n) {struct t}: op_type _ A n :=
      match t in Term _ n return op_type _ A n with
      | Var v a => vars a v
      | Op o => algebra_op o
      | App n a f p => eval vars f (eval vars p)
      end.

    Global Instance eval_proper {V} (n: OpType):
      Proper (equiv ==> eq ==> equiv) (@eval V n).
    Proof with auto.
     intros x y E a _ [].
     induction a.
       apply E...
      apply IHa1...
     simpl.
     apply algebra_propers.
    Qed.

    Definition eval_stmt (vars: Vars A nat): Statement → Prop :=
      fix F (s: Statement) :=
       match s with
       | Eq _ i => eval vars (fst i) = eval vars (snd i)
       | Impl a b => F a → F b
       | Ext P => P
       | Conj a b => F a ∧ F b
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

    Definition boring_eval_entailment (vars: Vars A nat) (ee: EqEntailment):
      eval_stmt vars ee <-> eval_stmt vars (entailment_as_conjunctive_statement ee).
    Proof. destruct ee. simpl. induction entailment_premises0; simpl; intuition. Qed.

  End eval.

End for_signature.

(* And with that, we define equational theories and varieties: *)

Record EquationalTheory :=
  { et_sig:> Signature
  ; et_laws:> EqEntailment et_sig → Prop }.

Class Variety
  (et: EquationalTheory)
  (carriers: sorts et → Type)
  {e: Π a, Equiv (carriers a)}
  `{!AlgebraOps et carriers}: Prop :=
  { variety_algebra:> Algebra et carriers
  ; variety_laws: Π s: EqEntailment et, et_laws et s → (Π vars: Π a, nat → carriers a,
      @eval_stmt et carriers e _ vars s)
  }.

Module op_type_notations.
  Global Infix "-=>" := (function _) (at level 95, right associativity).
End op_type_notations.

Module notations.
  Global Infix "===" := (mkIdentity0 _) (at level 70, no associativity).
  Global Infix "-=>" := (Impl _) (at level 95, right associativity).
End notations.
