Require Import
  Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Lists.List Coq.Classes.Morphisms
  MathClasses.interfaces.universal_algebra MathClasses.interfaces.abstract_algebra MathClasses.interfaces.canonical_names
  MathClasses.theory.categories MathClasses.categories.varieties.

Section contents.
  Context
    (operation: Set) (operation_type: operation → OpType unit).

  Let sig := Build_Signature unit operation operation_type.

  Context (laws: EqEntailment sig → Prop).

  Let et := Build_EquationalTheory sig laws.

  Context `{Setoid A}.

  Notation OpenTerm := (Term et A). (* Using a Let brings out Coq bug #2299. *)
  Definition OpenTerm0 a := OpenTerm (ne_list.one a).

  (* Operations are implemented as App-tree builders, so that [o a b] yields [App (App (Op o) a) b]. *)

  Fixpoint app_tree {o}: OpenTerm o → op_type OpenTerm0 o :=
    match o with
    | ne_list.one _ => id
    | ne_list.cons _ _ => λ x y, app_tree (App _ _ _ _ x y)
    end.

  Instance: AlgebraOps et OpenTerm0 := λ x, app_tree (Op _ _ x).

  (* We define term equivalence on all operation types: *)

  Inductive ee: ∀ o, Equiv (OpenTerm o) :=
    | e_vars a a': a = a' → Var et A a tt = Var et A a' tt
    | e_refl o: Reflexive (ee o)
    | e_trans o: Transitive (ee o)
    | e_sym o: Symmetric (ee o)
    | e_sub o h: Proper ((=) ==> (=) ==> (=)) (App _ _ h o)
    | e_law (s: EqEntailment et): et_laws et s → ∀ (v: Vars et OpenTerm0 nat),
      (∀ x, In x (entailment_premises _ s) → eval et v (fst (projT2 x)) = eval et v (snd (projT2 x))) →
        eval et v (fst (projT2 (entailment_conclusion _ s))) = eval et v (snd (projT2 (entailment_conclusion _ s))).

  Existing Instance ee.
  Existing Instance e_refl.
  Existing Instance e_sym.
  Existing Instance e_trans.

  (* .. and then take the specialization at arity 0 for Term0: *)

  Instance: ∀ a, Equiv (OpenTerm0 a) := λ a, ee (ne_list.one a).

  Instance: ∀ a, Setoid (OpenTerm0 a).
  Proof. split; apply _. Qed.

  (* While this fancy congruence is the one we'll use to make our initial object a setoid,
   in our proofs we will also need to talk about extensionally equal closed term
   builders (i.e. terms of type [op_type ClosedTerm0 a] for some a), where we use /Leibniz/ equality
   on closed terms: *)

  Let structural_eq a: relation _ := @op_type_equiv unit OpenTerm0 (λ _, eq) a.

  Instance structural_eq_refl a: Reflexive (structural_eq a).
  Proof. induction a; repeat intro. reflexivity. subst. apply IHa. Qed.

  (* The implementation is proper: *)

  Instance app_tree_proper: ∀ o, Proper ((=) ==> (=)) (@app_tree o).
  Proof with auto.
   induction o; repeat intro...
   apply IHo, e_sub...
  Qed.

  Instance: Algebra et OpenTerm0.
  Proof.
   constructor. intro. apply _.
   intro. apply app_tree_proper. reflexivity.
  Qed.

  (* Better still, the laws hold: *)

  Lemma laws_hold s (L: et_laws et s): ∀ vars, eval_stmt _ vars s.
  Proof with simpl in *; intuition.
   intros.
   rewrite boring_eval_entailment.
   destruct s. simpl in *. intros.
   apply (e_law _ L vars). clear L.
   induction entailment_premises... subst...
  Qed.

  (* Hence, we have an object in the variety: *)

  Global Instance: InVariety et OpenTerm0.
  Proof. constructor. apply _. intros. apply laws_hold. assumption. Qed.

  Definition the_object: varieties.Object et := varieties.object et OpenTerm0.

End contents.

(* Todo:
- show freedom;
- tackle multisorted case (likely requires modification of Term definition
   because it will no longer facilitate the trick of using the carrier as the variable
   indexing set).
*)
