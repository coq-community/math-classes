Require
  ne_list.
Require Import
  Morphisms Setoid Program List abstract_algebra.

Local Notation ne_list := ne_list.L.

Section with_sorts. Variable Sorts: Set.

  (* For single-sorted algebras, Sorts will typically be unit. *)

  (* OpType describes the type of an operation in an algebra. Note that higher order function types are excluded: *)

  Definition OpType := ne_list Sorts.

  Definition result: OpType → Sorts := @ne_list.last _.

  Variable carrier: Sorts → Type.

  (* Given a Type for each sort, we can map the operation type descriptions to real function types: *)

  Fixpoint op_type (o: OpType): Type :=
    match o with
    | ne_list.one a => carrier a
    | ne_list.cons a g => carrier a → op_type g
    end.

  (* This is just:

      Definition op_type: OpType → Type := ne_list.foldr1 (→) ∘ ne_list.map carrier.

    Unfortunately, in that formulation [simpl] never reduces it, which is extremely annoying...
  *)

  (* We use extensional equivalence for such generated function types: *)

  Context `{e: ∀ s, Equiv (carrier s)}.

  Fixpoint op_type_equiv o: Equiv (op_type o) :=
    match o with
    | ne_list.one _ => _: Equiv (carrier _) (*e A*)
    | ne_list.cons A g => (e A ==> op_type_equiv g)%signature
    end.

  Global Existing Instance op_type_equiv. (* There's no [Global Instance Fixpoint]. *)

  Global Instance sig_type_sym `{∀ s, Symmetric (e s)}: Symmetric (op_type_equiv o).
  Proof. induction o; simpl; firstorder. Qed.

  (* We need either reflexivity or symmetry of e in order to get transitivity of op_type_equiv: *)

  Global Instance sig_type_trans `{∀ s, Reflexive (e s)} `{∀ s, Transitive (e s)}: Transitive (op_type_equiv o).
  Proof.
   induction o; simpl. firstorder.
   intros ? y ???? y0 ?. transitivity (y y0); firstorder.
  Qed.

  Hint Unfold op_type.

  Global Instance sig_type_trans' `{∀ s, Symmetric (e s)} `{∀ s, Transitive (e s)}: Transitive (op_type_equiv o).
  Proof with auto.
   induction o; simpl...
   intros x y ? ? H2 x0 y0 ?.
   transitivity (y y0)...
   apply H2.
   transitivity x0; firstorder.
  Qed.

    (* This is the closest i've been able to get to reflexivity thus far: *)
  Lemma sig_type_refl `{∀ a, Reflexive (e a)} (o: OpType) a (x: op_type (ne_list.cons a o)) y:
    Proper (=) x → op_type_equiv o (x y) (x y).
  Proof. intro H0. apply H0. reflexivity. Qed.

(*
    Lemma sig_type_refl' (o: OpType) a (x: op_type (function a o)):
      Proper (=) x → op_type_equiv _ x x.
    Proof. intro H0. apply H0. Qed.
*)

End with_sorts.

Implicit Arguments op_type [[Sorts]].

Inductive Signature: Type :=
  { sorts: Set
  ; operation:> Set
  ; operation_type:> operation → OpType sorts }.

Definition single_sorted_signature {Op: Set} (arities: Op → nat): Signature :=
  Build_Signature unit Op (ne_list.replicate_Sn tt ∘ arities).

(* An implementation of a signature for a given realization of the sorts is simply a
 function (of the right type) for each operation: *)

Class AlgebraOps (σ: Signature) (A: sorts σ → Type) := algebra_op: ∀ o, op_type A (σ o).

(* .. which, if they are proper with respect to a bona fide setoid equality, form an algebra: *)

Class Algebra
  (σ: Signature)
  (carriers: sorts σ → Type)
  {e: ∀ a, Equiv (carriers a)}
  `{AlgebraOps σ carriers}: Prop :=
    { algebra_setoids:> ∀ a, Setoid (carriers a)
    ; algebra_propers:> ∀ o: σ, Proper (=) (algebra_op o) }.
