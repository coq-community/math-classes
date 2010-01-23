Require Import
  Setoid canonical_names.

Section pointwise_dependent_relation. Context A (B: A -> Type) (R: forall a, relation (B a)).

  Definition pointwise_dependent_relation: relation (forall a, B a) :=
    fun f f' => forall a, R _ (f a) (f' a).

  Global Instance pdr_equiv `{forall a, Equivalence (R a)}: Equivalence pointwise_dependent_relation.
  Proof. firstorder. Qed.

End pointwise_dependent_relation.

Definition sig_relation {A} (R: relation A) (P: A -> Prop): relation (sig P)
  := fun a b => R (proj1_sig a) (proj1_sig b).

Instance sig_equiv: forall (e: Equiv A) (P: A -> Prop), Equiv (sig P) := @sig_relation.
Implicit Arguments sig_equiv [[A] [e]].

Global Instance sig_equivalence `{e: Equiv A} (P: A -> Prop) `{!Equivalence e}: Equivalence (sig_equiv P).
Proof.
 split; repeat intro; unfold sig_equiv, sig_relation in *; try intuition.
 transitivity (proj1_sig y); intuition.
Qed.
