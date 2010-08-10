Require Import
  Setoid canonical_names.

Section pointwise_dependent_relation. Context A (B: A → Type) (R: ∀ a, relation (B a)).

  Definition pointwise_dependent_relation: relation (∀ a, B a) :=
    λ f f', ∀ a, R _ (f a) (f' a).

  Global Instance pdr_equiv `{∀ a, Equivalence (R a)}: Equivalence pointwise_dependent_relation.
  Proof. firstorder. Qed.

End pointwise_dependent_relation.

Program Definition sig_relation {A} (R: relation A) (P: A → Prop): relation (sig P) := R.

Instance sig_equiv: ∀ (e: Equiv A) (P: A → Prop), Equiv (sig P) := @sig_relation.
Implicit Arguments sig_equiv [[A] [e]].

Global Instance sig_equivalence `{e: Equiv A} (P: A → Prop) `{!Equivalence e}: Equivalence (sig_equiv P).
Proof.
 split; repeat intro; unfold sig_equiv, sig_relation in *; try intuition.
 transitivity (proj1_sig y); intuition.
Qed.

Definition sigT_relation {A} (R: relation A) (P: A → Type): relation (sigT P)
  := λ a b, R (projT1 a) (projT1 b).

Instance sigT_equiv: ∀ (e: Equiv A) (P: A → Type), Equiv (sigT P) := @sigT_relation.
Implicit Arguments sigT_equiv [[A] [e]].

Global Instance sigT_equivalence `{e: Equiv A} (P: A → Type) `{!Equivalence e}: Equivalence (sigT_equiv P).
Proof.
 split; repeat intro; unfold sigT_equiv, sigT_relation in *; try intuition.
 transitivity (projT1 y); intuition.
Qed.

Definition iffT (A B: Type): Type := prod (A → B) (B → A).

Class NonEmpty {A: Type} (P: A → Prop): Prop := { non_empty: sig P }.

Definition uncurry {A B C} (f: A → B → C) (p: A * B): C := f (fst p) (snd p).

Definition is_sole `{Equiv T} (P: T → Prop) (x: T): Prop :=
  P x ∧ `(P y → y = x).

Definition DN (T: Type): Prop := (T → False) → False.
Class Stable P := { stable: DN P → P }.

Instance: ∀ P, Decision P → Stable P.
Proof. firstorder. Qed.

Section obvious.

  Class Obvious (T: Type) := obvious: T.

  Context (A B C: Type).

  Global Instance: Obvious (A → A) := id.
  Global Instance: Obvious (False → A) := False_rect _.
  Global Instance: Obvious (A → A + B) := inl.
  Global Instance: Obvious (A → B + A) := inr.
  Global Instance obvious_sum_src  `{Obvious (A → C)} `{Obvious (B → C)}: Obvious (A+B → C). repeat intro. intuition. Defined.
  Global Instance obvious_sum_dst_l `{Obvious (A → B)}: Obvious (A → B+C). repeat intro. intuition. Defined.
  Global Instance obvious_sum_dst_r `{Obvious (A → B)}: Obvious (A → C+B). repeat intro. intuition. Defined.

End obvious.

Lemma not_symmetry `{Symmetric A R} (x y: A): ~ R x y → ~ R y x.
Proof. firstorder. Qed.
  (* Also see Coq bug #2358. A totally different approach would be to define negated relations such as inequality as separate relations rather than notations, so that the existing [symmetry] will work for them. However, this most likely breaks other things. *)
