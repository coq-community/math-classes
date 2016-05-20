Require Import
  Coq.Program.Program Coq.Classes.Morphisms Coq.Setoids.Setoid MathClasses.interfaces.canonical_names.

Section pointwise_dependent_relation.
  Context A (B: A → Type) (R: ∀ a, relation (B a)).

  Definition pointwise_dependent_relation: relation (∀ a, B a) :=
    λ f f', ∀ a, R _ (f a) (f' a).

  Global Instance pdr_equiv `{∀ a, Equivalence (R a)}: Equivalence pointwise_dependent_relation.
  Proof. firstorder. Qed.
End pointwise_dependent_relation.

Definition iffT (A B: Type): Type := prod (A → B) (B → A).

Class NonEmpty (A : Type) : Prop := non_empty : inhabited A.
Class NonEmptyT (A : Type) : Type := non_emptyT : A.

Definition uncurry {A B C} (f: A → B → C) (p: A * B): C := f (fst p) (snd p).

Definition is_sole `{Equiv T} (P: T → Prop) (x: T) : Prop := P x ∧ ∀ y, P y → y = x.

Definition DN (T: Type): Prop := (T → False) → False.
Class Stable P := stable: DN P → P.
(* TODO: include useful things from corn/logic/Stability.v and move to separate file *)

Class Obvious (T : Type) := obvious: T.

Section obvious.
  Context (A B C: Type).

  Global Instance: Obvious (A → A) := id.
  Global Instance: Obvious (False → A) := False_rect _.
  Global Instance: Obvious (A → A + B) := inl.
  Global Instance: Obvious (A → B + A) := inr.
  Global Instance obvious_sum_src  `{Obvious (A → C)} `{Obvious (B → C)}: Obvious (A+B → C).
  Proof. repeat intro. intuition. Defined.
  Global Instance obvious_sum_dst_l `{Obvious (A → B)}: Obvious (A → B+C).
  Proof. repeat intro. intuition. Defined.
  Global Instance obvious_sum_dst_r `{Obvious (A → B)}: Obvious (A → C+B).
  Proof. repeat intro. intuition. Defined.
End obvious.

Lemma not_symmetry `{Symmetric A R} (x y: A): ¬R x y → ¬R y x.
Proof. firstorder. Qed.
(* Also see Coq bug #2358. A totally different approach would be to define negated relations
    such as inequality as separate relations rather than notations, so that the existing [symmetry]
    will work for them. However, this most likely breaks other things. *)

Lemma biinduction_iff `{Biinduction R}
  (P1 : Prop) (P2 : R → Prop) (P2_proper : Proper ((=) ==> iff) P2) :
  (P1 ↔ P2 0) → (∀ n, P2 n ↔ P2 (1 + n)) → ∀ n, P1 ↔ P2 n.
Proof. intros ? ?. apply biinduction; [solve_proper | easy | firstorder]. Qed.

(* Isn't this in the stdlib? *)
Definition is_Some `(x : option A) :=
  match x with
  | None => False
  | Some _ => True
  end.

Lemma is_Some_def `(x : option A) :
  is_Some x ↔ ∃ y, x ≡ Some y.
Proof. unfold is_Some. destruct x; firstorder (eauto; discriminate). Qed.

Definition is_None `(x : option A) :=
  match x with
  | None => True
  | Some _ => False
  end.

Lemma is_None_def `(x : option A) :
  is_None x ↔ x ≡ None.
Proof. unfold is_None. destruct x; firstorder discriminate. Qed.

Lemma None_ne_Some `(x : option A) y :
  x ≡ None → x ≢ Some y.
Proof. congruence. Qed.
