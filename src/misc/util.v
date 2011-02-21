Require Import
  Program Morphisms Setoid canonical_names.

Section pointwise_dependent_relation. 
  Context A (B: A → Type) (R: ∀ a, relation (B a)).

  Definition pointwise_dependent_relation: relation (∀ a, B a) :=
    λ f f', ∀ a, R _ (f a) (f' a).

  Global Instance pdr_equiv `{∀ a, Equivalence (R a)}: Equivalence pointwise_dependent_relation.
  Proof. firstorder. Qed.
End pointwise_dependent_relation.

Instance sig_equiv `{Equiv A} (P: A → Prop) : Equiv (sig P) := λ x y, proj1_sig x = proj1_sig y.

Instance sig_equivalence `{e : Equiv A} (P: A → Prop) `{!Equivalence e}: Equivalence (sig_equiv P).
Proof.
 split; repeat intro; unfold sig_equiv in *; try intuition.
 transitivity (proj1_sig y); intuition.
Qed.

Instance sigT_equiv `{Equiv A} (P: A → Type) : Equiv (sigT P) := λ a b, projT1 a = projT1 b.

Instance sigT_equivalence `{e: Equiv A} (P: A → Type) `{!Equivalence e} : Equivalence (sigT_equiv P).
Proof.
 split; repeat intro; unfold sigT_equiv in *; try intuition.
 transitivity (projT1 y); intuition.
Qed.

Definition iffT (A B: Type): Type := prod (A → B) (B → A).

Class NonEmpty {A: Type} (P: A → Prop) : Prop := non_empty: ex P.

Definition uncurry {A B C} (f: A → B → C) (p: A * B): C := f (fst p) (snd p).

Definition is_sole `{Equiv T} (P: T → Prop) (x: T): Prop := P x ∧ `(P y → y = x).

Definition DN (T: Type): Prop := (T → False) → False.

Class Stable P := stable: DN P → P.

Instance: ∀ P, Decision P → Stable P.
Proof. firstorder. Qed.

Section obvious.
  Class Obvious (T: Type) := obvious: T.

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

Class PropHolds (P : Prop) := prop_holds: P.

Instance: Proper (iff ==> iff) PropHolds.
Proof. now repeat intro. Qed.

Definition bool_decide (P : Prop) `{dec : !Decision P} : bool := if dec then true else false.

Lemma bool_decide_true `{dec : Decision P} : bool_decide P ≡ true ↔ P.
Proof. unfold bool_decide. split; intro; destruct dec; firstorder. Qed.

Lemma bool_decide_false `{dec : !Decision P} : bool_decide P ≡ false ↔ ¬P.
Proof. unfold bool_decide. split; intro; destruct dec; firstorder. Qed.

(* 
  Because [vm_compute] evaluates terms in [Prop] eagerly and does not remove dead code we 
  need the decide_rel hack. Suppose we have [(x = y) =def  (f x = f y)], now:
     bool_decide (x = y) → bool_decide (f x = f y) → ...
  As we see, the dead code [f x] and [f y] is actually evaluated, which is of course an utter waste. 
  Therefore we introduce decide_rel and bool_decide_rel.
     bool_decide_rel (=) x y → bool_decide_rel (λ a b, f a = f b) x y → ...
  Now the definition of equality remains under a lambda and our problem does not occur anymore!
*)

Definition decide_rel `(R : relation A) {dec : ∀ x y, Decision (R x y)} (x : A) (y : A) : Decision (R x y)
  := dec x y.

Definition bool_decide_rel `(R : relation A) {dec : ∀ x y, Decision (R x y)} : A → A → bool 
  := λ x y, if dec x y then true else false.

Lemma bool_decide_rel_true `(R : relation A) {dec : ∀ x y, Decision (R x y)} : 
  ∀ x y, bool_decide_rel R x y ≡ true ↔ R x y.
Proof. unfold bool_decide_rel. split; intro; destruct dec; firstorder. Qed.

Lemma bool_decide_rel_false `(R : relation A)`{dec : ∀ x y, Decision (R x y)} : 
  ∀ x y, bool_decide_rel R x y ≡ false ↔ ¬R x y.
Proof. unfold bool_decide_rel. split; intro; destruct dec; firstorder. Qed.

Lemma not_symmetry `{Symmetric A R} (x y: A): ¬R x y → ¬R y x.
Proof. firstorder. Qed.
(* Also see Coq bug #2358. A totally different approach would be to define negated relations 
    such as inequality as separate relations rather than notations, so that the existing [symmetry] 
    will work for them. However, this most likely breaks other things. *)
