Require
  MathClasses.orders.naturals MathClasses.implementations.peano_naturals.
Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.orders MathClasses.interfaces.additional_operations.

Section contents.
Context `{Naturals N}.
Add Ring N : (rings.stdlib_semiring_theory N).

(* NatDistance instances are all equivalent, because their behavior is fully
 determined by the specification. *)
Lemma nat_distance_unique_respectful {a b : NatDistance N} :
  ((=) ==> (=) ==> (=))%signature (nat_distance (nd:=a)) (nat_distance (nd:= b)).
Proof.
  intros x1 y1 E x2 y2 F.
  unfold nat_distance, nat_distance_sig.
  destruct a as [[z1 A]|[z1 A]], b as [[z2 B]|[z2 B]]; simpl.
     apply (left_cancellation (+) x1). now rewrite A, E, B.
    destruct (naturals.zero_sum z1 z2).
     apply (left_cancellation (+) x1).
     rewrite associativity, A, F, B, E. ring.
    transitivity 0; intuition.
   destruct (naturals.zero_sum z1 z2).
   rewrite commutativity.
   apply (left_cancellation (+) y1).
   rewrite associativity, B, <-F, A, E. ring.
   transitivity 0; intuition.
  apply (left_cancellation (+) x2).
  now rewrite A, E, F, B.
Qed.

Lemma nat_distance_unique {a b: NatDistance N} {x y : N} : nat_distance (nd:=a) x y = nat_distance (nd:=b) x y.
Proof. now apply nat_distance_unique_respectful. Qed.

Context `{!NatDistance N}.

Global Instance nat_distance_proper : Proper ((=) ==> (=) ==> (=)) nat_distance.
Proof. apply nat_distance_unique_respectful. Qed.
End contents.

(* An existing instance of [CutMinus] allows to create an instance of [NatDistance] *)
Program Instance natdistance_cut_minus `{Naturals N} `{Apart N} `{!TrivialApart N} `{!FullPseudoSemiRingOrder Nle Nlt}
    `{!CutMinusSpec N cm} `{∀ x y, Decision (x ≤ y)} : NatDistance N :=
  λ x y, if decide_rel (≤) x y then inl (y ∸ x) else inr (x ∸ y).
Next Obligation. rewrite commutativity. now apply cut_minus_le. Qed.
Next Obligation. rewrite commutativity. now apply cut_minus_le, orders.le_flip. Qed.

(* Using the preceding instance we can make an instance for arbitrary models of the naturals
    by translation into [nat] on which we already have a [CutMinus] instance. *)
Global Program Instance natdistance_default `{Naturals N} : NatDistance N | 10 := λ x y,
  match nat_distance_sig (naturals_to_semiring N nat x) (naturals_to_semiring N nat y) with
  | inl (n↾E) => inl (naturals_to_semiring nat N n)
  | inr (n↾E) => inr (naturals_to_semiring nat N n)
  end.
Next Obligation.
  rewrite <-(naturals.to_semiring_involutive N nat y), <-E.
  now rewrite rings.preserves_plus, (naturals.to_semiring_involutive _ _).
Qed.
Next Obligation.
  rewrite <-(naturals.to_semiring_involutive N nat x), <-E.
  now rewrite rings.preserves_plus, (naturals.to_semiring_involutive _ _).
Qed.
