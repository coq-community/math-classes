Require
  MathClasses.theory.naturals.
Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.orders MathClasses.orders.rings.
Require Export
  MathClasses.orders.nat_int.

Section naturals_order.
Context `{Naturals N} `{Apart N} `{!TrivialApart N} `{!FullPseudoSemiRingOrder Nle Nlt}.

Instance nat_nonneg x : PropHolds (0 ≤ x).
Proof. now apply (to_semiring_nonneg (f:=id)). Qed.

Lemma nat_le_plus {x y: N}: x ≤ y ↔ ∃ z, y = x + z.
Proof.
  split; intros E.
   destruct (decompose_le E) as [z [Ez1 Ez2]]. now exists z.
  destruct E as [z Ez].
  apply compose_le with z; [solve_propholds | easy].
Qed.

Lemma nat_not_neg x : ¬x < 0.
Proof. apply le_not_lt_flip, nat_nonneg. Qed.

Lemma nat_0_or_pos x : x = 0 ∨ 0 < x.
Proof.
  destruct (trichotomy (<) 0 x) as [?|[?|?]]; intuition.
  now destruct (nat_not_neg x).
Qed.

Lemma nat_0_or_ge_1 x : x = 0 ∨ 1 ≤ x.
Proof. rewrite <-pos_ge_1. apply nat_0_or_pos. Qed.

Lemma nat_ne_0_pos x : x ≠ 0 ↔ 0 < x.
Proof.
  split.
   destruct (nat_0_or_pos x); intuition.
  intros E1 E2. rewrite E2 in E1. now destruct (irreflexivity (<) 0).
Qed.

Lemma nat_ne_0_ge_1 x : x ≠ 0 ↔ 1 ≤ x.
Proof. rewrite <-pos_ge_1. now apply nat_ne_0_pos. Qed.

Global Instance: ∀ (z : N), PropHolds (z ≠ 0) → OrderReflecting (z *.).
Proof.
   intros z ?.
   repeat (split; try apply _). apply (order_reflecting_pos (.*.) z).
   now apply nat_ne_0_pos.
Qed.

Global Program Instance slow_nat_le_dec: ∀ x y: N, Decision (x ≤ y) | 10 := λ x y,
  match decide (naturals_to_semiring _ nat x ≤ naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (order_reflecting (naturals_to_semiring N nat)). Qed.

Section another_ring.
  Context `{Ring R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}
    `{!SemiRing_Morphism (f : N → R)}.

  Lemma negate_to_ring_nonpos n : -f n ≤ 0.
  Proof. apply flip_nonneg_negate. now apply to_semiring_nonneg. Qed.

  Lemma between_to_ring n : -f n ≤ f n.
  Proof. apply between_nonneg. now apply to_semiring_nonneg. Qed.
End another_ring.
End naturals_order.

Hint Extern 20 (PropHolds (_ ≤ _)) => eapply @nat_nonneg : typeclass_instances.

(* A default order on the naturals *)
Instance nat_le `{Naturals N} : Le N | 10 :=  λ x y, ∃ z, x + z = y.
Instance nat_lt  `{Naturals N} : Lt N | 10 := dec_lt.

Section default_order.
Context `{Naturals N} `{Apart N} `{!TrivialApart N}.
Add Ring N2 : (rings.stdlib_semiring_theory N).

Instance: Proper ((=) ==> (=) ==> iff) nat_le.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   now rewrite <-E1, <-E2.
  now rewrite E1, E2.
Qed.

Instance: PartialOrder nat_le.
Proof.
  repeat (split; try apply _).
    intros x. exists 0. ring.
   intros x y z [a A] [b B]. exists (a + b). now rewrite associativity, A, B.
   intros x y [a A] [b B].
  destruct (naturals.zero_sum a b) as [E1 E2].
   apply (left_cancellation (+) x).
   rewrite associativity, A, B. ring.
  rewrite <-A, <-B, E1, E2. ring.
Qed.

Instance: SemiRingOrder nat_le.
Proof.
  repeat (split; try apply _).
     intros x y [a A]. now exists a.
    intros x y [a A]. exists a. rewrite <-A. ring.
   intros x y [a A]. exists a.
   apply (left_cancellation (+) z). rewrite <-A. ring.
  intros x y _ _. exists (x * y). ring.
Qed.

Notation n_to_sr := (naturals_to_semiring N nat).

Instance: TotalRelation nat_le.
Proof.
  assert (∀ x y, n_to_sr x ≤ n_to_sr y → x ≤ y) as P.
   intros x y E.
   destruct (decompose_le E) as [a [_ A]].
   exists (naturals_to_semiring nat N a).
   apply (injective n_to_sr).
   rewrite rings.preserves_plus. now rewrite (naturals.to_semiring_involutive _ _).
  intros x y.
  destruct (total (≤) (n_to_sr x) (n_to_sr y)); [left | right]; now apply P.
Qed.

Global Instance: FullPseudoSemiRingOrder nat_le nat_lt.
Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
