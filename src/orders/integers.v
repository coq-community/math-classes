Require
  theory.integers theory.int_abs.
Require Import
  Ring abstract_algebra interfaces.integers interfaces.naturals
  interfaces.additional_operations interfaces.orders
  natpair_integers orders.rings.
Require Export
  orders.nat_int.

Section integers.
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z} `{!FullPseudoSemiRingOrder Zle Zlt}.

Add Ring Z : (rings.stdlib_ring_theory Z).
Add Ring nat : (rings.stdlib_semiring_theory nat).

Lemma induction
  (P: Z → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → (∀ n, n ≤ 0 → P n → P (n - 1)) → ∀ n, P n.
Proof.
  intros P0 Psuc1 Psuc2 n.
  destruct (int_abs_sig Z nat n) as [[a A]|[a A]].
   rewrite <-A. clear A. revert a.
   apply naturals.induction.
     solve_proper.
    now rewrite rings.preserves_0.
   intros m E.
   rewrite rings.preserves_plus, rings.preserves_1.
   apply Psuc1. apply to_semiring_nonneg. easy.
  rewrite <-(groups.negate_involutive n), <-A.
  clear A. revert a. apply naturals.induction.
    solve_proper.
   now rewrite rings.preserves_0, rings.negate_0.
  intros m E.
  rewrite rings.preserves_plus, rings.preserves_1.
  rewrite rings.negate_plus_distr, commutativity.
  apply Psuc2. apply naturals.negate_to_ring_nonpos. easy.
Qed.

Lemma induction_nonneg
  (P: Z → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → ∀ n, 0 ≤ n → P n.
Proof.
  intros P0 PS. refine (induction _ _ _ _); auto.
   solve_proper.
  intros n E1 ? E2.
  destruct (rings.is_ne_0 1).
  apply (antisymmetry (≤)).
   apply (order_reflecting ((n - 1) +)). ring_simplify. now transitivity 0.
  transitivity (n - 1). easy. apply (order_reflecting (1 +)). ring_simplify.
  transitivity 0. easy. apply semirings.le_0_2.
Qed.

Global Instance: Biinduction Z.
Proof.
  intros P ? P0 Psuc. apply induction; trivial.
   firstorder.
  intros. apply Psuc.
  now setoid_replace (1 + (n - 1)) with n by ring.
Qed.

Global Program Instance: ∀ x y: Z, Decision (x ≤ y) | 10 := λ x y,
  match decide (integers_to_ring _ (SRpair nat) x ≤ integers_to_ring _ (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (order_reflecting (integers_to_ring _ (SRpair nat))). Qed.
End integers.

(* A default order on the integers *)
Instance int_le `{Integers Z} : Le Z | 10 :=  λ x y, ∃ z, y = x + naturals_to_semiring nat Z z.
Instance int_lt  `{Integers Z} : Lt Z | 10 := dec_lt.

Section default_order.
Context `{Integers Int} `{Apart Int} `{!TrivialApart Int}.
Add Ring Int2 : (rings.stdlib_ring_theory Int).

Instance: Proper ((=) ==> (=) ==> iff) int_le.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   now rewrite <-E1, <-E2.
  now rewrite E1, E2.
Qed.

Instance: PartialOrder int_le.
Proof.
  repeat (split; try apply _).
    intros x. exists (0:nat). rewrite rings.preserves_0. ring.
   intros x y z [a A] [b B]. exists (a + b).
   now rewrite rings.preserves_plus, associativity, <-A, B.
  intros x y [a A] [b B].
  destruct (naturals.zero_sum a b) as [E1 E2].
   apply (injective (naturals_to_semiring nat Int)).
   rewrite rings.preserves_plus, rings.preserves_0.
   apply (left_cancellation (+) x).
   rewrite B at 2. rewrite A. ring.
  rewrite A, B, E1, E2, rings.preserves_0. ring.
Qed.

Instance: SemiRingOrder int_le.
Proof.
  apply from_ring_order.
   repeat (split; try apply _).
   intros x y [a A]. exists a. rewrite A. ring.
  intros x y [a A] [b B]. exists (a * b). rewrite A, B, rings.preserves_mult. ring.
Qed.

Notation i_to_r := (integers_to_ring Int (SRpair nat)).

Instance: TotalRelation int_le.
Proof.
  assert (∀ x y, i_to_r x ≤ i_to_r y → x ≤ y) as P.
   intros x y E.
   destruct (decompose_le E) as [a [A B]].
   exists (pos a ∸ neg a).
   apply (injective i_to_r).
   rewrite rings.preserves_plus, B. clear B. apply sm_proper.
   rewrite (naturals.to_semiring_twice _ _ SRpair_inject).
   unfold equiv, SRpair_equiv, le, SRpair_le in *. simpl in *.
   rewrite right_identity, cut_minus_le.
    reflexivity.
   now rewrite rings.plus_0_l, rings.plus_0_r in A.
  intros x y.
  now destruct (total (≤) (i_to_r x) (i_to_r y)); [left|right]; eapply P.
Qed.

Global Instance: FullPseudoSemiRingOrder int_le int_lt.
Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
