Require Import
  Ring interfaces.naturals abstract_algebra interfaces.orders
  orders.nat_int theory.integers theory.rings orders.rings.

Section contents. 
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z} `{!FullPseudoSemiRingOrder Zle Zlt} `{Naturals N}.

Add Ring Z : (rings.stdlib_ring_theory Z).

Lemma int_to_nat_unique_respectful {a b : IntAbs Z N} : 
  ((=) ==> (=))%signature (int_to_nat Z N (ia:=a)) (int_to_nat Z N (ia:= b)).
Proof.
  intros x y E. unfold int_to_nat, int_abs_sig.
  apply (injective (naturals_to_semiring N Z)).
  destruct a as [[z1 A]|[z1 A]], b as [[z2 B]|[z2 B]].
     now rewrite A, B.
    destruct (naturals.to_ring_zero_sum z2 z1) as [? E2]. 
     now rewrite B, A, involutive.
    now rewrite E2.
   destruct (naturals.to_ring_zero_sum z1 z2) as [? E2]. 
    now rewrite B, A, involutive.
   now rewrite E2.
  reflexivity.
Qed.

Lemma int_to_nat_unique (a b : IntAbs Z N) (z : Z) : 
  int_to_nat Z N (ia:=a) z = int_to_nat Z N (ia:=a) z.
Proof. now apply int_to_nat_unique_respectful. Qed.

Context `{!IntAbs Z N}.

Global Instance int_to_nat_proper: Setoid_Morphism (int_to_nat Z N) | 0.
Proof. split; try apply _. now apply int_to_nat_unique_respectful. Qed.

Context `{!SemiRing_Morphism (f : N → Z)}.

Lemma int_to_nat_spec x :
  { 0 ≤ x ∧ f (int_to_nat Z N x) = x } + { x ≤ 0 ∧ int_to_nat Z N x = 0 }.
Proof.
  unfold int_to_nat. destruct int_abs_sig as [[n E]|[n E]].
   left. rewrite <-E. split.
    now apply to_semiring_nonneg.
   apply (naturals.to_semiring_unique_alt _ _).
  right. intuition. apply flip_nonpos_negate. rewrite <-E. 
  now apply to_semiring_nonneg.
Qed.

Lemma int_to_nat_nat n : 
  int_to_nat Z N (f n) = n.
Proof.
  apply (injective f). destruct (int_to_nat_spec (f n)) as [[??]|[? E]]; intuition.
  rewrite E, preserves_0. apply (antisymmetry (≤)); intuition.
  now apply to_semiring_nonneg.
Qed. 

Lemma int_to_nat_cancel_l x n :
  x = f n → int_to_nat Z N x = n.
Proof. intros E. now rewrite E, int_to_nat_nat. Qed.

Lemma int_to_nat_cancel_r x n :
  f n = x → n = int_to_nat Z N x.
Proof. intros E. now rewrite <-E, int_to_nat_nat. Qed.

Lemma int_to_nat_negate_nat n : 
  int_to_nat Z N (-f n) = 0.
Proof.
  apply (injective f). destruct (int_to_nat_spec (-f n)) as [[? E]|[? E]].
   rewrite E, preserves_0. apply (antisymmetry (≤)); intuition.
   apply rings.flip_nonneg_negate. now apply to_semiring_nonneg.
  now rewrite E.
Qed. 

Lemma int_to_nat_0 : int_to_nat Z N 0 = 0.
Proof. apply int_to_nat_cancel_l. now rewrite preserves_0. Qed.

Lemma int_to_nat_of_nonneg x : 
  0 ≤ x → f (int_to_nat Z N x) = x.
Proof.
  intros E1. destruct (int_to_nat_spec x) as [[? E2]|[? E2]]; intuition.
  rewrite E2, preserves_0. now apply (antisymmetry (≤)).
Qed.

Lemma int_to_nat_of_nonpos x : 
  x ≤ 0 → int_to_nat Z N x = 0.
Proof.
  intros E. destruct (int_to_nat_spec x) as [[? E2]|]; intuition.
  apply int_to_nat_cancel_l. rewrite preserves_0.
  now apply (antisymmetry (≤)).
Qed.

Lemma int_to_nat_nonneg_plus x y : 
  0 ≤ x → 0 ≤ y → int_to_nat Z N (x + y) = int_to_nat Z N x + int_to_nat Z N y.
Proof.
  intros. apply (injective f).
  rewrite preserves_plus, !int_to_nat_of_nonneg; intuition.
  now apply nonneg_plus_compat.
Qed.

Lemma int_to_nat_mult_nonneg_l x y : 
  0 ≤ x → int_to_nat Z N (x * y) = int_to_nat Z N x * int_to_nat Z N y.
Proof.
  intros E. apply (injective f). rewrite preserves_mult. 
  rewrite (int_to_nat_of_nonneg x) by easy.
  destruct (int_to_nat_spec y) as [[? Ey]|[? Ey]]; rewrite Ey, ?preserves_0.
   rewrite int_to_nat_of_nonneg. easy. now apply nonneg_mult_compat.
  rewrite int_to_nat_of_nonpos, preserves_0. ring. now apply nonneg_nonpos_mult.
Qed.

Lemma int_to_nat_mult_nonneg_r x y : 
  0 ≤ y → int_to_nat Z N (x * y) = int_to_nat Z N x * int_to_nat Z N y.
Proof. 
  rewrite (commutativity x), (commutativity (int_to_nat Z N x)).
  now apply int_to_nat_mult_nonneg_l.
Qed.

Lemma int_to_nat_1 : int_to_nat Z N 1 = 1.
Proof. apply int_to_nat_cancel_l. now rewrite preserves_1. Qed.

Context `{Apart N} `{!TrivialApart N} `{!FullPseudoSemiRingOrder (A:=N) Nle Nlt}.

Global Instance int_to_nat_nonneg x :
  PropHolds (0 ≤ int_to_nat Z N x).
Proof.
  destruct (int_to_nat_spec x) as [[? E]|[? E]].
   apply (order_reflecting f). now rewrite preserves_0, E.
  rewrite E. solve_propholds.
Qed.

Global Instance int_to_nat_pos x :
  PropHolds (0 < x) → PropHolds (0 < int_to_nat Z N x).
Proof.
  rewrite !lt_iff_le_ne. intros [??]. split.
   solve_propholds.
  apply (setoids.morphism_ne f).
  now rewrite preserves_0, int_to_nat_of_nonneg.
Qed.

Lemma int_to_nat_le_l x y :
  0 ≤ x → x ≤ y → f (int_to_nat Z N x) ≤ y.
Proof. intros. now rewrite int_to_nat_of_nonneg. Qed.

Lemma int_to_nat_le_cancel_l x n :
  0 ≤ x → x ≤ f n → int_to_nat Z N x ≤ n.
Proof. intros. now apply (order_reflecting f), int_to_nat_le_l. Qed.

Lemma int_to_nat_le_r x y :
  x ≤ y → x ≤ f (int_to_nat Z N y).
Proof. 
  intros E1. destruct (int_to_nat_spec y) as [[? E2]|[? E2]].
   now rewrite E2.
  rewrite E2, preserves_0. now transitivity y.
Qed.

Lemma int_to_nat_le_cancel_r x n :
  f n ≤ x → n ≤ int_to_nat Z N x.
Proof. intros. now apply (order_reflecting f), int_to_nat_le_r. Qed.

Global Instance: OrderPreserving (int_to_nat Z N).
Proof.
  repeat (split; try apply _). intros x y E.
  destruct (total (≤) 0 x).
   now apply int_to_nat_le_cancel_r, int_to_nat_le_l.
  rewrite int_to_nat_of_nonpos. solve_propholds. easy.
Qed.

Lemma int_to_nat_le_back x y :
  0 ≤ y → int_to_nat Z N x ≤ int_to_nat Z N y → x ≤ y.
Proof.
  intros. rewrite <-(int_to_nat_of_nonneg y) by easy.
  transitivity (f (int_to_nat Z N x)).
   now apply int_to_nat_le_r.
  now apply (order_preserving f).
Qed.

Lemma int_to_nat_lt_l x y :
  0 ≤ x → x < y → f (int_to_nat Z N x) < y.
Proof. intros. now rewrite int_to_nat_of_nonneg. Qed.

Lemma int_to_nat_lt_cancel_l x n :
  0 ≤ x → x < f n → int_to_nat Z N x < n.
Proof. intros. now apply (strictly_order_reflecting f), int_to_nat_lt_l. Qed.

Lemma int_to_nat_lt_r x y :
  x < y → x < f (int_to_nat Z N y).
Proof. 
  intros E1. destruct (int_to_nat_spec y) as [[? E2]|[? E2]].
   now rewrite E2.
  rewrite E2, preserves_0. now apply lt_le_trans with y.
Qed.

Lemma int_to_nat_lt_cancel_r x n :
  f n < x → n < int_to_nat Z N x.
Proof. intros. now apply (strictly_order_reflecting f), int_to_nat_lt_r. Qed.

Lemma int_to_nat_lt x y :
  0 < y → x < y → int_to_nat Z N x < int_to_nat Z N y.
Proof.
  intros Ey Exy. destruct (total (≤) 0 x).
   now apply int_to_nat_lt_cancel_r, int_to_nat_lt_l.
  rewrite int_to_nat_of_nonpos by easy. now apply int_to_nat_pos.
Qed.

Lemma int_to_nat_lt_back x y :
  0 ≤ y → int_to_nat Z N x < int_to_nat Z N y → x < y.
Proof.
  intros. rewrite <-(int_to_nat_of_nonneg y) by easy.
  apply le_lt_trans with (f (int_to_nat Z N x)).
   now apply int_to_nat_le_r.
  now apply (strictly_order_preserving f).
Qed.
End contents.
