Require Import
  Ring interfaces.naturals abstract_algebra interfaces.orders
  orders.nat_int theory.integers theory.rings orders.rings.

Section contents.
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z} `{!FullPseudoSemiRingOrder Zle Zlt} `{Naturals N}.

Add Ring Z : (rings.stdlib_ring_theory Z).

Lemma int_abs_unique_respectful {a b : IntAbs Z N} :
  ((=) ==> (=))%signature (int_abs Z N (ia:=a)) (int_abs Z N (ia:= b)).
Proof.
  intros x y E. unfold int_abs, int_abs_sig.
  apply (injective (naturals_to_semiring N Z)).
  destruct a as [[z1 A]|[z1 A]], b as [[z2 B]|[z2 B]].
     now rewrite A, B.
    symmetry. apply naturals.negate_to_ring. now rewrite A, B, involutive.
   apply naturals.negate_to_ring. now rewrite A, B, involutive.
  apply (injective (-)). now rewrite A, B, !involutive.
Qed.

Lemma int_abs_unique (a b : IntAbs Z N) (z : Z) :
  int_abs Z N (ia:=a) z = int_abs Z N (ia:=a) z.
Proof. now apply int_abs_unique_respectful. Qed.

Context `{!IntAbs Z N}.

Global Instance int_abs_proper: Setoid_Morphism (int_abs Z N) | 0.
Proof. split; try apply _. now apply int_abs_unique_respectful. Qed.

Context `{!SemiRing_Morphism (f : N → Z)}.

Lemma int_abs_spec x :
  { 0 ≤ x ∧ f (int_abs Z N x) = x } + { x ≤ 0 ∧ f (int_abs Z N x) = -x }.
Proof.
  unfold int_abs. destruct int_abs_sig as [[n E]|[n E]].
   left. rewrite <-E. split.
    now apply to_semiring_nonneg.
   apply (naturals.to_semiring_unique_alt _ _).
  right. split.
   apply flip_nonpos_negate. rewrite <-E. now apply to_semiring_nonneg.
  rewrite <-E. now apply (naturals.to_semiring_unique_alt _ _).
Qed.

Lemma int_abs_sig_alt x :
  { n : N | f n = x } + { n : N | f n = -x }.
Proof. destruct (int_abs_spec x) as [[??]|[??]]; eauto. Qed.

Lemma int_abs_nat n :
  int_abs Z N (f n) = n.
Proof.
  apply (injective f). destruct (int_abs_spec (f n)) as [[? E]|[? E]]; intuition.
  apply naturals.negate_to_ring. now rewrite E, involutive.
Qed.

Lemma int_abs_negate_nat n :
  int_abs Z N (-f n) = n.
Proof.
  apply (injective f). destruct (int_abs_spec (-f n)) as [[? E]|[? E]].
   symmetry. now apply naturals.negate_to_ring.
  now rewrite involutive in E.
Qed.

Lemma int_abs_negate x :
  int_abs Z N (-x) = int_abs Z N x.
Proof.
  destruct (int_abs_spec x) as [[_ E]|[_ E]].
   rewrite <-E at 1. now apply int_abs_negate_nat.
  rewrite <-E at 1. now apply int_abs_nat.
Qed.

Lemma int_abs_0_alt x : int_abs Z N x = 0 ↔ x = 0.
Proof.
  split; intros E1.
   destruct (int_abs_spec x) as [[_ E2]|[_ E2]].
    now rewrite <-E2, E1, preserves_0.
   apply flip_negate_0. now rewrite <-E2, E1, preserves_0.
  rewrite E1, <-(preserves_0 (f:=f)). now apply int_abs_nat.
Qed.

Lemma int_abs_ne_0 x : int_abs Z N x ≠ 0 ↔ x ≠ 0.
Proof. destruct (int_abs_0_alt x). intuition. Defined.

Lemma int_abs_0 : int_abs Z N 0 = 0.
Proof. now apply int_abs_0_alt. Qed.

Lemma int_abs_nonneg x :
  0 ≤ x → f (int_abs Z N x) = x.
Proof.
  intros E1. destruct (int_abs_spec x); intuition.
  setoid_replace x with (0 : Z).
   now rewrite int_abs_0, preserves_0.
  now apply (antisymmetry (≤)).
Qed.

Lemma int_abs_nonpos x :
  x ≤ 0 → f (int_abs Z N x) = -x.
Proof.
  intros E. rewrite <-int_abs_negate, int_abs_nonneg; intuition.
  now apply flip_nonpos_negate.
Qed.

Lemma int_abs_1 : int_abs Z N 1 = 1.
Proof.
  apply (injective f). rewrite preserves_1.
  apply int_abs_nonneg; solve_propholds.
Qed.

Lemma int_abs_nonneg_plus x y :
  0 ≤ x → 0 ≤ y → int_abs Z N (x + y) = int_abs Z N x + int_abs Z N y.
Proof.
  intros. apply (injective f).
  rewrite preserves_plus, !int_abs_nonneg; intuition.
  now apply nonneg_plus_compat.
Qed.

Lemma int_abs_mult x y :
  int_abs Z N (x * y) = int_abs Z N x * int_abs Z N y.
Proof.
  apply (injective f). rewrite preserves_mult.
  destruct (int_abs_spec x) as [[? Ex]|[? Ex]],
     (int_abs_spec y) as [[? Ey]|[? Ey]]; rewrite Ex, Ey.
     rewrite int_abs_nonneg. easy. now apply nonneg_mult_compat.
    rewrite int_abs_nonpos. ring. now apply nonneg_nonpos_mult.
   rewrite int_abs_nonpos. ring. now apply nonpos_nonneg_mult.
  rewrite int_abs_nonneg. ring. now apply nonpos_mult.
Qed.
End contents.
