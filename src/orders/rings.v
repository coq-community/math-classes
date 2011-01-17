Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra theory.rings.
Require Export 
  orders.orders orders.maps.

Section contents.
Context `{Ring R} `{!RingOrder o}.
Add Ring R : (stdlib_ring_theory R).

Lemma flip_inv x y : x ≤ y ↔ -y ≤ -x.
Proof with auto.
  assert (∀ a b, a ≤ b → -b ≤ -a).
   intros a b E.
   setoid_replace (-b) with (-a + -b + a) by ring.
   setoid_replace (-a) with (-a + -b + b) at 2 by ring.
   apply (order_preserving _)...
  split; intros...
  rewrite <-(inv_involutive x), <-(inv_involutive y)...
Qed.

Lemma flip_inv_strict x y : x < y ↔ -y < -x.
Proof with auto.
  assert (∀ a b, a < b → -b < -a).
   intros a b [E1 E2].
   split.
    apply ->flip_inv...
   intros E3. apply E2. apply (injective (-)). symmetry...
  split; intros...
  rewrite <-(inv_involutive x), <-(inv_involutive y)...
Qed.

Lemma flip_nonneg_inv x : 0 ≤ x ↔ -x ≤ 0. 
Proof with eauto.
  split; intros E.
   rewrite <- opp_0... apply ->flip_inv...
  apply flip_inv. rewrite opp_0...
Qed.

Lemma flip_nonpos_inv x : x ≤ 0 ↔ 0 ≤ -x. 
Proof with auto.
  rewrite <-(inv_involutive x) at 1. 
  split; intros; apply flip_nonneg_inv; auto.
Qed.

Lemma flip_pos_inv x : 0 < x ↔ -x < 0. 
Proof with eauto.
  split; intros E.
   rewrite <- opp_0... apply ->flip_inv_strict...
  apply flip_inv_strict. rewrite opp_0...
Qed.

Lemma flip_neg_inv x : x < 0 ↔ 0 < -x. 
Proof with auto.
  rewrite <-(inv_involutive x) at 1. 
  split; intros; apply flip_pos_inv; auto.
Qed.

Lemma flip_nonneg_minus (x y : R) : 0 ≤ y + -x ↔ x ≤ y.
Proof with auto.
  split; intros E.
   setoid_replace x with (x + 0) by ring.
   setoid_replace y with (x + (y + -x)) by ring.
   apply (order_preserving _)...
  rewrite commutativity.
  setoid_replace 0 with (-x + x) by ring.
  apply (order_preserving _)...
Qed.

Lemma flip_nonpos_minus (x y : R) : y + -x ≤ 0 ↔ y ≤ x.
Proof with auto.
  split; intros E.
   apply flip_nonneg_minus, flip_nonneg_inv.
   rewrite <-opp_swap...
  rewrite opp_swap.
  apply flip_nonneg_inv, flip_nonneg_minus...
Qed.

Lemma precedes_plus x y : x ≤ y ↔ ∃ z, 0 ≤ z ∧ y = x + z.
Proof with trivial.
  split.
   intros E.
   exists (y + - x). split.
    apply flip_nonneg_minus...
   ring.
  intros [z [Ez1 Ez2]].
  rewrite Ez2, <-(plus_0_r x) at 1.
  apply (order_preserving (x +))...
Qed.

Global Instance: SemiRingOrder o.
Proof.
  repeat (split; try apply _). 
    apply precedes_plus. 
   apply precedes_plus.
  apply ringorder_mult.
Qed.

Lemma nonpos_mult x y : x ≤ 0 → y ≤ 0 → 0 ≤ x * y.
Proof.
  intros E F.
  setoid_replace (x * y) with (-x * -y) by ring.
  apply ringorder_mult; apply flip_nonpos_inv; assumption.
Qed.

Lemma nonpos_nonneg_mult x y : x ≤ 0 → 0 ≤ y → x * y ≤ 0.
Proof with auto.
  intros E F. 
  apply flip_nonpos_inv. 
  rewrite rings.distr_opp_mult_l. 
  apply ringorder_mult...
  apply flip_nonpos_inv...
Qed.

Lemma nonneg_nonpos_mult x y : 0 ≤ x → y ≤ 0 → x * y ≤ 0.
Proof with auto.
  intros E F.
  rewrite commutativity. 
  apply nonpos_nonneg_mult...
Qed.

Context `{!TotalOrder o}.

Lemma square_nonneg x : 0 ≤ x * x.
Proof with auto.
  destruct (total_order 0 x).
   apply ringorder_mult...
  setoid_replace (x * x) with (-x * -x) by ring.
  apply ringorder_mult; apply flip_nonpos_inv...
Qed.

Lemma eq_opp_self (z : R) : z = -z → z = 0.
Proof with auto.
  intros E.
  apply (antisymmetry (≤)); destruct (total_order 0 z)...
    rewrite E. apply flip_nonneg_inv...
  rewrite E. apply flip_nonpos_inv...
Qed.
End contents.

Section another_ring.
  Context `{Ring R} `{!RingOrder o} `{Ring R2} `{o2 : Order R2} `{!RingOrder o2} {f : R → R2} `{!SemiRing_Morphism f}.

  Lemma preserving_back_preserves_0 : (∀ x, 0 ≤ f x → 0 ≤ x) → OrderPreservingBack f.
  Proof with trivial.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply flip_nonneg_minus. apply E.
    rewrite preserves_plus, preserves_inv.
    apply flip_nonneg_minus. apply F.
  Qed.
End another_ring.
