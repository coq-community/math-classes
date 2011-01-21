Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra theory.rings theory.fields.
Require Export
  orders.semirings.

Section contents.
Context `{Field F} `{!RingOrder o} `{!TotalOrder o} `{!DecMultInv F} `{∀ x y : F, Decision (x = y)}.
Add Ring F : (stdlib_ring_theory F).

Lemma pos_dec_mult_inv_compat x : 0 < x → 0 < /x.
Proof with trivial.
  intros E.
  split.
   apply (order_preserving_back_gt_0 (.*.) x)...
   rewrite dec_mult_inverse.
    ring_simplify. apply precedes_0_1.
   apply not_symmetry, neq_precedes_sprecedes...
  apply not_symmetry, dec_mult_inv_nonzero.
  apply not_symmetry, neq_precedes_sprecedes...
Qed.

Lemma nonneg_dec_mult_inv_compat x : 0 ≤ x → 0 ≤ /x.
Proof with trivial.
  intros E.
  destruct (decide (x = 0)) as [E2 | E2].
   rewrite E2, dec_mult_inv_0. reflexivity.
  apply pos_dec_mult_inv_compat.
  split... apply not_symmetry...
Qed.

Lemma flip_dec_mult_inv x y : 0 < y → y ≤ x  → /x ≤ /y.
Proof with trivial.
  intros E1 E2.
  apply (order_preserving_back_gt_0 (.*.) x)...
   apply sprecedes_trans_l with y...
  rewrite dec_mult_inverse.
   apply (order_preserving_back_gt_0 (.*.) y)...
   rewrite (commutativity x), associativity, dec_mult_inverse.
    ring_simplify...
   apply not_symmetry, neq_precedes_sprecedes...
  apply not_symmetry, neq_precedes_sprecedes.
  apply sprecedes_trans_l with y...
Qed.

Lemma flip_dec_mult_inv_l x y : 0 < y → /y ≤ x  → /x ≤ y.
Proof with trivial.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive y).
  apply flip_dec_mult_inv...
  apply pos_dec_mult_inv_compat...
Qed.

Lemma flip_dec_mult_inv_r x y : 0 < y → y ≤ /x  → x ≤ /y.
Proof with trivial.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive x).
  apply flip_dec_mult_inv...
Qed.
End contents.
