Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra theory.rings theory.fields.
Require Export
  orders.semirings.

Section contents.
Context `{Field F} `{!RingOrder o} `{!TotalOrder o} `{!DecMultInv F} `{∀ x y : F, Decision (x = y)}.
Add Ring F : (stdlib_ring_theory F).

Global Instance pos_dec_mult_inv_compat x : PropHolds (0 < x) → PropHolds (0 < /x).
Proof.
  intros E.
  assert (PropHolds (x ≠ 0)) by now apply orders.sprecedes_ne_flip.
  split.
   apply (order_preserving_back (x *.)).
    rewrite dec_mult_inverse.
    ring_simplify. now apply precedes_0_1.
   easy.
  apply not_symmetry. solve_propholds.
Qed.

Global Instance nonneg_dec_mult_inv_compat x : PropHolds (0 ≤ x) → PropHolds (0 ≤ /x).
Proof.
  intros E. red.
  destruct (decide (x = 0)) as [E2 | E2].
   now rewrite E2, dec_mult_inv_0. 
  apply pos_dec_mult_inv_compat.
  split. easy. now apply not_symmetry.
Qed.

Lemma neg_dec_mult_inv_compat x : x < 0 → /x < 0.
Proof.
  intros. apply flip_neg_opp.
  rewrite dec_mult_inv_opp.
  apply pos_dec_mult_inv_compat.
  now apply flip_neg_opp.
Qed.

Lemma nonpos_dec_mult_inv_compat x : x ≤ 0 → /x ≤ 0.
Proof.
  intros. apply flip_nonpos_opp.
  rewrite dec_mult_inv_opp.
  apply nonneg_dec_mult_inv_compat.
  now apply flip_nonpos_opp.
Qed.

Lemma flip_dec_mult_inv x y : 0 < y → y ≤ x  → /x ≤ /y.
Proof with trivial.
  intros E1 E2.
  apply (order_preserving_back_gt_0 (.*.) x)...
   now apply sprecedes_trans_l with y.
  rewrite dec_mult_inverse.
   apply (order_preserving_back_gt_0 (.*.) y)...
   rewrite (commutativity x), associativity, dec_mult_inverse.
    now ring_simplify.
   now apply not_symmetry, neq_precedes_sprecedes.
  apply not_symmetry, neq_precedes_sprecedes.
  now apply sprecedes_trans_l with y.
Qed.

Lemma flip_dec_mult_inv_l x y : 0 < y → /y ≤ x  → /x ≤ y.
Proof with trivial.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive y).
  apply flip_dec_mult_inv...
  now apply pos_dec_mult_inv_compat.
Qed.

Lemma flip_dec_mult_inv_r x y : 0 < y → y ≤ /x  → x ≤ /y.
Proof.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive x).
  now apply flip_dec_mult_inv.
Qed.

Lemma precedes_0_half : 0 ≤ 1/2.
Proof.
  apply (order_preserving_back (.* 2)).
  ring_simplify.
  rewrite dec_mult_inverse.
   apply precedes_0_1.
  apply (ne_0 2).
Qed.
End contents.
