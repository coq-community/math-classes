Require Import
  Relation_Definitions Ring
  abstract_algebra interfaces.orders theory.rings theory.dec_fields.
Require Export
  orders.rings.

Section contents.
Context `{DecField F} `{Apart F} `{!TrivialApart F} `{!FullPseudoSemiRingOrder Fle Flt} `{∀ x y : F, Decision (x = y)}.
Add Ring F : (stdlib_ring_theory F).

Instance pos_dec_mult_inv_compat x : PropHolds (0 < x) → PropHolds (0 < /x).
Proof.
  intros E.
  apply (strictly_order_preserving_back (x *.)).
  rewrite dec_mult_inverse by now apply orders.lt_ne_flip.
  rewrite mult_0_r. solve_propholds.
Qed.

Instance nonneg_dec_mult_inv_compat x : PropHolds (0 ≤ x) → PropHolds (0 ≤ /x).
Proof.
  intros E. red.
  destruct (decide (x = 0)) as [E2 | E2].
   now rewrite E2, dec_mult_inv_0. 
  apply lt_le. apply pos_dec_mult_inv_compat.
  apply lt_iff_le_ne. split. easy. now apply not_symmetry.
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

Lemma flip_le_dec_mult_inv x y : 0 < y → y ≤ x  → /x ≤ /y.
Proof with trivial.
  intros E1 E2.
  apply (order_preserving_back_pos (.*.) x)...
   now apply lt_le_trans with y.
  rewrite dec_mult_inverse.
   apply (order_preserving_back_pos (.*.) y)...
   rewrite (commutativity x), associativity, dec_mult_inverse.
    now ring_simplify.
   now apply lt_ne_flip.
  apply lt_ne_flip.
  now apply lt_le_trans with y.
Qed.

Lemma flip_le_dec_mult_inv_l x y : 0 < y → /y ≤ x  → /x ≤ y.
Proof with trivial.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive y).
  apply flip_le_dec_mult_inv...
  now apply pos_dec_mult_inv_compat.
Qed.

Lemma flip_le_dec_mult_inv_r x y : 0 < y → y ≤ /x  → x ≤ /y.
Proof.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive x).
  now apply flip_le_dec_mult_inv.
Qed.

Lemma flip_lt_dec_mult_inv x y : 0 < y → y < x  → /x < /y.
Proof.
  intros E1 E2.
  assert (PropHolds (0 < x)) by (red; now transitivity y).
  apply (strictly_order_preserving_back (x *.)).
  rewrite dec_mult_inverse.
   assert (PropHolds (0 < y)) by easy.
   apply (strictly_order_preserving_back (y *.)).
   rewrite (commutativity x), associativity, dec_mult_inverse.
    now ring_simplify.
   now apply lt_ne_flip.
  now apply lt_ne_flip.
Qed.

Lemma flip_lt_dec_mult_inv_l x y : 0 < y → /y < x  → /x < y.
Proof.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive y).
  apply flip_lt_dec_mult_inv; trivial.
  now apply pos_dec_mult_inv_compat.
Qed.

Lemma flip_lt_dec_mult_inv_r x y : 0 < y → y < /x  → x < /y.
Proof.
  intros E1 E2.
  rewrite <-(dec_mult_inv_involutive x).
  now apply flip_lt_dec_mult_inv.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 12 (PropHolds (0 ≤ _)) => eapply @nonneg_dec_mult_inv_compat : typeclass_instances.
Hint Extern 12 (PropHolds (0 < _)) => eapply @pos_dec_mult_inv_compat : typeclass_instances.
