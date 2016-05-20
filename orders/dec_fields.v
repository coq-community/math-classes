Require Import
  Coq.Relations.Relation_Definitions Coq.setoid_ring.Ring
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders MathClasses.theory.rings MathClasses.theory.dec_fields.
Require Export
  MathClasses.orders.rings.

Section contents.
Context `{DecField F} `{Apart F} `{!TrivialApart F} `{!FullPseudoSemiRingOrder Fle Flt} `{∀ x y : F, Decision (x = y)}.
Add Ring F : (stdlib_ring_theory F).

Instance pos_dec_recip_compat x : PropHolds (0 < x) → PropHolds (0 < /x).
Proof.
  intros E.
  apply (strictly_order_reflecting (x *.)).
  rewrite dec_recip_inverse by now apply orders.lt_ne_flip.
  rewrite mult_0_r. solve_propholds.
Qed.

Instance nonneg_dec_recip_compat x : PropHolds (0 ≤ x) → PropHolds (0 ≤ /x).
Proof.
  intros E. red.
  destruct (decide (x = 0)) as [E2 | E2].
   now rewrite E2, dec_recip_0.
  apply lt_le. apply pos_dec_recip_compat.
  apply lt_iff_le_ne. split. easy. now apply not_symmetry.
Qed.

Lemma neg_dec_recip_compat x : x < 0 → /x < 0.
Proof.
  intros. apply flip_neg_negate.
  rewrite dec_recip_negate.
  apply pos_dec_recip_compat.
  now apply flip_neg_negate.
Qed.

Lemma nonpos_dec_recip_compat x : x ≤ 0 → /x ≤ 0.
Proof.
  intros. apply flip_nonpos_negate.
  rewrite dec_recip_negate.
  apply nonneg_dec_recip_compat.
  now apply flip_nonpos_negate.
Qed.

Lemma flip_le_dec_recip x y : 0 < y → y ≤ x  → /x ≤ /y.
Proof with trivial.
  intros E1 E2.
  apply (order_reflecting_pos (.*.) x)...
   now apply lt_le_trans with y.
  rewrite dec_recip_inverse.
   apply (order_reflecting_pos (.*.) y)...
   rewrite (commutativity x), associativity, dec_recip_inverse.
    now ring_simplify.
   now apply lt_ne_flip.
  apply lt_ne_flip.
  now apply lt_le_trans with y.
Qed.

Lemma flip_le_dec_recip_l x y : 0 < y → /y ≤ x  → /x ≤ y.
Proof with trivial.
  intros E1 E2.
  rewrite <-(dec_recip_involutive y).
  apply flip_le_dec_recip...
  now apply pos_dec_recip_compat.
Qed.

Lemma flip_le_dec_recip_r x y : 0 < y → y ≤ /x  → x ≤ /y.
Proof.
  intros E1 E2.
  rewrite <-(dec_recip_involutive x).
  now apply flip_le_dec_recip.
Qed.

Lemma flip_lt_dec_recip x y : 0 < y → y < x  → /x < /y.
Proof.
  intros E1 E2.
  assert (0 < x) by now transitivity y.
  apply (strictly_order_reflecting (x *.)).
  rewrite dec_recip_inverse.
   apply (strictly_order_reflecting (y *.)).
   rewrite (commutativity x), associativity, dec_recip_inverse.
    now ring_simplify.
   now apply lt_ne_flip.
  now apply lt_ne_flip.
Qed.

Lemma flip_lt_dec_recip_l x y : 0 < y → /y < x  → /x < y.
Proof.
  intros E1 E2.
  rewrite <-(dec_recip_involutive y).
  apply flip_lt_dec_recip; trivial.
  now apply pos_dec_recip_compat.
Qed.

Lemma flip_lt_dec_recip_r x y : 0 < y → y < /x  → x < /y.
Proof.
  intros E1 E2.
  rewrite <-(dec_recip_involutive x).
  now apply flip_lt_dec_recip.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 12 (PropHolds (0 ≤ _)) => eapply @nonneg_dec_recip_compat : typeclass_instances.
Hint Extern 12 (PropHolds (0 < _)) => eapply @pos_dec_recip_compat : typeclass_instances.
