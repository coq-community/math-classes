Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  interfaces.orders abstract_algebra theory.rings.
Require Export 
  orders.semirings.

Section ring_order.
  Context `{Ring R} `{!RingOrder Rle}.
  Add Ring R : (stdlib_ring_theory R).

  Lemma flip_le_opp x y : -y ≤ -x ↔ x ≤ y.
  Proof.
    assert (∀ a b, a ≤ b → -b ≤ -a).
     intros a b E.
     setoid_replace (-b) with (-a + -b + a) by ring.
     setoid_replace (-a) with (-a + -b + b) at 2 by ring.
     now apply (order_preserving _).
    split; intros; auto.
    rewrite <-(opp_involutive x), <-(opp_involutive y); auto.
  Qed.

  Lemma flip_nonneg_opp x : 0 ≤ x ↔ -x ≤ 0. 
  Proof.
    split; intros E.
     rewrite <-opp_0. now apply flip_le_opp.
    apply flip_le_opp. now rewrite opp_0.
  Qed.

  Lemma flip_nonpos_opp x : x ≤ 0 ↔ 0 ≤ -x. 
  Proof.
    rewrite <-(opp_involutive x) at 1. 
    split; intros; now apply flip_nonneg_opp.
  Qed.

  Lemma flip_le_minus_r (x y z : R) : z ≤ y - x ↔ z + x ≤ y.
  Proof.
    split; intros E.
     rewrite commutativity.
     setoid_replace y with (x + (y - x)) by ring.
     now apply (order_preserving _).
    rewrite commutativity.
    setoid_replace z with (-x + (z + x)) by ring.
    now apply (order_preserving _).
  Qed.

  Lemma flip_le_minus_l (x y z : R) : y - x ≤ z ↔ y ≤ z + x.
  Proof.
    rewrite <-(opp_involutive x) at 2.
    split; now apply flip_le_minus_r.
  Qed.

  Lemma flip_nonneg_minus (x y : R) : 0 ≤ y - x ↔ x ≤ y.
  Proof.
    setoid_replace x with (0 + x) at 2 by ring.
    now apply flip_le_minus_r.
  Qed.

  Lemma flip_nonpos_minus (x y : R) : y - x ≤ 0 ↔ y ≤ x.
  Proof.
    setoid_replace x with (0 + x) at 2 by ring.
    now apply flip_le_minus_l.
  Qed.

  Lemma nonneg_minus_compat (x y z : R) : 0 ≤ z → x ≤ y → x - z ≤ y.
  Proof.
    intros E1 E2.
    rewrite commutativity.
    setoid_replace y with (-z + (y + z)) by ring.
    apply (order_preserving (-(z) +)).
    transitivity y; trivial.
    setoid_replace y with (y + 0) at 1 by ring.
    now apply (order_preserving (y +)).
  Qed.

  Lemma nonneg_minus_compat_back (x y z : R) : 0 ≤ z → x ≤ y - z → x ≤ y.
  Proof.
    intros E1 E2.
    transitivity (y - z); trivial.
    now apply nonneg_minus_compat.
  Qed.

  Lemma between_nonneg (x : R) : 0 ≤ x → -x ≤ x.
  Proof.
    intros E.
    transitivity 0; trivial.
    now apply flip_nonneg_opp.
  Qed.

  Global Instance: SemiRingOrder Rle.
  Proof.
    split; try apply _.
     split.
      intros E.
      exists (y - x). split.
       now apply flip_nonneg_minus.
      ring.
     intros [z [Ez1 Ez2]].
     rewrite Ez2, <-(plus_0_r x) at 1.
     now apply (order_preserving (x +)).
    now apply ringorder_mult.
  Qed.
End ring_order.

Section strict_ring_order.
  Context `{Ring R} `{!StrictRingOrder Rlt}.
  Add Ring Rs : (stdlib_ring_theory R).

  Lemma flip_lt_opp x y : -y < -x ↔ x < y.
  Proof.
    assert (∀ a b, a < b → -b < -a).
     intros a b E.
     setoid_replace (-b) with (-a + -b + a) by ring.
     setoid_replace (-a) with (-a + -b + b) at 2 by ring.
     now apply (strictly_order_preserving _).
    split; intros; auto.
    rewrite <-(opp_involutive x), <-(opp_involutive y); auto.
  Qed.

  Lemma flip_pos_opp x : 0 < x ↔ -x < 0. 
  Proof.
    split; intros E.
     rewrite <- opp_0. now apply flip_lt_opp.
    apply flip_lt_opp. now rewrite opp_0.
  Qed.

  Lemma flip_neg_opp x : x < 0 ↔ 0 < -x. 
  Proof.
    rewrite <-(opp_involutive x) at 1. 
    split; intros; now apply flip_pos_opp.
  Qed.

  Lemma flip_lt_minus_r (x y z : R) : z < y - x ↔ z + x < y.
  Proof.
    split; intros E.
     rewrite commutativity.
     setoid_replace y with (x + (y - x)) by ring.
     now apply (strictly_order_preserving _).
    rewrite commutativity.
    setoid_replace z with (-x + (z + x)) by ring.
    now apply (strictly_order_preserving _).
  Qed.

  Lemma flip_lt_minus_l (x y z : R) : y - x < z ↔ y < z + x.
  Proof.
    rewrite <-(opp_involutive x) at 2.
    split; now apply flip_lt_minus_r.
  Qed.

  Lemma flip_pos_minus (x y : R) : 0 < y - x ↔ x < y.
  Proof.
    setoid_replace x with (0 + x) at 2 by ring.
    now apply flip_lt_minus_r.
  Qed.

  Lemma flip_neg_minus (x y : R) : y - x < 0 ↔ y < x.
  Proof.
    setoid_replace x with (0 + x) at 2 by ring.
    now apply flip_lt_minus_l.
  Qed.

  Lemma pos_minus_compat (x y z : R) : 0 < z → x < y → x - z < y.
  Proof.
    intros E1 E2.
    rewrite commutativity.
    setoid_replace y with (-z + (y + z)) by ring.
    apply (strictly_order_preserving (-(z) +)).
    transitivity y; trivial.
    setoid_replace y with (y + 0) at 1 by ring.
    now apply (strictly_order_preserving (y +)).
  Qed.

  Lemma between_pos (x : R) : 0 < x → -x < x.
  Proof.
    intros E.
    transitivity 0; trivial.
    now apply flip_pos_opp.
  Qed.

  Global Instance: StrictSemiRingOrder Rlt.
  Proof.
    split; try apply _.
     split.
      intros E.
      exists (y - x). split.
       now apply flip_pos_minus.
      ring.
     intros [z [Ez1 Ez2]].
     rewrite Ez2, <-(plus_0_r x) at 1.
     now apply (strictly_order_preserving (x +)).
    now apply strict_ringorder_mult.
  Qed.
End strict_ring_order.

Section pseudo_ring_order.
  Context `{Ring R} `{Apart R} `{!PseudoRingOrder Rle Rlt}.
  Add Ring Rp : (stdlib_ring_theory R).

  Instance: StrongSetoid R := pseudo_order_setoid.

  Global Instance: StrictRingOrder Rlt.
  Proof.
    split; try apply _.
    exact pseudo_ringorder_mult.
  Qed.

  Global Instance: PseudoSemiRingOrder Rle Rlt.
  Proof.
    split; try apply _.
      intros x y E1. 
      exists (y - x). split.
       rewrite le_iff_not_lt_flip in E1 |- *. 
       intros E2. apply E1. now apply flip_neg_minus.
      ring.
     exact strict_srorder_plus.
    exact pos_mult_compat.
  Qed.

  Global Instance: RingOrder Rle.
  Proof.
    split; try apply _.
    now apply nonneg_mult_compat.
  Qed.
End pseudo_ring_order.

Section dec_semiring_order.
  Context `{Ring A} `{Apart A} `{!TrivialApart A} `{!RingOrder Rle} 
    `{!NoZeroDivisors A} `{!TotalRelation (≤)} `{∀ x y, Decision (x = y)}.

  Context `{Rlt : Lt A} (lt_correct : ∀ x y, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance: PseudoPartialOrder Rle Rlt := dec_pseudo_partial_order lt_correct.
  Instance: StrongSetoid A := pseudo_order_setoid.

  Instance dec_pseudo_ringorder: PseudoRingOrder (≤) (<).
  Proof.
    split; try apply _.
      apply (strong_setoids.dec_strong_binary_morphism (+)).
     intros z. split; try apply _. intros x y. 
     rewrite !lt_correct. intros [E1a E1b]. split.
      now apply (order_preserving (z+)).
     intros E2. apply E1b.
     now apply (left_cancellation (+) z).
    intros x y. rewrite !lt_correct.
    intros [E1a E1b] [E2a E2b]. split.
     now apply nonneg_mult_compat.
    apply not_symmetry. 
    now apply mult_ne_0; apply not_symmetry.
  Qed.
End dec_semiring_order.

Section another_ring_order.
  Context `{Ring R} `{!RingOrder Rle} `{Ring R2} `{R2le : Le R2}.

  Lemma projected_ringorder (f : R2 → R) `{!SemiRing_Morphism f} `{!Injective f} `{!OrderEmbedding f} : 
    RingOrder R2le.
  Proof.
    split.
      apply (projected_partial_order f).
     repeat (split; try apply _). intros x y E. 
     apply (order_preserving_back f). rewrite 2!preserves_plus.
     apply ringorder_plus. now apply (order_preserving f).
    intros x E1 y E2. 
    apply (order_preserving_back f). rewrite preserves_mult, preserves_0.
    apply ringorder_mult; rewrite <-(preserves_0 (f:=f)); now apply (order_preserving f).
  Qed.

  Context `{!RingOrder R2le} {f : R → R2} `{!SemiRing_Morphism f}.

  Lemma preserving_back_preserves_nonneg : (∀ x, 0 ≤ f x → 0 ≤ x) → OrderPreservingBack f.
  Proof.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply flip_nonneg_minus. apply E.
    rewrite preserves_plus, preserves_opp.
    apply flip_nonneg_minus. now apply F.
  Qed.

  Lemma preserves_ge_opp1 `{!OrderPreserving f} x : -1 ≤ x → -1 ≤ f x.
  Proof. intros. rewrite <-(preserves_1 (f:=f)), <-preserves_opp. now apply (order_preserving f). Qed.

  Lemma preserves_le_opp1 `{!OrderPreserving f} x : x ≤ -1 → f x ≤ -1.
  Proof. intros. rewrite <-(preserves_1 (f:=f)), <-preserves_opp. now apply (order_preserving f). Qed.
End another_ring_order.

Section another_strict_ring_order.
  Context `{Ring R} `{!StrictRingOrder Rlt} `{Ring R2} `{R2lt : Lt R2}.

  Lemma projected_strict_ringorder (f : R2 → R) `{!SemiRing_Morphism f} `{!StrictOrderEmbedding f} : 
    StrictRingOrder R2lt.
  Proof.
    split.
      apply (projected_strict_order f).
     repeat (split; try apply _). intros x y E. 
     apply (strictly_order_preserving_back f). rewrite 2!preserves_plus.
     apply strict_ringorder_plus. now apply (strictly_order_preserving f).
    intros x E1 y E2. 
    apply (strictly_order_preserving_back f). rewrite preserves_mult, preserves_0.
    apply strict_ringorder_mult; rewrite <-(preserves_0 (f:=f)); now apply (strictly_order_preserving f).
  Qed.
End another_strict_ring_order.

Section another_pseudo_ring_order.
  Context `{Ring R} `{Apart R} `{!PseudoRingOrder Rle Rlt} 
    `{Ring R2} `{Apart R2} `{R2le : Le R2} `{R2lt : Lt R2}.

  Lemma projected_pseudo_ringorder (f : R2 → R) `{!SemiRing_Morphism f} `{!StrongInjective f} 
    `{!StrictOrderEmbedding f} `{!OrderEmbedding f} : PseudoRingOrder R2le R2lt.
  Proof.
    pose proof (projected_strict_ringorder f).
    pose proof (projected_pseudo_partial_order f).
    pose proof (pseudo_order_setoid : StrongSetoid R2).
    pose proof (strong_injective_mor f).
    repeat (split; try apply _).
     intros x₁ y₁ x₂ y₂ E.
     apply (strong_injective f) in E. rewrite 2!preserves_mult in E.
     destruct (strong_binary_extensionality (.*.) _ _ _ _ E); [left | right];
      now apply (strong_extensionality f).
    now apply pos_mult_compat.
  Qed.
End another_pseudo_ring_order.
