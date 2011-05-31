Require Import
  Relation_Definitions Ring
  abstract_algebra interfaces.orders theory.rings.
Require Export 
  orders.semirings.

Section from_ring_order.
  Context `{Ring R} `{!PartialOrder Rle}
    (plus_spec : ∀ z, OrderPreserving (z +))
    (mult_spec : ∀ x y, PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y)).

  Lemma from_ring_order: SemiRingOrder (≤).
  Proof.
    repeat (split; try apply _). 
     intros x y E. exists (- x + y). 
     now rewrite associativity, plus_opp_r, plus_0_l.
    intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_opp_l z), <-!associativity.
    now apply (order_preserving _).
  Qed.
End from_ring_order.

Section from_strict_ring_order.
  Context `{Ring R} `{!StrictSetoidOrder Rle}
    (plus_spec : ∀ z, StrictlyOrderPreserving (z +))
    (mult_spec : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y)).

  Lemma from_strict_ring_order: StrictSemiRingOrder (<).
  Proof.
    repeat (split; try apply _). 
     intros x y E. exists (- x + y). 
     now rewrite associativity, plus_opp_r, plus_0_l.
    intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_opp_l z), <-!associativity.
    now apply (strictly_order_preserving _).
  Qed.
End from_strict_ring_order.

Section from_pseudo_ring_order.
  Context `{Ring R} `{Apart R} `{!PseudoOrder Rlt}
    (plus_spec : ∀ z, StrictlyOrderPreserving (z +))
    (mult_ext : StrongSetoid_BinaryMorphism (.*.))
    (mult_spec : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y)).

  Lemma from_pseudo_ring_order: PseudoSemiRingOrder (<).
  Proof.
    repeat (split; try apply _).
     intros x y E. exists (- x + y). 
     now rewrite associativity, plus_opp_r, plus_0_l.
    intros x y E.
    rewrite <-(plus_0_l x), <-(plus_0_l y), <-!(plus_opp_l z), <-!associativity.
    now apply (strictly_order_preserving _).
  Qed.
End from_pseudo_ring_order.

Section from_full_pseudo_ring_order.
  Context `{Ring R} `{Apart R} `{!FullPseudoOrder Rle Rlt}
    (plus_spec : ∀ z, StrictlyOrderPreserving (z +))
    (mult_ext : StrongSetoid_BinaryMorphism (.*.))
    (mult_spec : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y)).

  Lemma from_full_pseudo_ring_order: FullPseudoSemiRingOrder (≤) (<).
  Proof.
    split.
     now apply from_pseudo_ring_order.
    now apply le_iff_not_lt_flip.
  Qed.
End from_full_pseudo_ring_order.

Section ring_order.
  Context `{Ring R} `{!SemiRingOrder Rle}.
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
End ring_order.

Section strict_ring_order.
  Context `{Ring R} `{!StrictSemiRingOrder Rlt}.
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
End strict_ring_order.

Section another_ring_order.
  Context `{Ring R1} `{!SemiRingOrder R1le} `{Ring R2} `{R2le : Le R2}.

  Lemma projected_ring_order (f : R2 → R1) `{!SemiRing_Morphism f} `{!Injective f} `{!OrderEmbedding f} : 
    SemiRingOrder R2le.
  Proof.
    pose proof (projected_partial_order f).
    apply from_ring_order.
     repeat (split; try apply _). intros x y E. 
     apply (order_reflecting f). rewrite 2!preserves_plus.
     now do 2 apply (order_preserving _).
    intros x y E1 E2. 
    apply (order_reflecting f). 
    rewrite preserves_mult, preserves_0.
    solve_propholds.
  Qed.

  Context `{!SemiRingOrder R2le} {f : R1 → R2} `{!SemiRing_Morphism f}.

  Lemma reflecting_preserves_nonneg : (∀ x, 0 ≤ f x → 0 ≤ x) → OrderReflecting f.
  Proof.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply flip_nonneg_minus, E.
    rewrite preserves_plus, preserves_opp.
    now apply flip_nonneg_minus, F.
  Qed.

  Lemma preserves_ge_opp1 `{!OrderPreserving f} x : -1 ≤ x → -1 ≤ f x.
  Proof. intros. rewrite <-(preserves_1 (f:=f)), <-preserves_opp. now apply (order_preserving f). Qed.

  Lemma preserves_le_opp1 `{!OrderPreserving f} x : x ≤ -1 → f x ≤ -1.
  Proof. intros. rewrite <-(preserves_1 (f:=f)), <-preserves_opp. now apply (order_preserving f). Qed.
End another_ring_order.

Section another_strict_ring_order.
  Context `{Ring R1} `{!StrictSemiRingOrder R1lt} `{Ring R2} `{R2lt : Lt R2}.

  Lemma projected_strict_ring_order (f : R2 → R1) `{!SemiRing_Morphism f} `{!StrictOrderEmbedding f} : 
    StrictSemiRingOrder R2lt.
  Proof.
    pose proof (projected_strict_order f).
    apply from_strict_ring_order.
     repeat (split; try apply _). intros x y E. 
     apply (strictly_order_reflecting f). rewrite 2!preserves_plus.
     now do 2 apply (strictly_order_preserving _).
    intros x y E1 E2. 
    apply (strictly_order_reflecting f). rewrite preserves_mult, preserves_0.
    solve_propholds.
  Qed.
End another_strict_ring_order.

Section another_pseudo_ring_order.
  Context `{Ring R1} `{Apart R1} `{!PseudoSemiRingOrder R1lt} 
    `{Ring R2} `{Apart R2} `{R2lt : Lt R2}.

  Lemma projected_pseudo_ring_order (f : R2 → R1) `{!SemiRing_Morphism f} `{!StrongInjective f} 
    `{!StrictOrderEmbedding f} : PseudoSemiRingOrder R2lt.
  Proof.
    pose proof (projected_pseudo_order f).
    pose proof (projected_strict_ring_order f).
    apply from_pseudo_ring_order; try apply _.
    pose proof (pseudo_order_setoid : StrongSetoid R1).
    pose proof (pseudo_order_setoid : StrongSetoid R2).
    pose proof (strong_injective_mor f).
    repeat (split; try apply _).
    intros x₁ y₁ x₂ y₂ E.
    apply (strong_injective f) in E. rewrite 2!preserves_mult in E.
    destruct (strong_binary_extensionality (.*.) _ _ _ _ E); [left | right]; now apply (strong_extensionality f).
  Qed.
End another_pseudo_ring_order.

Section another_full_pseudo_ring_order.
  Context `{Ring R1} `{Apart R1} `{!FullPseudoSemiRingOrder R1le R1lt} 
    `{Ring R2} `{Apart R2} `{R2le : Le R2} `{R2lt : Lt R2}.

  Lemma projected_full_pseudo_ring_order (f : R2 → R1) `{!SemiRing_Morphism f} `{!StrongInjective f} 
    `{!StrictOrderEmbedding f} `{!OrderEmbedding f} : FullPseudoSemiRingOrder R2le R2lt.
  Proof.
    pose proof (projected_full_pseudo_order f).
    pose proof (projected_pseudo_ring_order f).
    split; try apply _.
    apply le_iff_not_lt_flip.
  Qed.
End another_full_pseudo_ring_order.
