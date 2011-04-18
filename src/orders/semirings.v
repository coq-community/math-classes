Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra interfaces.orders theory.rings.
Require Export 
  orders.orders orders.maps.

Section semiring_order.
  Context `{SemiRing R} `{!SemiRingOrder Rle}.
  Add Ring R : (stdlib_semiring_theory R).

  Lemma decompose_le {x y} : x ≤ y → ∃ z, 0 ≤ z ∧ y = x + z.
  Proof. intros. now apply srorder_plus. Qed.

  Global Instance: ∀ (z : R), OrderPreserving (z+).
  Proof.
    intros z. repeat (split; try apply _). intros x y E.
    destruct (decompose_le E) as [a [Ea1 Ea2]].
    apply srorder_plus.
    exists a. split. easy.
    now rewrite <-associativity, <-Ea2.
  Qed.

  Global Instance: ∀ (z : R), OrderPreserving (+z).
  Proof. intro. now apply order_preserving_flip. Qed.

  Lemma nonneg_plus_le_compat_r x z : 0 ≤ z → x ≤ x + z.
  Proof. intros E. apply srorder_plus. exists z. now intuition. Qed.

  Lemma nonneg_plus_le_compat_l x z : 0 ≤ z → x ≤ z + x.
  Proof. rewrite commutativity. now apply nonneg_plus_le_compat_r. Qed.

  Lemma plus_le_compat x₁ y₁ x₂ y₂ : x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ + x₂ ≤ y₁ + y₂.
  Proof.
    intros E1 E2.
    transitivity (y₁ + x₂).
     now apply (order_preserving (+ x₂)).
    now apply (order_preserving (y₁ +)).
  Qed.

  Lemma plus_le_compat_r x y z : 0 ≤ z → x ≤ y → x ≤ y + z.
  Proof. intros. rewrite <-(plus_0_r x). now apply plus_le_compat. Qed.

  Lemma plus_le_compat_l x y z : 0 ≤ z → x ≤ y → x ≤ z + y.
  Proof. rewrite commutativity. now apply plus_le_compat_r. Qed.

  Lemma nonpos_plus_compat x y : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
  Proof. intros. rewrite <-(plus_0_r 0). now apply plus_le_compat. Qed.

  Instance nonneg_plus_compat (x y : R) : PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x + y).
  Proof. intros. now apply plus_le_compat_l. Qed.

  Global Instance: ∀ (z : R), PropHolds (0 ≤ z) → OrderPreserving (z *.).
  Proof.
    intros z E. 
    repeat (split; try apply _).
    intros x y F.
    destruct (decompose_le F) as [a [Ea1 Ea2]]. 
    rewrite Ea2, plus_mult_distr_l.
    apply nonneg_plus_le_compat_r.
    now apply nonneg_mult_compat.
  Qed.

  Global Instance: ∀ (z : R), PropHolds (0 ≤ z) → OrderPreserving (.* z).
  Proof. intros. now apply order_preserving_flip. Qed.

  Lemma mult_le_compat x₁ y₁ x₂ y₂ : 
    0 ≤ x₁ → 0 ≤ x₂ → x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ * x₂ ≤ y₁ * y₂.
  Proof.
    intros Ex₁ Ey₁ E1 E2.
    transitivity (y₁ * x₂).
     now apply (order_preserving_flip_nonneg (.*.) x₂).
    apply (order_preserving_nonneg (.*.) y₁); [| easy].
    now transitivity x₁.
  Qed.

  Lemma ge_1_mult_le_compat_r x y z : 1 ≤ z → 0 ≤ y → x ≤ y → x ≤ y * z.
  Proof. 
    intros.
    transitivity y; [easy |].
    rewrite <-(mult_1_r y) at 1.
    now apply (order_preserving_nonneg (.*.) y).
  Qed.

  Lemma ge_1_mult_le_compat_l x y z : 1 ≤ z → 0 ≤ y → x ≤ y → x ≤ z * y.
  Proof. rewrite commutativity. now apply ge_1_mult_le_compat_r. Qed.

  Lemma flip_nonpos_mult_l x y z : z ≤ 0 → x ≤ y → z * y ≤ z * x.
  Proof.
    intros Ez Exy.
    destruct (decompose_le Ez) as [a [Ea1 Ea2]], (decompose_le Exy) as [b [Eb1 Eb2]].
    rewrite Eb2.
    apply srorder_plus. exists (a * b). split.
     now apply nonneg_mult_compat.
    transitivity (z * x + (z + a) * b).
     rewrite <-Ea2. ring.
    ring.
  Qed.

  Lemma flip_nonpos_mult_r x y z : z ≤ 0 → x ≤ y → y * z ≤ x * z.
  Proof.
    rewrite 2!(commutativity _ z).
    now apply flip_nonpos_mult_l.
  Qed.

  Lemma nonpos_mult x y : x ≤ 0 → y ≤ 0 → 0 ≤ x * y.
  Proof.
    intros.
    rewrite <-(mult_0_r x).
    now apply flip_nonpos_mult_l.
  Qed.

  Lemma nonpos_nonneg_mult x y : x ≤ 0 → 0 ≤ y → x * y ≤ 0.
  Proof.
    intros.
    rewrite <-(mult_0_r x).
    now apply flip_nonpos_mult_l.
  Qed.

  Lemma nonneg_nonpos_mult x y : 0 ≤ x → y ≤ 0 → x * y ≤ 0.
  Proof. intros. rewrite commutativity. now apply nonpos_nonneg_mult. Qed.

  Context `{∀ z, LeftCancellation (+) z}.

  Global Instance: ∀ (z : R), OrderPreservingBack (z +).
  Proof. 
    intros z. split; try apply _. intros x y E.
    destruct (decompose_le E) as [a [Ea1 Ea2]].
    apply srorder_plus. exists a. split. easy.
    apply (left_cancellation (+) z). 
    now rewrite associativity.
  Qed.

  Global Instance: ∀ (z : R), OrderPreservingBack (+ z).
  Proof. intros. now apply order_preserving_back_flip. Qed.
End semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 ≤ _ + _)) => eapply @nonneg_plus_compat : typeclass_instances.

Section strict_semiring_order.
  Context `{SemiRing R} `{!StrictSemiRingOrder Rlt}.
  Add Ring Rs : (stdlib_semiring_theory R).

  Lemma decompose_lt {x y} : x < y → ∃ z, 0 < z ∧ y = x + z.
  Proof. intros. now apply strict_srorder_plus. Qed.

  Global Instance: ∀ (z : R), StrictlyOrderPreserving (z+).
  Proof.
    intros z. repeat (split; try apply _). intros x y E.
    destruct (decompose_lt E) as [a [Ea1 Ea2]].
    apply strict_srorder_plus.
    exists a. split. easy.
    now rewrite <-associativity, <-Ea2.
  Qed.

  Global Instance: ∀ (z : R), StrictlyOrderPreserving (+z).
  Proof. intro. now apply strictly_order_preserving_flip. Qed.

  Lemma pos_plus_lt_compat_r x z : 0 < z → x < x + z.
  Proof. intros E. apply <-strict_srorder_plus. exists z. now intuition. Qed.

  Lemma pos_plus_lt_compat_l x z : 0 < z → x < z + x.
  Proof. rewrite commutativity. now apply pos_plus_lt_compat_r. Qed.

  Lemma plus_lt_compat x₁ y₁ x₂ y₂ : x₁ < y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂.
  Proof.
    intros E1 E2.
    transitivity (y₁ + x₂).
     now apply (strictly_order_preserving (+ x₂)).
    now apply (strictly_order_preserving (y₁ +)).
  Qed.

  Lemma plus_lt_compat_r x y z : 0 < z → x < y → x < y + z.
  Proof. intros. rewrite <-(plus_0_r x). now apply plus_lt_compat. Qed.

  Lemma plus_lt_compat_l x y z : 0 < z → x < y → x < z + y.
  Proof. rewrite commutativity. now apply plus_lt_compat_r. Qed.

  Lemma neg_plus_compat x y : x < 0 → y < 0 → x + y < 0.
  Proof. intros. rewrite <-(plus_0_r 0). now apply plus_lt_compat. Qed.

  Instance pos_plus_compat (x y : R) : PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x + y).
  Proof. intros. now apply plus_lt_compat_l. Qed.

  Global Instance: ∀ (z : R), PropHolds (0 < z) → StrictlyOrderPreserving (z *.).
  Proof.
    intros z E. repeat (split; try apply _). intros x y F.
    destruct (decompose_lt F) as [a [Ea1 Ea2]]. 
    rewrite Ea2, plus_mult_distr_l.
    apply pos_plus_lt_compat_r.
    now apply pos_mult_compat.
  Qed.

  Global Instance: ∀ (z : R), PropHolds (0 < z) → StrictlyOrderPreserving (.* z).
  Proof. intros. now apply strictly_order_preserving_flip. Qed.

  Lemma mult_lt_compat x₁ y₁ x₂ y₂ : 
    0 < x₁ → 0 < x₂ → x₁ < y₁ → x₂ < y₂ → x₁ * x₂ < y₁ * y₂.
  Proof.
    intros Ex₁ Ey₁ E1 E2.
    transitivity (y₁ * x₂).
     now apply (strictly_order_preserving_flip_pos (.*.) x₂).
    apply (strictly_order_preserving_pos (.*.) y₁); [| easy ].
    now transitivity x₁.
  Qed.

  Lemma gt_1_mult_lt_compat_r x y z : 1 < z → 0 < y → x < y → x < y * z.
  Proof. 
    intros.
    transitivity y; [ easy |].
    rewrite <-(mult_1_r y) at 1.
    now apply (strictly_order_preserving_pos (.*.) y).
  Qed.

  Lemma gt_1_mult_lt_compat_l x y z : 1 < z → 0 < y → x < y → x < z * y.
  Proof. rewrite commutativity. now apply gt_1_mult_lt_compat_r. Qed.

  Lemma flip_neg_mult_l x y z : z < 0 → x < y → z * y < z * x.
  Proof.
    intros Ez Exy.
    destruct (decompose_lt Ez) as [a [Ea1 Ea2]], (decompose_lt Exy) as [b [Eb1 Eb2]].
    rewrite Eb2.
    apply strict_srorder_plus. exists (a * b). split.
     now apply pos_mult_compat.
    transitivity (z * x + (z + a) * b).
     rewrite <-Ea2. ring.
    ring.
  Qed.

  Lemma flip_neg_mult_r x y z : z < 0 → x < y → y * z < x * z.
  Proof.
    rewrite 2!(commutativity _ z).
    now apply flip_neg_mult_l.
  Qed.

  Lemma neg_mult x y : x < 0 → y < 0 → 0 < x * y.
  Proof.
    intros.
    rewrite <-(mult_0_r x).
    now apply flip_neg_mult_l.
  Qed.

  Lemma neg_pos_mult x y : x < 0 → 0 < y → x * y < 0.
  Proof.
    intros.
    rewrite <-(mult_0_r x).
    now apply flip_neg_mult_l.
  Qed.

  Lemma pos_neg_mult x y : 0 < x → y < 0 → x * y < 0.
  Proof. intros. rewrite commutativity. now apply neg_pos_mult. Qed.

  Context `{∀ z, LeftCancellation (+) z}.

  Global Instance: ∀ (z : R), StrictlyOrderPreservingBack (z +).
  Proof. 
    intros z. split; try apply _. intros x y E.
    apply strict_srorder_plus in E. destruct E as [a [Ea1 Ea2]].
    apply strict_srorder_plus. exists a. split. easy.
    apply (left_cancellation (+) z). 
    now rewrite associativity.
  Qed.

  Global Instance: ∀ (z : R), StrictlyOrderPreservingBack (+ z).
  Proof. intros. apply strictly_order_preserving_back_flip. Qed.
End strict_semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 < _ + _)) => eapply @pos_plus_compat : typeclass_instances.

Section pseudo_semiring_order.
  Context `{SemiRing R} `{Apart R} `{!PseudoSemiRingOrder Rle Rlt}.
  Add Ring Rp : (stdlib_semiring_theory R).

  Instance: StrongSetoid R := pseudo_order_setoid.

  Global Instance: ∀ z, RightCancellation (+) z.
  Proof. intros. now apply (right_cancel_from_left (+)). Qed.

  Global Instance: StrictSemiRingOrder Rlt.
  Proof.
    split; try apply _.
     exact pseudo_srorder_plus_lt.
    exact pseudo_srorder_mult.
  Qed.

  Global Instance: StrongSetoid_BinaryMorphism (+).
  Proof.
    assert (∀ z, StrongSetoid_Morphism (z +)).
     intros. now apply pseudo_partial_order_embedding_inj.
    now apply strong_setoids.strong_binary_setoid_morphism_commutative.
  Qed.

  Global Instance: ∀ z, StrongLeftCancellation (+) z.
  Proof.
    intros z x y.
    rewrite !apart_iff_total_lt.
    intros [|]; [left | right]; now apply (strictly_order_preserving (z +)).
  Qed.

  Global Instance: ∀ z, StrongRightCancellation (+) z.
  Proof. intros. now apply (strong_right_cancel_from_left (+)). Qed.

  Lemma neg_mult_decompose x y : x * y < 0 → (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0).
  Proof.
    intros.
    assert (0 ⪥ x) as Ex.
     apply (strong_extensionality (.* y)).
     rewrite mult_0_l. now apply lt_apart_flip.
    assert (0 ⪥ y) as Ey.
     apply (strong_extensionality (x *.)).
     rewrite mult_0_r. now apply lt_apart_flip.
    rewrite apart_iff_total_lt in Ex, Ey. 
    destruct Ex as [Ex|Ex], Ey as [Ey|Ey]; try tauto.
     destruct (irreflexivity (<) 0).
     transitivity (x * y); [| easy].
     now apply pos_mult_compat.
    destruct (irreflexivity (<) 0).
    transitivity (x * y); [| easy].
    now apply neg_mult.
  Qed.

  Lemma pos_mult_decompose x y : 0 < x * y → (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0).
  Proof.
    intros.
    assert (0 ⪥ x) as Ex.
     apply (strong_extensionality (.* y)).
     rewrite mult_0_l. now apply lt_apart.
    assert (0 ⪥ y) as Ey.
     apply (strong_extensionality (x *.)).
     rewrite mult_0_r. now apply lt_apart.
    rewrite apart_iff_total_lt in Ex, Ey. 
    destruct Ex as [Ex|Ex], Ey as [Ey|Ey]; try tauto.
     destruct (irreflexivity (<) 0).
     transitivity (x * y); [easy |].
     now apply pos_neg_mult.
    destruct (irreflexivity (<) 0).
    transitivity (x * y); [easy |].
    now apply neg_pos_mult.
  Qed.

  Global Instance: SemiRingOrder Rle.
  Proof.
    split; try apply _.
     intros x y. split.
      now apply pseudo_srorder_plus_le.
     intros [z [Ez1 Ez2]].
     rewrite !le_iff_not_lt_flip in Ez1 |- *.
     intros E2. apply Ez1.
     apply (strictly_order_preserving_back (x+)).
     now rewrite <-Ez2, plus_0_r.
    intros x y. rewrite !le_iff_not_lt_flip. intros Ex Ey E.
    destruct (neg_mult_decompose x y); now intuition.
  Qed.

  Global Instance: ∀ (z : R), PropHolds (0 < z) → OrderPreservingBack (z *.).
  Proof. intros z E. now apply pseudo_partial_order_preserving_back. Qed.

  Global Instance: ∀ (z : R), PropHolds (0 < z) → OrderPreservingBack (.* z).
  Proof. intros. now apply order_preserving_back_flip. Qed.

  Global Instance: ∀ (z : R), PropHolds (0 < z) → StrictlyOrderPreservingBack (z *.).
  Proof. intros. apply _. Qed.

  Global Instance: ∀ (z : R), PropHolds (0 < z) → StrictlyOrderPreservingBack (.* z).
  Proof. intros. apply _. Qed.

  Global  Instance: ∀ z, PropHolds (z ⪥ 0) → StrongLeftCancellation (.*.) z.
  Proof.
    intros z Ez x y E. red in Ez.
    rewrite apart_iff_total_lt in E, Ez |- *.
    destruct E as [E|E], Ez as [Ez|Ez].
       right. now apply flip_neg_mult_l.
      left. now apply (strictly_order_preserving_pos (.*.) z).
     left. now apply flip_neg_mult_l.
    right. now apply (strictly_order_preserving_pos (.*.) z).
  Qed.

  Global Instance: ∀ z, PropHolds (z ⪥ 0) → StrongRightCancellation (.*.) z.
  Proof. intros. now apply (strong_right_cancel_from_left (.*.)). Qed.

  Global Instance: ∀ z, PropHolds (z ⪥ 0) → LeftCancellation (.*.) z.
  Proof. intros. now apply _. Qed.

  Global Instance: ∀ z, PropHolds (z ⪥ 0) → RightCancellation (.*.) z.
  Proof. intros. now apply _. Qed.

  Lemma plus_lt_le_compat x₁ y₁ x₂ y₂ : x₁ < y₁ → x₂ ≤ y₂ → x₁ + x₂ < y₁ + y₂.
  Proof.
    intros E1 E2.
    apply lt_le_trans with (y₁ + x₂).
     now apply (strictly_order_preserving (+ x₂)).
    now apply (order_preserving (y₁ +)).
  Qed.

  Lemma plus_le_lt_compat x₁ y₁ x₂ y₂ : x₁ ≤ y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂.
  Proof.
    intros E1 E2.
    apply le_lt_trans with (y₁ + x₂).
     now apply (order_preserving (+ x₂)).
    now apply (strictly_order_preserving (y₁ +)).
  Qed.

  Lemma nonneg_plus_lt_compat_r x y z : 0 ≤ z → x < y → x < y + z.
  Proof. intros. rewrite <-(plus_0_r x). now apply plus_lt_le_compat. Qed.

  Lemma nonneg_plus_lt_compat_l x y z : 0 ≤ z → x < y → x < z + y.
  Proof. intros. rewrite commutativity. now apply nonneg_plus_lt_compat_r. Qed.

  Lemma pos_plus_le_lt_compat_r x y z : 0 < z → x ≤ y → x < y + z.
  Proof. intros. rewrite <-(plus_0_r x). now apply plus_le_lt_compat. Qed.

  Lemma pos_plus_le_lt_compat_l x y z : 0 < z → x ≤ y → x < z + y.
  Proof. intros. rewrite commutativity. now apply pos_plus_le_lt_compat_r. Qed.

  Lemma square_pos x : x ⪥ 0 → 0 < x * x.
  Proof.
    intros E. apply apart_iff_total_lt in E. 
    destruct E as [E|E].
     apply strict_srorder_plus in E. destruct E as [z [Ez1 Ez2]].
     apply strict_srorder_plus. exists (z * z).
     split.
      now apply pos_mult_compat.
     rewrite plus_0_l.
     apply (left_cancellation (+) (x * z)).
     rewrite <-plus_mult_distr_r, <-plus_mult_distr_l.
     rewrite (commutativity z x), <-!Ez2. 
     ring.
    now apply pos_mult_compat.
  Qed.

  Lemma square_nonneg x : 0 ≤ x * x.
  Proof.
    apply not_lt_le_flip. intros E.
    destruct (lt_antisym (x * x) 0).
    split; [easy |].
    apply square_pos.
    apply (strong_extensionality (x *.)).
    rewrite mult_0_r.
    now apply lt_apart.
  Qed.

  Instance le_0_1 : PropHolds (0 ≤ 1).
  Proof. red. setoid_replace 1 with (1 * 1) by ring. now apply square_nonneg. Qed.

  Instance le_0_2 : PropHolds (0 ≤ 2).
  Proof. solve_propholds. Qed.

  Instance le_0_3 : PropHolds (0 ≤ 3).
  Proof. solve_propholds. Qed.

  Instance le_0_4 : PropHolds (0 ≤ 4).
  Proof. solve_propholds. Qed.

  Lemma le_1_2 : 1 ≤ 2.
  Proof. now apply nonneg_plus_le_compat_r, le_0_1. Qed.

  Lemma le_1_3 : 1 ≤ 3.
  Proof. now apply nonneg_plus_le_compat_r, le_0_2. Qed.

  Lemma le_1_4 : 1 ≤ 4.
  Proof. now apply nonneg_plus_le_compat_r, le_0_3. Qed.

  Lemma le_2_3 : 2 ≤ 3.
  Proof. apply (order_preserving (1+)), le_1_2. Qed.

  Lemma le_2_4 : 2 ≤ 4.
  Proof. apply (order_preserving (1+)), le_1_3. Qed.

  Lemma le_3_4 : 3 ≤ 4.
  Proof. apply (order_preserving (1+)), le_2_3. Qed.

  Lemma ge_1_mult_compat x y : 1 ≤ x → 1 ≤ y → 1 ≤ x * y.
  Proof. 
    intros.
    apply ge_1_mult_le_compat_r; trivial. 
    transitivity 1. now apply le_0_1. easy.
  Qed.

  Lemma gt_1_ge_1_mult_compat x y : 1 < x → 1 ≤ y → 1 < x * y.
  Proof. 
    intros. 
    apply lt_le_trans with x; trivial.
    apply ge_1_mult_le_compat_r; try easy.
    transitivity 1. now apply le_0_1. now apply lt_le.
  Qed.

  Lemma ge_1_gt_1_mult_compat x y : 1 ≤ x → 1 < y → 1 < x * y.
  Proof. intros. rewrite commutativity. now apply gt_1_ge_1_mult_compat. Qed.

  Context `{PropHolds (1 ⪥ 0)}.

  Instance lt_0_1 : PropHolds (0 < 1).
  Proof. red. setoid_replace 1 with (1 * 1) by ring. now apply square_pos. Qed.

  Instance lt_0_2 : PropHolds (0 < 2).
  Proof. apply _. Qed.

  Instance lt_0_3 : PropHolds (0 < 3).
  Proof. apply _. Qed.

  Instance lt_0_4 : PropHolds (0 < 4).
  Proof. apply _. Qed.

  Lemma lt_1_2 : 1 < 2.
  Proof. now apply pos_plus_lt_compat_r, lt_0_1. Qed.

  Lemma lt_1_3 : 1 < 3.
  Proof. now apply pos_plus_lt_compat_r, lt_0_2. Qed.

  Lemma lt_1_4 : 1 < 4.
  Proof. now apply pos_plus_lt_compat_r, lt_0_3. Qed.

  Lemma lt_2_3 : 2 < 3.
  Proof. apply (strictly_order_preserving (1+)), lt_1_2. Qed.

  Lemma lt_2_4 : 2 < 4.
  Proof. apply (strictly_order_preserving (1+)), lt_1_3. Qed.

  Lemma lt_3_4 : 3 < 4.
  Proof. apply (strictly_order_preserving (1+)), lt_2_3. Qed.

  Instance apart_0_2 : PropHolds (2 ⪥ 0).
  Proof. red. symmetry. now apply lt_apart, lt_0_2. Qed.

  Lemma not_le_1_0 : ¬1 ≤ 0.
  Proof. now apply lt_not_le_flip, lt_0_1. Qed.

  Lemma not_le_2_0 : ¬2 ≤ 0.
  Proof. now apply lt_not_le_flip, lt_0_2. Qed.
End pseudo_semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 ≤ 1)) => eapply @le_0_1 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 2)) => eapply @le_0_2 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 3)) => eapply @le_0_3 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 4)) => eapply @le_0_4 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 1)) => eapply @lt_0_1 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 2)) => eapply @lt_0_2 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 3)) => eapply @lt_0_3 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 4)) => eapply @lt_0_4 : typeclass_instances.
Hint Extern 7 (PropHolds (2 ⪥ 0)) => eapply @apart_0_2 : typeclass_instances.

Section dec_semiring_order.
  (* Maybe these assumptions can be weakened? *)
  Context `{SemiRing A} `{Apart A} `{!TrivialApart A} `{!SemiRingOrder Rle} 
    `{∀ z : A, LeftCancellation (+) z} `{!NoZeroDivisors A}
    `{!TotalRelation (≤)} `{∀ x y, Decision (x = y)}.

  Context `{Rlt : Lt A} (lt_correct : ∀ x y, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance: PseudoPartialOrder Rle Rlt := dec_pseudo_partial_order lt_correct.
  Instance: StrongSetoid A := pseudo_order_setoid.

  Instance dec_pseudo_srorder: PseudoSemiRingOrder (≤) (<).
  Proof.
    split; try apply _.
       now apply (strong_setoids.dec_strong_binary_morphism (+)).
      now apply srorder_plus.
     intros x y. rewrite lt_correct. split.
      intros [E1a E1b].
      destruct (decompose_le E1a) as [z [? E2]].
      exists z. split; trivial.
      apply lt_correct. split; trivial.
      intros E3. rewrite <-E3, plus_0_r in E2.
      apply E1b. now symmetry.
     intros [z [E1a E1b]]. rewrite E1b. clear E1b.
     apply lt_correct in E1a. destruct E1a as [E1a E1b].
     split.
      now apply nonneg_plus_le_compat_r.
     intros E2. apply E1b. 
     apply (left_cancellation (+) x). now rewrite plus_0_r.
    intros x y. rewrite !lt_correct.
    intros [E1a E1b] [E2a E2b]. split.
     now apply nonneg_mult_compat.
    apply not_symmetry.
    now apply mult_ne_0; apply not_symmetry.
  Qed.
End dec_semiring_order.

Section another_semiring.
  Context `{SemiRing R1} `{SemiRing R2} `{!SemiRingOrder (A:=R1) o1} `{!SemiRingOrder (A:=R2) o2} 
    `{!SemiRing_Morphism (f : R1 → R2)}.

  (* If a morphism agrees on the positive cone then it is order preserving *)    
  Lemma preserving_preserves_nonneg : (∀ x, 0 ≤ x → 0 ≤ f x) → OrderPreserving f.
  Proof.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply srorder_plus in F. destruct F as [z [Ez1 Ez2]].
    apply srorder_plus. exists (f z). split.
     now apply E.
    now rewrite Ez2, preserves_plus.
  Qed.

  Instance preserves_nonneg `{!OrderPreserving f} x : PropHolds (0 ≤ x) → PropHolds (0 ≤ f x).
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_nonpos `{!OrderPreserving f} x : x ≤ 0 → f x ≤ 0.
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_ge_1 `{!OrderPreserving f} x : 1 ≤ x → 1 ≤ f x.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_le_1 `{!OrderPreserving f} x : x ≤ 1 → f x ≤ 1.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (order_preserving f). Qed.
End another_semiring.

Section another_semiring_strict.
  Context `{SemiRing R1} `{SemiRing R2} `{!StrictSemiRingOrder (A:=R1) o1} `{!StrictSemiRingOrder (A:=R2) o2} 
    `{!SemiRing_Morphism (f : R1 → R2)}.

  Instance preserves_pos `{!StrictlyOrderPreserving f} x : PropHolds (0 < x) → PropHolds (0 < f x).
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (strictly_order_preserving f). Qed.

  Lemma preserves_neg `{!StrictlyOrderPreserving f} x : x < 0 → f x < 0.
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (strictly_order_preserving f). Qed.

  Lemma preserves_gt_1 `{!StrictlyOrderPreserving f} x : 1 < x → 1 < f x.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (strictly_order_preserving f). Qed.

  Lemma preserves_lt_1 `{!StrictlyOrderPreserving f} x : x < 1 → f x < 1.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (strictly_order_preserving f). Qed.
End another_semiring_strict.

(* Due to bug #2528 *)
Hint Extern 15 (PropHolds (_ ≤ _ _)) => eapply @preserves_nonneg : typeclass_instances.
Hint Extern 15 (PropHolds (_ < _ _)) => eapply @preserves_pos : typeclass_instances.
