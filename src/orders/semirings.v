Require Export
  orders.rings.
Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra theory.rings
  implementations.semiring_pairs orders.orders orders.maps.

Section contents.
Context `{SemiRing R} `{!SemiRingOrder o}.
Add Ring R : (stdlib_semiring_theory R).

Global Instance: ∀ (z : R), OrderPreserving ((+) z).
Proof with trivial.
  intros z. repeat (split; try apply _). intros x y E.
  apply srorder_plus in E. destruct E as [a [Ea1 Ea2]].
  apply srorder_plus.
  exists a. split...
  rewrite <-associativity, <-Ea2. reflexivity.
Qed.

Global Instance: ∀ (z : R), OrderPreserving (flip (+) z).
Proof. intro. apply order_preserving_flip. Qed.

Lemma plus_compat x1 y1 x2 y2 : x1 ≤ y1 → x2 ≤ y2 → x1 + x2 ≤ y1 + y2.
Proof with auto.
  intros E1 E2.
  apply transitivity with (y1 + x2).
   apply (order_preserving (flip (+) x2))...
  apply (order_preserving ((+) y1))...
Qed.

Lemma nonneg_plus_compat_r x y z : z ≤ x → 0 ≤ y → z ≤ x + y.
Proof. intros. rewrite <-(plus_0_r z). apply plus_compat; assumption. Qed.

Lemma nonneg_plus_compat_l x y z : 0 ≤ x → z ≤ y → z ≤ x + y.
Proof. intros. rewrite <-(plus_0_l z). apply plus_compat; assumption. Qed.

Lemma nonneg_plus_compat x y : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
Proof. apply nonneg_plus_compat_r. Qed.

Lemma nonpos_plus_compat x y : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof. intros. rewrite <-(plus_0_r 0). apply plus_compat; assumption. Qed.

Lemma nonneg_mult_compat (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof. intros. apply srorder_mult; assumption. Qed.

Lemma nonneg_mult_compat_both x1 y1 x2 y2 : 
  0 ≤ x1 → 0 ≤ y1 → x1 ≤ x2 → y1 ≤ y2 → x1 * y1 ≤ x2 * y2.
Proof with auto using nonneg_mult_compat.
  intros E1x E1y E2x E2y. 
  eapply srorder_plus in E2x. eapply srorder_plus in E2y.
  destruct E2x as [a [? E3x]], E2y as [b [? E3y]].
  rewrite E3x, E3y.
  ring_simplify.
  apply nonneg_plus_compat_r...
  apply nonneg_plus_compat_r...
  apply nonneg_plus_compat_r...
  reflexivity.
Qed.

Global Instance mult_compat: ∀ (z : R), GeZero z → OrderPreserving (ring_mult z).
Proof with auto.
  intros z E. 
  repeat (split; try apply _).
  intros x y F.
  apply srorder_plus in F. destruct F as [a [Ea1 Ea2]]. 
  rewrite Ea2. 
  setoid_replace (z * (x + a)) with (z * x + z * a) by ring.
  apply nonneg_plus_compat_r.
   reflexivity.
  apply srorder_mult...
Qed.

Global Instance: ∀ (z : R), GeZero z → OrderPreserving (flip ring_mult z).
Proof. intros. apply order_preserving_flip. Qed.

Context `{∀ z, LeftCancellation (+) z}.

Global Instance: ∀ (z : R), OrderPreservingBack ((+) z).
Proof with auto. 
  intros z.
  repeat (split; try apply _). 
  intros x y E.
  apply srorder_plus in E. destruct E as [a [Ea1 Ea2]].
  apply srorder_plus. exists a. split...
  apply (left_cancellation (+) z). 
  rewrite associativity...
Qed.

Global Instance: ∀ (z : R), OrderPreservingBack (flip (+) z).
Proof. intros. apply order_preserving_back_flip. Qed.

Context `{!TotalOrder (≤)} `{∀ z, NeZero z → LeftCancellation ring_mult z}.

Global Instance ring_mult_compat_back : ∀ (z : R), GtZero z → OrderPreservingBack (ring_mult z).
Proof with auto.
  intros z E.
  repeat (split; try apply _). 
  intros x y F.
  destruct (total_order x y) as [G|G]...
  apply (order_preserving_ge_0 ring_mult z) in G.
   apply equiv_precedes.
   apply (left_cancellation_ne_0 ring_mult z).
    apply not_symmetry, neq_precedes_sprecedes...
   eapply (antisymmetry (≤))...
  apply sprecedes_weaken...
Qed.

Global Instance: ∀ (z : R), GtZero z → OrderPreservingBack (flip ring_mult z).
Proof. intros. apply order_preserving_back_flip. Qed.

Global Instance: ∀ (z : R), StrictlyOrderPreserving ((+) z).
Proof with trivial.
  intros z.
  split; try apply _.
  intros x y [E1 E2]. split.
   apply (order_preserving ((+) z))...
  intros F. apply E2.
  apply (left_cancellation (+) z)...
Qed.

Global Instance: ∀ (z : R), StrictlyOrderPreserving (flip (+) z).
Proof. 
  intros z.
  split; try apply _.
  intros x y E.
  unfold flip. do 2 rewrite (commutativity _ z).
  apply (strictly_order_preserving ((+) z)). assumption.
Qed.

Lemma plus_scompat_l x1 y1 x2 y2 : x1 < y1 → x2 ≤ y2 → x1 + x2 < y1 + y2.
Proof with auto.
  intros E1 E2.
  apply sprecedes_trans_l with (y1 + x2).
   apply (strictly_order_preserving (flip (+) x2))...
  apply (order_preserving ((+) y1))...
Qed.

Lemma plus_scompat_r x1 y1 x2 y2 : x1 ≤ y1 → x2 < y2 → x1 + x2 < y1 + y2.
Proof with auto.
  intros E1 E2.
  apply sprecedes_trans_r with (y1 + x2).
   apply (order_preserving (flip (+) x2))...
  apply (strictly_order_preserving ((+) y1))...
Qed.

Lemma nonneg_plus_scompat_r x y z : z < x → 0 ≤ y → z < x + y.
Proof. intros. rewrite <-(plus_0_r z). apply plus_scompat_l; assumption. Qed.

Lemma nonneg_plus_scompat_l x y z : 0 ≤ x → z < y → z < x + y.
Proof. intros. rewrite <-(plus_0_l z). apply plus_scompat_r; assumption. Qed.

Lemma pos_plus_compat_r x y z : z ≤ x → 0 < y → z < x + y.
Proof. intros. rewrite <-(plus_0_r z). apply plus_scompat_r; assumption. Qed.

Lemma pos_plus_compat_l x y z : 0 < x → z ≤ y → z < x + y.
Proof. intros. rewrite <-(plus_0_l z). apply plus_scompat_l; assumption. Qed.

Lemma pos_plus_compat x y : 0 < x → 0 < y → 0 < x + y.
Proof. intros. apply pos_plus_compat_r. apply sprecedes_weaken. trivial. trivial. Qed.

Global Instance: ∀ (z : R), GtZero z → StrictlyOrderPreserving (ring_mult z).
Proof with trivial.
  intros z Ez.
  split; try apply _.
  intros x y [E1 E2]. split.
   apply (order_preserving_ge_0 ring_mult z)... apply sprecedes_weaken...
  intros F. apply E2.
  apply (left_cancellation_ne_0 ring_mult z)... apply not_symmetry, neq_precedes_sprecedes...
Qed.

Global Instance: ∀ (z : R), GtZero z → StrictlyOrderPreserving (flip ring_mult z).
Proof. 
  intros z.
  split; try apply _.
  intros x y E.
  unfold flip. do 2 rewrite (commutativity _ z).
  apply (strictly_order_preserving (ring_mult z)). assumption.
Qed.

Lemma pos_mult_compat x y : 0 < x → 0 < y → 0 < x * y.
Proof. 
  intros E F.
  rewrite <-(mult_0_r x).
  assert (GtZero x). assumption.
  apply (strictly_order_preserving (ring_mult x)). assumption.
Qed.

Lemma square_nonneg x : 0 ≤ x * x.
Proof with auto.
  apply (order_preserving_back SRpair_inject).
  rewrite preserves_mult.
  apply square_nonneg.
Qed.

Lemma precedes_0_1 : 0 ≤ 1.
Proof. setoid_replace 1 with (1 * 1) by ring. apply square_nonneg. Qed.

Lemma sprecedes_0_1 `{!NeZero (1:R)} : 0 < 1.
Proof.
  split. 
   apply (precedes_0_1). 
  apply not_symmetry. apply (ne_zero 1).
Qed.

Lemma precedes_0_2 : 0 ≤ 2.
Proof. apply nonneg_plus_compat; apply precedes_0_1. Qed.

Lemma precedes_1_2 : 1 ≤ 2.
Proof. apply nonneg_plus_compat_l. apply precedes_0_1. reflexivity. Qed.

Lemma not_precedes_1_0 `{!NeZero (1:R)} : ¬1 ≤ 0.
Proof.
  intros E.
  apply (ne_zero (1:R)).
  eapply (antisymmetry (≤)); eauto.
  apply precedes_0_1.
Qed.

Global Instance ne_0_2 `{!NeZero (1:R)} : NeZero (2 : R).
Proof.
  intro E.
  apply not_precedes_1_0.
  rewrite <-E.
  apply precedes_1_2.
Qed.

Lemma not_precedes_2_0 `{!NeZero (1:R)} : ¬2 ≤ 0.
Proof.
  intros E.
  apply (ne_zero (2:R)).
  eapply (antisymmetry (≤)); eauto.
  apply precedes_0_2.
Qed.

(* If a morphism agrees on the positive cone then it is order preserving *)
Section another_semiring.
  Context `{SemiRing R2} `{o2 : Order R2} `{!SemiRingOrder o2} {f : R → R2} `{!SemiRing_Morphism f}.

  Lemma preserving_preserves_0 : (∀ x, 0 ≤ x → 0 ≤ f x) → OrderPreserving f.
  Proof.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply srorder_plus in F. destruct F as [z [Ez1 Ez2]].
    apply srorder_plus. exists (f z). split.
     apply E. assumption.
    rewrite Ez2, preserves_plus. reflexivity.
  Qed.
End another_semiring.

End contents.
