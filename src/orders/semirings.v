Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra theory.rings
  implementations.semiring_pairs.
Require Export
  orders.rings.

Section contents.
Context `{SemiRing R} `{!SemiRingOrder o}.
Add Ring R : (stdlib_semiring_theory R).

Global Instance: ∀ (z : R), OrderPreserving (z+).
Proof.
  intros z. repeat (split; try apply _). intros x y E.
  apply srorder_plus in E. destruct E as [a [Ea1 Ea2]].
  apply srorder_plus.
  exists a. split. easy.
  now rewrite <-associativity, <-Ea2.
Qed.

Global Instance: ∀ (z : R), OrderPreserving (+z).
Proof. intro. apply order_preserving_flip. Qed.

Lemma plus_compat x1 y1 x2 y2 : x1 ≤ y1 → x2 ≤ y2 → x1 + x2 ≤ y1 + y2.
Proof.
  intros E1 E2.
  apply transitivity with (y1 + x2).
   now apply (order_preserving (+ x2)).
  now apply (order_preserving (y1 +)).
Qed.

Lemma nonneg_plus_compat_r x y z : z ≤ x → 0 ≤ y → z ≤ x + y.
Proof. intros. rewrite <-(plus_0_r z). now apply plus_compat. Qed.

Lemma nonneg_plus_compat_l x y z : 0 ≤ x → z ≤ y → z ≤ x + y.
Proof. intros. rewrite <-(plus_0_l z). now apply plus_compat. Qed.

Lemma nonneg_plus_compat x y : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
Proof. apply nonneg_plus_compat_r. Qed.

Lemma nonpos_plus_compat x y : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof. intros. rewrite <-(plus_0_r 0). now apply plus_compat. Qed.

Lemma nonneg_mult_compat (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof. intros. now apply srorder_mult. Qed.

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

Global Instance mult_compat: ∀ (z : R), GeZero z → OrderPreserving (z*.).
Proof.
  intros z E. 
  repeat (split; try apply _).
  intros x y F.
  apply srorder_plus in F. destruct F as [a [Ea1 Ea2]]. 
  rewrite Ea2. 
  setoid_replace (z * (x + a)) with (z * x + z * a) by ring.
  apply nonneg_plus_compat_r.
   reflexivity.
  now apply srorder_mult.
Qed.

Global Instance: ∀ (z : R), GeZero z → OrderPreserving (.*z).
Proof. intros. apply order_preserving_flip. Qed.

Context `{∀ z, LeftCancellation (+) z}.

Global Instance: ∀ (z : R), StrictlyOrderPreserving (z+).
Proof.
  intros z.
  split; try apply _.
  intros x y [E1 E2]. split.
   now apply (order_preserving (z +)).
  intros F. apply E2.
  now apply (left_cancellation (+) z).
Qed.

Global Instance: ∀ (z : R), StrictlyOrderPreserving (+z).
Proof. 
  intros z.
  split; try apply _.
  intros x y E.
  unfold flip. do 2 rewrite (commutativity _ z).
  now apply (strictly_order_preserving (z +)).
Qed.

Lemma plus_scompat_l x1 y1 x2 y2 : x1 < y1 → x2 ≤ y2 → x1 + x2 < y1 + y2.
Proof.
  intros E1 E2.
  apply sprecedes_trans_l with (y1 + x2).
   now apply (strictly_order_preserving (+ x2)).
  now apply (order_preserving (y1 +)).
Qed.

Lemma plus_scompat_r x1 y1 x2 y2 : x1 ≤ y1 → x2 < y2 → x1 + x2 < y1 + y2.
Proof.
  intros E1 E2.
  apply sprecedes_trans_r with (y1 + x2).
   now apply (order_preserving (+ x2)).
  now apply (strictly_order_preserving (y1 +)).
Qed.

Lemma nonneg_plus_scompat_r x y z : z < x → 0 ≤ y → z < x + y.
Proof. intros. rewrite <-(plus_0_r z). now apply plus_scompat_l. Qed.

Lemma nonneg_plus_scompat_l x y z : 0 ≤ x → z < y → z < x + y.
Proof. intros. rewrite <-(plus_0_l z). now apply plus_scompat_r. Qed.

Lemma pos_plus_compat_r x y z : z ≤ x → 0 < y → z < x + y.
Proof. intros. rewrite <-(plus_0_r z). now apply plus_scompat_r. Qed.

Lemma pos_plus_compat_l x y z : 0 < x → z ≤ y → z < x + y.
Proof. intros. rewrite <-(plus_0_l z). now apply plus_scompat_l. Qed.

Lemma pos_plus_compat x y : 0 < x → 0 < y → 0 < x + y.
Proof. intros. apply pos_plus_compat_r. now apply sprecedes_weaken. easy. Qed.

Global Instance: ∀ (z : R), OrderPreservingBack (z +).
Proof. 
  intros z.
  split; try apply _. 
  intros x y E.
  apply srorder_plus in E. destruct E as [a [Ea1 Ea2]].
  apply srorder_plus. exists a. split. easy.
  apply (left_cancellation (+) z). 
  now rewrite associativity.
Qed.

Global Instance: ∀ (z : R), OrderPreservingBack (+ z).
Proof. intros. apply order_preserving_back_flip. Qed.

Context `{!TotalOrder (≤)} `{∀ z, NeZero z → LeftCancellation (.*.) z}.

Global Instance ring_mult_compat_back : ∀ (z : R), GtZero z → OrderPreservingBack (z *.).
Proof.
  intros z E.
  repeat (split; try apply _). 
  intros x y F.
  destruct (total_order x y) as [G|G]. easy.
  apply (order_preserving_ge_0 (.*.) z) in G.
   apply equiv_precedes.
   apply (left_cancellation_ne_0 (.*.) z).
   now apply not_symmetry, neq_precedes_sprecedes.
   now eapply (antisymmetry (≤)).
  now apply sprecedes_weaken.
Qed.

Global Instance: ∀ (z : R), GtZero z → OrderPreservingBack (.* z).
Proof. intros. apply order_preserving_back_flip. Qed.

Global Instance: ∀ (z : R), GtZero z → StrictlyOrderPreserving (z *.).
Proof.
  intros z Ez.
  split; try apply _.
  intros x y [E1 E2]. split.
   apply (order_preserving_ge_0 (.*.) z). now apply sprecedes_weaken. easy.
  intros F. apply E2.
  apply (left_cancellation_ne_0 (.*.) z). now apply not_symmetry, neq_precedes_sprecedes. easy.
Qed.

Global Instance: ∀ (z : R), GtZero z → StrictlyOrderPreserving (.* z).
Proof. 
  intros z.
  split; try apply _.
  intros x y E.
  unfold flip. rewrite 2!(commutativity _ z).
  now apply (strictly_order_preserving (z *.)).
Qed.

Lemma pos_mult_compat x y : 0 < x → 0 < y → 0 < x * y.
Proof. 
  intros E F.
  rewrite <-(mult_0_r x).
  assert (GtZero x) by assumption.
  now apply (strictly_order_preserving (x *.)).
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

Lemma sprecedes_0_2 `{!NeZero (1:R)} : 0 < 2.
Proof. apply pos_plus_compat; apply sprecedes_0_1. Qed.

Lemma precedes_1_2 : 1 ≤ 2.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. easy. Qed.

Lemma sprecedes_1_2 `{!NeZero (1:R)} : 1 < 2.
Proof. apply pos_plus_compat_l. now apply sprecedes_0_1. easy. Qed.

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

Section another_semiring.
  Context `{SemiRing R2} `{o2 : Order R2}.

  (* If a morphism agrees on the positive cone then it is order preserving *)    
  Lemma preserving_preserves_0 {f : R → R2} `{!SemiRing_Morphism f} `{!SemiRingOrder o2} : 
    (∀ x, 0 ≤ x → 0 ≤ f x) → OrderPreserving f.
  Proof.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply srorder_plus in F. destruct F as [z [Ez1 Ez2]].
    apply srorder_plus. exists (f z). split.
     now apply E.
    now rewrite Ez2, preserves_plus.
  Qed.
End another_semiring.

End contents.
