Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.orders
  MathClasses.theory.naturals MathClasses.theory.rings MathClasses.implementations.peano_naturals.
Require Export
  MathClasses.orders.semirings.

(*
We axiomatize the order on the naturals and the integers as a non trivial
pseudo semiring order that satisfies the biinduction principle. We prove
some results that hold for the order on the naturals and the integers.
In particular, we show that given another non trivial pseudo semiring order
(that not necessarily has to satisfy the biinduction principle, for example
the rationals or the reals), any morphism to it is an order embedding.
*)
Lemma to_semiring_nonneg `{FullPseudoSemiRingOrder N}
  `{!NaturalsToSemiRing N} `{!Naturals N} `{FullPseudoSemiRingOrder R}
  `{!SemiRing_Morphism (f : N → R)} n : 0 ≤ f n.
Proof.
  pose proof (pseudo_srorder_semiring (A:=R)).
  revert n. apply naturals.induction.
    solve_proper.
   intros. now rewrite preserves_0.
  intros n E. rewrite preserves_plus, preserves_1.
  apply nonneg_plus_compat. solve_propholds. easy.
Qed.

Section nat_int_order.
Context `{FullPseudoSemiRingOrder R} `{!Biinduction R} `{PropHolds (1 ≶ 0)}.

Local Existing Instance pseudo_srorder_semiring.
Add Ring R : (stdlib_semiring_theory R).

(* Hmm, can we avoid using nat here? *)
Lemma nat_int_to_semiring x : ∃ z, x = naturals_to_semiring nat R z ∨ x + naturals_to_semiring nat R z = 0.
Proof.
  revert x. apply biinduction.
    solve_proper.
   exists (0 : nat). left. now rewrite preserves_0.
  intros n; split.
   intros [z [Ez | Ez]].
    exists (1 + z). left. now rewrite preserves_plus, preserves_1, Ez.
   destruct z as [|z].
    exists (1 : nat). left. rewrite O_nat_0, preserves_0, plus_0_r in Ez.
    rewrite Ez, preserves_1. ring.
   exists z. right. rewrite S_nat_1_plus, preserves_plus, preserves_1 in Ez.
   rewrite <-Ez. ring.
  intros [z [Ez | Ez]].
   destruct z as [|z].
    exists (1 : nat). right. rewrite O_nat_0, preserves_0 in Ez.
    rewrite preserves_1, <-Ez. ring.
   exists z. left. rewrite S_nat_1_plus, preserves_plus, preserves_1 in Ez.
   now apply (left_cancellation (+) 1).
  exists (1 + z). right. rewrite preserves_plus, preserves_1, <-Ez. ring.
Qed.

Lemma nat_int_nonneg_decompose x : 0 ≤ x → ∃ z, x = naturals_to_semiring nat R z.
Proof.
  destruct (nat_int_to_semiring x) as [z [Ez1 | Ez2]].
   now exists z.
  intros E. exists (0 : nat). rewrite preserves_0.
  apply (antisymmetry (≤)); auto.
  rewrite <-Ez2. now apply nonneg_plus_le_compat_r, to_semiring_nonneg.
Qed.

Lemma nat_int_le_plus x y : x ≤ y ↔ ∃ z, y = x + naturals_to_semiring nat R z.
Proof.
  split.
   intros E. destruct (decompose_le E) as [z [Ez1 Ez2]].
   destruct (nat_int_nonneg_decompose _ Ez1) as [u Eu].
   exists u. now rewrite <-Eu.
  intros [z Ez]. rewrite Ez.
  now apply nonneg_plus_le_compat_r, to_semiring_nonneg.
Qed.

Lemma nat_int_lt_plus x y : x < y ↔ ∃ z, y = x + 1 + naturals_to_semiring nat R z.
Proof.
  split.
   intros E. destruct (proj1 (nat_int_le_plus x y)) as [[|z] Ez].
     now apply lt_le.
    rewrite O_nat_0, preserves_0, plus_0_r in Ez.
    now destruct (lt_ne_flip x y).
   exists z. now rewrite S_nat_1_plus, preserves_plus, preserves_1, associativity in Ez.
  intros [z Ez]. rewrite Ez.
  apply nonneg_plus_lt_compat_r.
   now apply to_semiring_nonneg.
  apply pos_plus_lt_compat_r; solve_propholds.
Qed.

Lemma lt_iff_plus_1_le x y : x < y ↔ x + 1 ≤ y.
Proof. now rewrite nat_int_lt_plus, nat_int_le_plus. Qed.

Lemma lt_iff_S_le x y : x < y ↔ 1 + x ≤ y.
Proof. rewrite commutativity. now apply lt_iff_plus_1_le. Qed.

Lemma pos_ge_1 x : 0 < x ↔ 1 ≤ x.
Proof.
  split; intros E.
   rewrite <-(plus_0_l 1). now apply lt_iff_plus_1_le.
  apply lt_le_trans with 1; [solve_propholds | easy].
Qed.

Lemma le_iff_lt_plus_1 x y : x ≤ y ↔ x < y + 1.
Proof.
  split; intros E.
   apply lt_iff_plus_1_le. now apply (order_preserving (+1)).
  now apply (order_reflecting (+1)), lt_iff_plus_1_le.
Qed.

Lemma le_iff_lt_S x y : x ≤ y ↔ x < 1 + y.
Proof. rewrite commutativity. now apply le_iff_lt_plus_1. Qed.

Section another_semiring.
  Context `{FullPseudoSemiRingOrder R2} `{PropHolds ((1 : R2) ≶ 0)} `{!SemiRing_Morphism (f : R → R2)}.

  Instance: OrderPreserving f.
  Proof.
    repeat (split; try apply _).
    intros x y E. apply nat_int_le_plus in E. destruct E as [z E].
    rewrite E, preserves_plus, (naturals.to_semiring_twice _ _ _).
    apply nonneg_plus_le_compat_r. now apply to_semiring_nonneg.
  Qed.

  Global Instance: StrictlyOrderPreserving f | 50.
  Proof.
    repeat (split; try apply _).
    intros x y E. apply nat_int_lt_plus in E. destruct E as [z E].
    rewrite E, !preserves_plus, preserves_1, (naturals.to_semiring_twice _ _ _).
    apply nonneg_plus_lt_compat_r.
     now apply to_semiring_nonneg.
    apply pos_plus_lt_compat_r; solve_propholds.
  Qed.

  Global Instance: OrderEmbedding f | 50.
  Proof. split; try apply _. apply full_pseudo_order_reflecting. Qed.
End another_semiring.
End nat_int_order.
