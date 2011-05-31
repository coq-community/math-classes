Require
  theory.naturals. 
Require Import
  Morphisms Ring Program
  abstract_algebra interfaces.naturals interfaces.orders
  orders.rings theory.rings.

Section naturals_order.
Context `{Naturals N} `{Apart N} `{!TrivialApart N} `{!FullPseudoSemiRingOrder Nle Nlt}.

Lemma to_semiring_nonneg `{SemiRing R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}
  `{!SemiRing_Morphism (f : N → R)} n : 0 ≤ f n.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   intros. rewrite preserves_0. reflexivity.
  intros n E.
  rewrite preserves_plus, preserves_1.
  apply nonneg_plus_compat; try assumption.
  apply le_0_1.
Qed.

Lemma naturals_nonneg x : 0 ≤ x.
Proof. now apply (to_semiring_nonneg (f:=id)). Qed.

Lemma natural_le_plus {x y: N}: x ≤ y ↔ ∃ z: N, y = x + z.
Proof with auto.
  split; intros E.
   destruct (decompose_le E) as [z [Ez1 Ez2]].
   exists z...
  destruct E as [z Ez].
  apply compose_le with z.
   apply naturals_nonneg.
  easy.
Qed.

Section another_semiring.
  Context `{SemiRing R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}
    {f : N → R} `{!SemiRing_Morphism f}.

  Global Instance morphism_order_preserving: OrderPreserving f.
  Proof.
    apply preserving_preserves_nonneg.
    intros x E.
    apply to_semiring_nonneg.
  Qed.
End another_semiring.

Section another_ring.
  Context `{Ring R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt}.

  Lemma opp_to_semiring_nonpos n : - naturals_to_semiring N R n ≤ 0.
  Proof. apply flip_nonneg_opp. apply to_semiring_nonneg. Qed.

  Lemma opp_to_sr_le_to_sr n : - naturals_to_semiring N R n ≤ naturals_to_semiring N R n.
  Proof. transitivity (0:R). apply opp_to_semiring_nonpos. apply to_semiring_nonneg. Qed.

  Lemma opp_to_semiring x y : - naturals_to_semiring N R x = naturals_to_semiring N R y
    → naturals_to_semiring N R x = naturals_to_semiring N R y.
  Proof.
    intros E. apply (antisymmetry (≤)).
     apply flip_le_opp. rewrite E. apply opp_to_sr_le_to_sr.
    rewrite <-E. apply opp_to_sr_le_to_sr.
  Qed.
End another_ring. 
End naturals_order.

(* A PseudoSemiRingOrder uniquely specifies the orders on the naturals *)
Section order_unique.
Context `{Naturals N} `{Naturals N2} {f : N → N2} `{!SemiRing_Morphism f}
  `{Apart N} `{!TrivialApart N} `{!FullPseudoSemiRingOrder (A:=N) Nle Nlt} 
  `{Apart N2} `{!TrivialApart N2} `{!FullPseudoSemiRingOrder (A:=N2) N2le N2lt}.

Global Instance: OrderEmbedding f.
Proof.
  repeat (split; try apply _).
  intros x y E.
  rewrite <-(naturals.morphisms_involutive (naturals_to_semiring N2 N) f x).
  rewrite <-(naturals.morphisms_involutive (naturals_to_semiring N2 N) f y).
  now apply (order_preserving _).
Qed.
End order_unique.

Section other_results.
Context `{Naturals N} `{Apart N} `{!TrivialApart N} `{!FullPseudoSemiRingOrder Nle Nlt}.
Add Ring N : (stdlib_semiring_theory N).

Global Program Instance slow_nat_le_dec: ∀ x y: N, Decision (x ≤ y) | 10 := λ x y,
  match decide (naturals_to_semiring _ nat x ≤ naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. 
  now apply (order_reflecting (naturals_to_semiring N nat)). 
Qed.
Next Obligation.
  intros F. apply E.
  now apply (order_preserving _).
Qed.

Lemma ne_0_ge_1 x : x ≠ 0 → 1 ≤ x.
Proof with intuition.
  intros E.
  destruct (total (≤) 1 x) as [| F]...
  apply natural_le_plus in F. destruct F as [z Fz]. symmetry in Fz.
  destruct (naturals.one_sum _ _ Fz)...
  apply orders.eq_le. symmetry...
Qed.

Lemma le_iff_lt_plus_1 x y : x ≤ y ↔ x < y + 1.
Proof.
  split; intros E.
   apply pos_plus_le_lt_compat_r. now apply lt_0_1. easy.
  apply lt_iff_le_ne in E. destruct E as [E1 E2].
  apply natural_le_plus in E1. destruct E1 as [z E1].
  destruct (decide (z = 0)) as [E3 | E3].
   destruct E2. rewrite E1, E3. ring.
  apply ne_0_ge_1 in E3. apply natural_le_plus in E3. destruct E3 as [k E3].
  apply natural_le_plus. exists k. 
  apply (right_cancellation (+) 1). rewrite E1, E3. ring.
Qed.

Lemma lt_iff_plus_1_le x y : x < y ↔ x + 1 ≤ y.
Proof.
  split; intros E.
   apply le_iff_lt_plus_1. now apply (strictly_order_preserving (+ 1)).
  apply (strictly_order_reflecting (+ 1)). now apply le_iff_lt_plus_1.
Qed.

Global Instance: ∀ (z : N), PropHolds (z ≠ 0) → OrderReflecting (z *.).
Proof.
   intros z ?. 
   apply (order_reflecting_pos (.*.) z).
   apply lt_iff_le_ne. split.
    apply naturals_nonneg. 
   now apply not_symmetry.
Qed.
End other_results.

Instance nat_le `{Naturals N} : Le N | 10 :=  λ x y, ∃ z, x + z = y.
Instance nat_lt  `{Naturals N} : Lt N | 10 := dec_lt.

Section default_order.
Context `{Naturals N} `{Apart N} `{!TrivialApart N}.
Add Ring N2 : (rings.stdlib_semiring_theory N).

Instance: Proper ((=) ==> (=) ==> iff) nat_le.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   now rewrite <-E1, <-E2.
  now rewrite E1, E2.
Qed.

Instance: SemiRingOrder nat_le.
Proof.
  repeat (split; try apply _).
        intros x. exists 0. ring.
       intros x y z [a A] [b B]. exists (a + b). now rewrite associativity, A, B.
      intros x y [a A] [b B].
      destruct (naturals.zero_sum a b) as [E1 E2].
       apply (left_cancellation (+) x). 
       rewrite associativity, A, B. ring.
      rewrite <-A, <-B, E1, E2. ring.
     intros x y [a A]. now exists a.
    intros x y [a A]. exists a. rewrite <-A. ring.
   intros x y [a A]. exists a.
   apply (left_cancellation (+) z). rewrite <-A. ring.
  intros x y _ _. exists (x * y). ring.
Qed.

Notation n_to_sr := (naturals_to_semiring N nat).

Instance: TotalRelation nat_le.
Proof.
  assert (∀ x y, n_to_sr x ≤ n_to_sr y → x ≤ y) as P.
   intros x y E. 
   destruct (decompose_le E) as [a [_ A]].
   exists (naturals_to_semiring nat N a). 
   apply (injective n_to_sr).
   rewrite preserves_plus. now rewrite (naturals.to_semiring_involutive _ _).
  intros x y.
  destruct (total (≤) (n_to_sr x) (n_to_sr y)); [left | right]; now apply P.
Qed.

Global Instance: FullPseudoSemiRingOrder nat_le nat_lt.
Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
