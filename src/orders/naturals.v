Require
  theory.naturals. 
Require Import
  Morphisms Ring Program
  abstract_algebra interfaces.naturals
  orders.semirings theory.rings.

Section naturals_order.
Context `{Naturals N} `{!SemiRingOrder o} `{!TotalOrder o}.

Lemma to_semiring_nonneg `{SemiRing R} {oR : Order R} `{!SemiRingOrder oR} `{!TotalOrder oR} 
     `{∀ z : R, LeftCancellation (+) z} {f : N → R} `{!SemiRing_Morphism f} n : 
  0 ≤ f n.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   intros. rewrite preserves_0. reflexivity.
  intros n E.
  rewrite preserves_plus, preserves_1.
  apply nonneg_plus_compat; try assumption.
  apply precedes_0_1.
Qed.

Lemma naturals_nonneg x : 0 ≤ x.
Proof.
  rewrite (naturals.to_semiring_self x).
  apply to_semiring_nonneg.
Qed.

Lemma natural_precedes_plus {x y: N}: x ≤ y ↔ ∃ z: N, y = x + z.
Proof with auto.
  split; intros E.
   apply srorder_plus in E. destruct E as [z [Ez1 Ez2]].
   exists z...
  destruct E as [z Ez].
  apply srorder_plus. exists z.
  split... apply naturals_nonneg.
Qed.

Section another_semiring.
  Context `{SemiRing R} {oR : Order R} `{!SemiRingOrder oR} `{!TotalOrder oR} `{∀ z : R, LeftCancellation (+) z}
    {f : N → R} `{!SemiRing_Morphism f}.

  Global Instance morphism_order_preserving: OrderPreserving f.
  Proof.
    apply preserving_preserves_nonneg.
    intros x E.
    apply to_semiring_nonneg.
  Qed.
End another_semiring.

Section another_ring.
  Context `{Ring R} {oR : Order R} `{!RingOrder oR} `{!TotalOrder oR}.

  Lemma opp_to_semiring_nonpos n : - naturals_to_semiring N R n ≤ 0.
  Proof. apply flip_nonneg_opp. apply to_semiring_nonneg. Qed.

  Lemma opp_to_sr_precedes_to_sr n : - naturals_to_semiring N R n ≤ naturals_to_semiring N R n.
  Proof. transitivity (0:R). apply opp_to_semiring_nonpos. apply to_semiring_nonneg. Qed.

  Lemma opp_to_semiring x y : - naturals_to_semiring N R x = naturals_to_semiring N R y
    → naturals_to_semiring N R x = naturals_to_semiring N R y.
  Proof.
    intros E. apply (antisymmetry (≤)).
     apply flip_opp. rewrite E. apply opp_to_sr_precedes_to_sr.
    rewrite <-E. apply opp_to_sr_precedes_to_sr.
  Qed.
End another_ring. 
End naturals_order.

Section order_unique.
Context `{Naturals N} `{Naturals N2} {f : N → N2} `{!SemiRing_Morphism f}
  {o1 : Order N} `{!SemiRingOrder o1} `{!TotalOrder o1}
  {o2 : Order N2} `{!SemiRingOrder o2} `{!TotalOrder o2}.

Global Instance: OrderEmbedding f.
Proof.
  repeat (split; try apply _).
  intros x y E.
  eapply poset_proper.
    symmetry. now apply (naturals.morphisms_involutive (naturals_to_semiring N2 N) f).
   symmetry. now apply (naturals.morphisms_involutive (naturals_to_semiring N2 N) f).
  now apply (order_preserving _).
Qed.
End order_unique.

Section other_results.
Context `{Naturals N} `{!SemiRingOrder o} `{!TotalOrder o}.
Add Ring N : (stdlib_semiring_theory N).

Global Program Instance slow_nat_le_dec: ∀ x y: N, Decision (x ≤ y) | 10 := λ x y,
  match decide (naturals_to_semiring _ nat x ≤ naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. 
  now apply (order_preserving_back (naturals_to_semiring N nat)). 
Qed.
Next Obligation.
  intros F. apply E.
  now apply (order_preserving _).
Qed.

Lemma ne0_ge1 x : x ≠ 0 → 1 ≤ x.
Proof with intuition.
  intros E.
  destruct (total_order 1 x) as [| F]...
  apply natural_precedes_plus in F. destruct F as [z Fz]. symmetry in Fz.
  destruct (naturals.one_sum _ _ Fz)...
  apply orders.equiv_precedes. symmetry...
Qed.

Lemma precedes_sprecedes x y : x ≤ y ↔ x < y + 1.
Proof with trivial.
  split; intros E.
   apply pos_plus_scompat_r... apply sprecedes_0_1.
  destruct E as [E1 E2].
  apply natural_precedes_plus in E1. destruct E1 as [z E1].
  destruct (decide (z = 0)) as [E3 | E3].
   destruct E2. rewrite E1, E3. ring.
  apply ne0_ge1 in E3. apply natural_precedes_plus in E3. destruct E3 as [k E3].
  apply natural_precedes_plus. exists k. 
  apply (right_cancellation (+) 1). rewrite E1, E3. ring.
Qed.

Lemma precedes_sprecedes_alt x y : x < y ↔ x + 1 ≤ y.
Proof.
  split; intros E.
   apply precedes_sprecedes. now apply (strictly_order_preserving (+ 1)).
  apply (strictly_order_preserving_back (+ 1)). now apply precedes_sprecedes.
Qed.

Global Instance: ∀ (z : N), PropHolds (z ≠ 0) → OrderPreservingBack (z *.).
Proof.
   intros z ?. 
   apply (order_preserving_back_gt_0 (.*.) z).
   split.
    apply naturals_nonneg. 
   now apply not_symmetry.
Qed.
End other_results.

Instance nat_precedes `{Naturals N} : Order N | 10 :=  λ x y, ∃ z, y = x + z.

Section default_order.
Context `{Naturals N}.
Add Ring N2 : (rings.stdlib_semiring_theory N).

Global Instance: Proper ((=) ==> (=) ==> iff) nat_precedes.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   now rewrite <-E1, <-E2.
  now rewrite E1, E2.
Qed.

Global Instance: SemiRingOrder nat_precedes.
Proof with trivial; try ring.
  repeat (split; try apply _).
       intros x. exists 0...
      intros x y z [a A] [b B]. exists (a + b). rewrite associativity, <-A, B...
     intros x y [a A] [b B].
     destruct (naturals.zero_sum a b) as [E1 E2].
      apply (left_cancellation (+) x). rewrite B at 2. rewrite A...
     rewrite A, B, E1, E2...
    intros [a A]. exists a. split... exists a...
   intros [a [_ A]]. rewrite A. exists a...
  intros x _ y _. exists (x * y)...
Qed.

Notation n_to_sr := (naturals_to_semiring N nat).

Global Instance: TotalOrder nat_precedes.
Proof.
  assert (∀ x y, n_to_sr x ≤ n_to_sr y → x ≤ y) as P.
   intros x y E. apply srorder_plus in E. 
   destruct E as [a [_ A]].
   exists (naturals_to_semiring nat N a). 
   apply (injective n_to_sr).
   rewrite preserves_plus. now rewrite (naturals.to_semiring_involutive _ _).
  intros x y.
  destruct (total_order (n_to_sr x) (n_to_sr y)); intuition.
Qed.
End default_order.
