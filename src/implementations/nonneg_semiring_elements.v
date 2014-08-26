Require
  theory.rings.
Require Import
  Ring
  abstract_algebra interfaces.orders orders.semirings.

Local Existing Instance pseudo_srorder_semiring.

Section nonneg_semiring_elements.
Context `{FullPseudoSemiRingOrder R} `{Apart R}.

Add Ring R : (rings.stdlib_semiring_theory R).

(* * Embedding of R⁺ into R *)
Global Instance NonNeg_inject: Cast (R⁺) R := @proj1_sig R _.

(* Operations *)
Global Program Instance NonNeg_plus: Plus (R⁺) := λ x y, (`x + `y)↾_.
Next Obligation.
  destruct x as [x Hx], y as [y Hy].
  now apply nonneg_plus_compat.
Qed.

Global Program Instance NonNeg_mult: Mult (R⁺) := λ x y, (`x * `y)↾_.
Next Obligation.
  destruct x as [x Hx], y as [y Hy].
  now apply nonneg_mult_compat.
Qed.

Global Program Instance NonNeg_0: Zero (R⁺) := 0↾_.

Global Program Instance NonNeg_1: One (R⁺) := 1↾_.
Next Obligation. apply le_0_1. Qed.

(* * Equalitity *)
Local Ltac unfold_equivs := unfold equiv, sig_equiv in *; simpl in *.

Instance: Proper ((=) ==> (=) ==> (=)) NonNeg_plus.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs.
  now rewrite E1, E2.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) NonNeg_mult.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs.
  now rewrite E1, E2.
Qed.

(* It is indeed a semiring *)
Global Instance: SemiRing (R⁺).
Proof. repeat (split; try apply _); repeat intro; unfold_equivs; ring. Qed.

Instance: Proper ((=) ==> (=)) NonNeg_inject.
Proof. now repeat intro. Qed.

Global Instance: SemiRing_Morphism NonNeg_inject.
Proof. repeat (split; try apply _); now repeat intro. Qed.

Global Instance: Injective NonNeg_inject.
Proof. split. trivial. apply _. Qed.

(* Misc *)
Global Instance NonNeg_trivial_apart `{!TrivialApart R} :  TrivialApart (R⁺).
Proof. intros x y. now rapply trivial_apart. Qed.

Global Instance NonNeg_equiv_dec `{∀ x y : R, Decision (x = y)} : ∀ x y: R⁺, Decision (x = y)
  := λ x y, decide_rel (=) ('x : R) ('y : R).

Global Instance NonNeg_apart_dec `{∀ x y : R, Decision (x ≶ y)} : ∀ x y: R⁺, Decision (x ≶ y)
  := λ x y, decide_rel (≶) ('x : R) ('y : R).

(* Order *)
Global Instance NonNeg_le: Le (R⁺) := λ x y, 'x ≤ 'y.
Global Instance NonNeg_lt: Lt (R⁺) := λ x y, 'x < 'y.

Global Instance: Proper ((=) ==> (=) ==> iff) NonNeg_le.
Proof. intros x1 y1 E1 x2 y2 E2. unfold NonNeg_le. now rewrite E1, E2. Qed.

Instance: PartialOrder NonNeg_le.
Proof. now apply (maps.projected_partial_order NonNeg_inject). Qed.

Global Instance: OrderEmbedding NonNeg_inject.
Proof. repeat (split; try apply _); intuition. Qed.

(*
Global Instance: TotalOrder NonNeg_le.
Proof maps.embed_totalorder NonNeg_le.

Global Instance: SemiRingOrder NonNeg_order.
Proof.
  split; try apply _.
   intros x y. split; intros E.
    apply (order_preserving NonNeg_inject) in E.
    apply srorder_plus in E. destruct E as [z [Ez1 Ez2]].
    exists (z↾Ez1); intuition.
   destruct E as [z [Ez1 Ez2]].
   rewrite Ez2.
   apply (order_reflecting NonNeg_inject).
   rewrite rings.preserves_plus.
   now apply nonneg_plus_compat_r.
  intros x E1 y E2.
  apply (order_reflecting NonNeg_inject).
  rewrite rings.preserves_0, rings.preserves_mult.
  now apply srorder_mult.
Qed.
*)
Global Program Instance NonNeg_le_dec `{∀ x y : R, Decision (x ≤ y)} : ∀ x y: R⁺, Decision (x ≤ y) := λ x y,
  match decide_rel (≤) ('x) ('y) with
  | left E => left _
  | right E => right _
  end.
End nonneg_semiring_elements.

Typeclasses Opaque NonNeg_le.
Typeclasses Opaque NonNeg_lt.
