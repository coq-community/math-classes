Require Import
  Morphisms Ring Program Setoid
  abstract_algebra orders.semirings.

Section positive_semiring_elements.
Context `{SemiRing R} `{!SemiRingOrder o} `{!TotalOrder o} `{!PropHolds (1 ≠ 0)}
  `{∀ z : R, LeftCancellation (+) z} `{∀ z : R, PropHolds (z ≠ 0) → LeftCancellation ring_mult z}.

Add Ring R : (rings.stdlib_semiring_theory R).

(* * Embedding of R₊ into R *)
Global Instance Pos_inject: Coerce (R₊) R := @proj1_sig R _.

(* Operations *)
Global Program Instance Pos_plus: RingPlus (R₊) := λ x y, (x + y : R). 
Next Obligation.
  destruct x as [x Hx], y as [y Hy].
  now apply pos_plus_scompat.
Qed.

Global Program Instance Pos_mult: RingMult (R₊) := λ x y, (x * y : R). 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  now apply pos_mult_scompat.
Qed.

Global Program Instance Pos_1: RingOne (R₊) := (1 : R).
Next Obligation. apply sprecedes_0_1. Qed.

(* * Equalitity *)
Local Ltac unfold_equivs := unfold equiv, sig_equiv in *; simpl in *.

Global Instance: Proper ((=) ==> (=) ==> (=)) Pos_plus.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs.
  now rewrite E1, E2.
Qed.

Global Instance: Proper ((=) ==> (=) ==> (=)) Pos_mult.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs. 
  now rewrite E1, E2.
Qed.

Instance: Proper ((=) ==> (=)) Pos_inject.
Proof. now repeat intro. Qed.

Global Instance: Injective Pos_inject.
Proof. now repeat (split; try apply _). Qed.
End positive_semiring_elements.
