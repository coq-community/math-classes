Require Import
  Morphisms Ring Program Setoid
  abstract_algebra orders.semirings.

Section positive_semiring_elements.
Context `{SemiRing R} `{!SemiRingOrder o} `{!TotalOrder o} `{!NeZero (1:R)}
  `{∀ z : R, LeftCancellation (+) z} `{∀ z : R, NeZero z → LeftCancellation ring_mult z}.

Add Ring R : (rings.stdlib_semiring_theory R).

(* * Embedding of R₊ into R *)
Global Instance Pos_inject: Inject (R₊) R := @proj1_sig R _.

(* Operations *)
Global Program Instance Pos_plus: RingPlus (R₊) := λ x y, exist _ (x + y) _. 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  apply pos_plus_compat...
Qed.

Global Program Instance Pos_mult: RingMult (R₊) := λ x y, exist _ (x * y) _. 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  apply pos_mult_compat...
Qed.

Global Program Instance Pos_1: RingOne (R₊) := exist _ 1 _.
Next Obligation. apply sprecedes_0_1. Qed.

(* * Equalitity *)
Global Instance Pos_equiv: Equiv (R₊) := λ x y, 'x = 'y.

Local Ltac unfold_equivs := unfold equiv, Pos_equiv, inject, Pos_inject in *; simpl in *.

Instance: Proper ((=) ==> (=) ==> (=)) Pos_plus.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs.
  rewrite E1, E2. reflexivity.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) Pos_mult.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs. 
  rewrite E1, E2. reflexivity.
Qed.

Instance: Proper ((=) ==> (=)) Pos_inject.
Proof. repeat intro. assumption. Qed.

Global Instance: Injective Pos_inject.
Proof. repeat (split; try apply _). easy. Qed.
End positive_semiring_elements.