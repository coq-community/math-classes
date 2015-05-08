Require Import
  Coq.setoid_ring.Ring
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.additional_operations
  MathClasses.interfaces.orders MathClasses.interfaces.integers
  MathClasses.orders.semirings MathClasses.theory.shiftl MathClasses.theory.int_pow.

Local Existing Instance pseudo_srorder_semiring.

Section positive_semiring_elements.
Context `{FullPseudoSemiRingOrder R} `{!PropHolds (1 ≶ 0)}.

Add Ring R : (rings.stdlib_semiring_theory R).

(* * Embedding of R₊ into R *)
Global Instance Pos_inject: Cast (R₊) R := @proj1_sig R _.

(* Operations *)
Global Program Instance Pos_plus: Plus (R₊) := λ x y, (`x + `y)↾_.
Next Obligation.
  destruct x as [x Hx], y as [y Hy].
  now apply pos_plus_compat.
Qed.

Global Program Instance Pos_mult: Mult (R₊) := λ x y, (`x * `y)↾_.
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  now apply pos_mult_compat.
Qed.

Global Program Instance Pos_1: One (R₊) := (1 : R).
Next Obligation. now apply lt_0_1. Qed.

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

Section shiftl.
  Context `{SemiRing B} `{!Biinduction B} `{!ShiftLSpec R B sl}.

  Global Program Instance Pos_shiftl: ShiftL (R₊) B | 5 := λ x n,
    (`x ≪ n)↾_.
  Next Obligation. destruct x. now apply shiftl_pos. Qed.
End shiftl.
End positive_semiring_elements.

Section int_pow.
  Context `{DecField R} `{Apart R} `{!FullPseudoSemiRingOrder Rle Rlt}
    `{!TrivialApart R} `{∀ x y : R, Decision (x = y)} `{Integers B} `{!IntPowSpec R B ipw}.

  Global Program Instance Pos_int_pow: Pow (R₊) B | 5 := λ x n,
    (`x ^ n)↾_.
  Next Obligation. destruct x. now apply int_pow_pos. Qed.
End int_pow.
