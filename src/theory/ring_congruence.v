Require Import
  Ring abstract_algebra theory.rings.

Class RingCongruence A (R : relation A) `{Ring A} :=
  { ring_congr_equivalence : Equivalence R
  ; ring_congr_subrelation : subrelation (=) R
  ; ring_congr_plus : Proper (R ==> R ==> R) (+)
  ; ring_congr_mult : Proper (R ==> R ==> R) (.*.)
  ; ring_congr_negate : Proper (R ==> R) (-)}.

(*
As far as I see, there are three ways to represent the quotient ring:
- Define the congruence as a new Equiv instance. This leads to ambiguity.
- Wrap it into a definition and define a ring structure on top of it.
     Definition Quotient A (R : relation A) := A.
   However, in order to avoid ambiguity we have to make it Opaque for
   type class resolution.
- Wrap it into an inductive and define a ring structure on top of it.
The latter makes the clearest distinction between the original structure
and the quotient. Unfortunately, it is sometimes a bit verbose.
*)
Inductive Quotient A (R : relation A) := quotient_inject : Cast A (Quotient A R).
Existing Instance quotient_inject.
Implicit Arguments quotient_inject [[A] [R]].

Instance quotient_rep {A R} : Cast (Quotient A R) A := λ x,
  match x with quotient_inject r => r end.

Section quotient_ring.
  Context `{cong : RingCongruence A R}.
  Add Ring A : (rings.stdlib_ring_theory A).

  Existing Instance ring_congr_equivalence.

  Global Instance quotient_equiv: Equiv (Quotient A R) := λ x y, R ('x) ('y).
  Global Instance quotient_0: Zero (Quotient A R) := cast A (Quotient A R) 0.
  Global Instance quotient_1: One (Quotient A R) := cast A (Quotient A R) 1.
  Global Instance quotient_plus: Plus (Quotient A R) := λ x y, cast A (Quotient A R) ('x + 'y).
  Global Instance quotient_mult: Mult (Quotient A R) := λ x y, cast A (Quotient A R) ('x * 'y).
  Global Instance quotient_negate: Negate (Quotient A R) := λ x, cast A (Quotient A R) (-'x).

  Instance: Setoid (Quotient A R).
  Proof.
    constructor; unfold equiv, quotient_equiv.
      intros [x]. reflexivity.
     intros [x] [y] E. now symmetry.
    intros [x] [y] [z] E1 E2. now transitivity y.
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) quotient_plus.
  Proof. intros [?] [?] E1 [?] [?] E2. now rapply ring_congr_plus. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) quotient_mult.
  Proof. intros [?] [?] E1 [?] [?] E2. now rapply ring_congr_mult. Qed.

  Instance: Proper ((=) ==> (=)) quotient_negate.
  Proof. intros [?] [?] E. now rapply ring_congr_negate. Qed.

  Global Instance: Setoid_Morphism quotient_inject.
  Proof. split; try apply _. intros ?? E. now rapply ring_congr_subrelation. Qed.

  Global Instance: Ring (Quotient A R).
  Proof.
    repeat (constructor; try apply _); repeat intros [?];
      unfold mult, plus, sg_op, mon_unit, one_is_mon_unit, zero_is_mon_unit, plus_is_sg_op, mult_is_sg_op,
      quotient_0, negate, quotient_negate, quotient_1, quotient_plus, quotient_mult, cast in *; simpl; apply sm_proper; ring.
  Qed.
End quotient_ring.
