Require
  orders.integers theory.fields.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers 
  interfaces.additional_operations.

Section shiftl.
Context `{SemiRing A} `{!LeftCancellation (.*.) (2:A)} `{SemiRing B} `{!Biinduction B} `{!ShiftLSpec A B sl}.

Add Ring A: (rings.stdlib_semiring_theory A).
Add Ring B: (rings.stdlib_semiring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) (≪) | 1.
Proof shiftl_proper.

Lemma shiftl_nat_pow_alt `{Naturals B2} `{!NatPowSpec A B2 pw} `{!SemiRing_Morphism (f : B2 → B)} x n : 
  x ≪ f n = x * 2 ^ n.
Proof.
  pose proof nat_pow_proper.
  revert n. apply naturals.induction.
    solve_proper.
   rewrite rings.preserves_0, ?shiftl_0, nat_pow_0. ring.
  intros n E.
  rewrite rings.preserves_plus, rings.preserves_1, shiftl_S.
  rewrite E, nat_pow_S. ring.
Qed.

Lemma shiftl_nat_pow `{!NaturalsToSemiRing B} `{!Naturals B} `{!NatPowSpec A B np} x n : x ≪ n = x * 2 ^ n.
Proof. change (x ≪ id  n = x * 2 ^ n). apply shiftl_nat_pow_alt. Qed.

Lemma shiftl_1 x : x ≪ (1:B) = 2 * x.
Proof. now rewrite <-(rings.plus_0_r 1), shiftl_S, shiftl_0. Qed.

Lemma shiftl_2 x : x ≪ (2:B) = 4 * x.
Proof. rewrite shiftl_S, shiftl_1. ring. Qed.

Global Instance shiftl_base_0: LeftAbsorb (≪) 0.
Proof. 
  intros n. pattern n. apply biinduction; clear n.
    solve_proper.
   now apply shiftl_0.
  intros n; split; intros E.
   rewrite shiftl_S, E. ring.
  apply (left_cancellation (.*.) 2).
  rewrite <-shiftl_S, E. ring.
Qed.

Lemma shiftl_exp_plus x n m : x ≪ (n + m) = x ≪ n ≪ m.
Proof.
  pattern m. apply biinduction; clear m.
    solve_proper.
   now rewrite shiftl_0, rings.plus_0_r.
  intros m.
  setoid_replace (n + (1 + m)) with (1 + (n + m)) by ring.
  rewrite ?shiftl_S.
  split; intros E.
   now rewrite E.
  now apply (left_cancellation (.*.) 2).
Qed.

Lemma shiftl_order x n m: x ≪ n ≪ m  = x ≪ m ≪ n.
Proof. rewrite <-?shiftl_exp_plus. now rewrite commutativity. Qed.

Lemma shiftl_reverse (x : A) (n m : B) : n + m = 0 → x ≪ n ≪ m = x.
Proof. intros E. now rewrite <-shiftl_exp_plus, E, shiftl_0. Qed.

Lemma shiftl_mult x y n : x * (y ≪ n) = (x * y) ≪ n.
Proof. 
  pattern n. apply biinduction; clear n.
    solve_proper.
   now rewrite ?shiftl_0.
  intros m.
  rewrite ?shiftl_S.
  split; intros E.
   rewrite <-E. ring.
  apply (left_cancellation (.*.) 2). rewrite <-E. ring.
Qed.

Lemma shiftl_base_plus x y n : (x + y) ≪ n  = x ≪ n + y ≪ n.
Proof.
  pattern n. apply biinduction; clear n.
    solve_proper.
   now rewrite ?shiftl_0.
  intros m. rewrite ?shiftl_S.
  split; intros E.
   rewrite E. ring.
  apply (left_cancellation (.*.) 2). rewrite E. ring.
Qed.

Lemma shiftl_opp `{GroupInv A} `{!Ring A} x n : (-x) ≪ n = -(x ≪ n).
Proof.
  rewrite (rings.opp_mult x), (rings.opp_mult (x ≪ n)).
  symmetry. now apply shiftl_mult.
Qed.

Context `{!NoZeroDivisors A} `{!PropHolds ((2:A) ≠ 0)}.

Global Instance shiftl_inj: ∀ n, Injective (≪ n).
Proof.
  repeat (split; try apply _). 
   2: solve_proper.
  pattern n. apply biinduction; clear n.
    solve_proper.
   intros x y E. now rewrite ?shiftl_0 in E.
  intros n; split; intros E1 x y E2.
   apply E1. rewrite ?shiftl_S in E2.
   now apply (left_cancellation (.*.) 2).
  apply E1. now rewrite ?shiftl_S, E2.
Qed.

Global Instance shiftl_nonzero x n : 
  PropHolds (x ≠ 0) → PropHolds (x ≪ n ≠ 0).
Proof. 
  intros E1 E2. apply E1. 
  apply (injective (≪ n)).
  now rewrite shiftl_base_0.
Qed.

Context `{oA : Order A} `{!SemiRingOrder oA} `{!TotalOrder oA} 
  `{!PropHolds (0 < (2:A))} `{!OrderPreservingBack ((2:A) *.)}.

Global Instance: ∀ n, OrderPreserving (≪ n).
Proof.
  repeat (split; try apply _).
  intros x y E. pattern n. apply biinduction; clear n; intros.
    solve_proper.
   now rewrite 2!shiftl_0.
  rewrite ?shiftl_S.
  split; intros.
   now apply (order_preserving (2 *.)). 
  now apply (order_preserving_back (2 *.)).
Qed.

Global Instance: ∀ n, OrderPreservingBack (≪ n).
Proof.
  repeat (split; try apply _).
  intros x y. pattern n. apply biinduction; clear n.
    solve_proper.
   now rewrite 2!shiftl_0 .
  intros m. rewrite ?shiftl_S.
  split; intros E1 E2.
   apply E1. now apply (order_preserving_back (2 *.)).
  apply E1. now apply (order_preserving (2 *.)).  
Qed.

Global Instance: ∀ n, StrictlyOrderPreserving (≪ n). 
Proof. intros. apply _. Qed.

Global Instance shiftl_nonneg (x : A) (n : B) : PropHolds (0 ≤ x) → PropHolds (0 ≤ x ≪ n).
Proof.
  intro. rewrite <-(shiftl_base_0 n).
  now apply (order_preserving (≪ n)).
Qed.

Global Instance shiftl_pos (x : A) (n : B) : PropHolds (0 < x) → PropHolds (0 < x ≪ n).
Proof.
  intro. rewrite <-(shiftl_base_0 n).
  now apply (strictly_order_preserving (≪ n)).
Qed.
End shiftl.

Section shiftl_field_integers.
  Context `{Field A} `{Integers B} `{∀ x y : A, Stable (x = y)} `{!PropHolds ((2:A) ≠ 0)} `{!ShiftLSpec A B sl}.

  Lemma shiftl_int_pow `{!IntPowSpec A B ipw} x n : x ≪ n = x * 2 ^ n.
  Proof.
    pose proof int_pow_proper.
    revert n. apply biinduction.
      solve_proper.
     now rewrite shiftl_0, int_pow_0, rings.mult_1_r.
    intros n.
    rewrite shiftl_S, int_pow_S by solve_propholds.
    rewrite associativity, (commutativity x 2), <-associativity.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) 2).
  Qed.
End shiftl_field_integers.

Section preservation.
  Context `{SemiRing B} `{!Biinduction B}
    `{Ring A1} `{!ShiftLSpec A1 B sl1} `{Ring A2} `{!LeftCancellation (.*.) (2:A2)} `{!ShiftLSpec A2 B sl2} 
    `{!SemiRing_Morphism (f : A1 → A2)}.

  Lemma preserves_shiftl x (n : B) : f (x ≪ n) = (f x) ≪ n.
  Proof.
    revert n. apply biinduction.
      solve_proper.
     now rewrite 2!shiftl_0.
    intros n; split; intros IH.
     rewrite 2!shiftl_S.
     now rewrite rings.preserves_mult, rings.preserves_2, IH.
    apply (left_cancellation (.*.) 2).
    rewrite <-(rings.preserves_2 (f:=f)) at 1. 
    rewrite <-rings.preserves_mult, <-shiftl_S, IH.
    now rewrite shiftl_S.
  Qed.
End preservation.

Section exp_preservation.
  Context `{SemiRing B1} `{!Biinduction B1} `{SemiRing B2} `{!Biinduction B2}
   `{Ring A}  `{!LeftCancellation (.*.) (2:A)} `{!ShiftLSpec A B1 sl1} `{!ShiftLSpec A B2 sl2} 
   `{!SemiRing_Morphism (f : B1 → B2)}.

  Lemma preserves_shiftl_exp x (n : B1) : x ≪ f n = x ≪ n.
  Proof.
    revert n. apply biinduction.
      solve_proper.
     now rewrite rings.preserves_0, ?shiftl_0.
    intros n.
    rewrite rings.preserves_plus, rings.preserves_1, ?shiftl_S.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) 2).
  Qed.
End exp_preservation.

Section default_shiftl_naturals.
  Context `{SemiRing A} `{Naturals B} `{!NatPowSpec A B pw}.

  Global Instance default_shiftl: ShiftL A B | 10 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl.
  Proof. now apply shiftl_spec_from_nat_pow. Qed.
End default_shiftl_naturals.

Section default_shiftl_integers.
  Context `{Field A} `{Integers B} `{!IntPowSpec A B ipw} `{∀ x y : A, Decision (x = y)} `{!PropHolds ((2:A) ≠ 0)}.

  Global Instance default_shiftl_int: ShiftL A B | 9 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl_int.
  Proof. now apply shiftl_spec_from_int_pow. Qed.
End default_shiftl_integers.
