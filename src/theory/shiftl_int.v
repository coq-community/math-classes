Require
  orders.integers theory.fields.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.int_pow.
Require Export 
  theory.shiftl.

(* This section contains a lot of duplication: most lemmas stated in theory.shiftl for 
  shifting with a natural  are restated for shifting with an integer. However, those proofs
  are trivial, because we can rewrite to nat_pow, while we can't do that here.

  Todo: figure out a way to get rid of some duplication. 
*)
Section shift_left_integers.
Context `{IntegralDomain A} `{!LeftCancellation (.*.) (2:A)} `{Integers B} 
  `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB} `{!ShiftLSpec A B sl}.

Add Ring A3: (rings.stdlib_semiring_theory A).
Add Ring B3: (rings.stdlib_semiring_theory B).

Lemma shiftl_int_shiftl `{Naturals B2} `{!ShiftLSpec A B2 sl2} `{!SemiRing_Morphism (f : B2 → B)} x n : 
  x ≪ f n = x ≪ n.
Proof. 
  revert n. apply naturals.induction.
    solve_proper.
   now rewrite rings.preserves_0, ?shiftl_0.
  intros n E.
  rewrite rings.preserves_plus, rings.preserves_1, shiftl_S.
  rewrite E, shiftl_S. ring.
Qed.

Lemma shiftl_int_nat_pow `{Naturals B2} `{!NatPowSpec A B2 pw} `{!SemiRing_Morphism (f : B2 → B)} x n : 
  x ≪ f n = x * 2 ^ n.
Proof. rewrite shiftl_int_shiftl. apply shiftl_nat_pow. Qed.

Global Instance shiftl_int_base_0: LeftAbsorb (≪) 0.
Proof. 
  intros n. pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now apply shiftl_0.
  intros n; split; intros E.
   rewrite shiftl_S, E. ring.
  apply (left_cancellation (.*.) 2).
  rewrite <-shiftl_S, E. ring.
Qed.

Lemma shiftl_int_exp_plus x n m : x ≪ (n + m) = x ≪ n ≪ m.
Proof.
  pattern m. apply integers.biinduction; clear m.
    solve_proper.
   now rewrite shiftl_0, rings.plus_0_r.
  intros m.
  setoid_replace (n + (1 + m)) with (1 + (n + m)) by ring.
  rewrite ?shiftl_S.
  split; intros E.
   now rewrite E.
  now apply (left_cancellation (.*.) 2).
Qed.

Lemma shiftl_int_order x n m: x ≪ n ≪ m  = x ≪ m ≪ n.
Proof. rewrite <-?shiftl_int_exp_plus. now rewrite commutativity. Qed.

Lemma shiftl_int_mult x y n : x * (y ≪ n) = (x * y) ≪ n.
Proof. 
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now rewrite ?shiftl_0.
  intros m.
  rewrite ?shiftl_S.
  split; intros E.
   rewrite <-E. ring.
  apply (left_cancellation (.*.) 2). rewrite <-E. ring.
Qed.

Lemma shiftl_int_base_plus x y n : (x + y) ≪ n  = x ≪ n + y ≪ n.
Proof.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now rewrite ?shiftl_0.
  intros m. rewrite ?shiftl_S.
  split; intros E.
   rewrite E. ring.
  apply (left_cancellation (.*.) 2). rewrite E. ring.
Qed.

Lemma shiftl_int_opp x n : (-x) ≪ n = -(x ≪ n).
Proof.
  rewrite (rings.opp_mult x), (rings.opp_mult (x ≪ n)).
  symmetry. now apply shiftl_int_mult.
Qed.

Global Instance shiftl_int_nonzero `{!PropHolds ((2:A) ≠ 0)} x n : 
  PropHolds (x ≠ 0) → PropHolds (x ≪ n ≠ 0).
Proof.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now rewrite shiftl_0.
  intros m. rewrite ?shiftl_S.
  split; intros E1 E2. 
   solve_propholds.
  intros E3. apply E1; auto. rewrite E3. ring.
Qed.

Context `{oA : Order A} `{!RingOrder oA} `{!TotalOrder oA} `{∀ x y, Decision (x = y)}.

Global Instance shiftl_int_nonneg (x : A) (n : B) : PropHolds (0 ≤ x) → PropHolds (0 ≤ x ≪ n).
Proof.
  intros nonneg.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now rewrite shiftl_0.
  intros m. rewrite ?shiftl_S.
  split; intros E.
   solve_propholds.
  red. apply (order_preserving_back (2 *.)). 
  now rewrite rings.mult_0_r.
Qed.

Global Instance shiftl_int_pos (x : A) (n : B) : PropHolds (0 < x) → PropHolds (0 < x ≪ n).
Proof.
  intros [E1 E2]. split.
   now apply shiftl_int_nonneg.
  apply not_symmetry, shiftl_int_nonzero. now apply not_symmetry.
Qed.
End shift_left_integers.

Section shift_left_field_integers.
  Context `{Field A} `{Integers B} `{∀ x y : A, Decision (x = y)} `{!PropHolds ((2:A) ≠ 0)}.

  Add Ring A4: (rings.stdlib_semiring_theory A).

  Lemma shiftl_spec_from_int_pow `{!IntPowSpec A B ip} (sl : ShiftL A B) :
    (∀ x n, x ≪ n = x * 2 ^ n) → ShiftLSpec A B sl.
  Proof.
    intros spec.
    split.
      intros ? ? E1 ? ? E2.
      rewrite 2!spec. now rewrite E1, E2.
     intro x. rewrite spec, int_pow_0. ring.
    intros x n. rewrite 2!spec. rewrite int_pow_S by solve_propholds. ring.
  Qed.

  Context `{!ShiftLSpec A B sl}.

  Lemma shiftl_int_pow `{!IntPowSpec A B ipw} x n : x ≪ n = x * 2 ^ n.
  Proof. 
    revert n. apply integers.biinduction.
      solve_proper.
     rewrite shiftl_0, int_pow_0. ring.
    intros n; split; intros IH. 
     rewrite shiftl_S, IH, int_pow_S. ring.
     apply (rings.ne_0 (2:A)). 
    apply (left_cancellation (.*.) 2).
    rewrite <-shiftl_S, IH.
    rewrite int_pow_S. ring.
    apply (rings.ne_0 (2:A)).
  Qed.
End shift_left_field_integers.

Section preservation_integers.
  Context `{Integers B} `{Ring A1} `{!ShiftLSpec A1 B sl1} `{Ring A2} `{!ShiftLSpec A2 B sl2} 
    {f : A1 → A2} `{!SemiRing_Morphism f} `{!LeftCancellation (.*.) (2:A2)}.

  Lemma preserves_shiftl_int x (n : B) : f (x ≪ n) = (f x) ≪ n.
  Proof.
    revert n. apply integers.biinduction.
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
End preservation_integers.

Section exp_preservation.
  Context `{Ring A} `{Integers B1} `{Integers B2}  `{!ShiftLSpec A B1 sl1} `{!ShiftLSpec A B2 sl2} 
    {f : B1 → B2} `{!SemiRing_Morphism f} `{!LeftCancellation (.*.) (2:A)}.

  Lemma preserves_shiftl_int_exp x (n : B1) : x ≪ f n = x ≪ n.
  Proof.
    revert n. apply integers.biinduction.
      solve_proper.
     now rewrite rings.preserves_0, ?shiftl_0.
    intros n.
    rewrite rings.preserves_plus, rings.preserves_1, ?shiftl_S.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) 2).
  Qed.
End exp_preservation.

Section default_shiftl_integers.
  Context `{Field A} `{Integers B} `{!IntPowSpec A B ipw} `{∀ x y : A, Decision (x = y)} `{!PropHolds ((2:A) ≠ 0)}.

  Global Instance default_shiftl_int: ShiftL A B | 9 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl_int.
  Proof. now apply shiftl_spec_from_int_pow. Qed.
End default_shiftl_integers.
