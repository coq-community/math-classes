Require
  orders.integers theory.fields.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.nat_pow theory.int_pow.

(* * Properties of [shiftl] on the naturals *)
Section shift_left_naturals.
  Context `{SemiRing A} `{Naturals B}.

  Add Ring A2: (rings.stdlib_semiring_theory A).
  Add Ring B2: (rings.stdlib_semiring_theory B).

  Lemma shiftl_spec_from_nat_pow `{!NatPowSpec A B np} (sl : ShiftL A B) :
    (∀ x n, x ≪ n = x * 2 ^ n) → ShiftLSpec A B sl.
  Proof.
    intros spec.
    split.
      intros ? ? E1 ? ? E2.
      do 2 rewrite spec. now rewrite E1, E2.
     intro x. rewrite spec, nat_pow_0. ring.
    intros x n. do 2 rewrite spec. rewrite nat_pow_S. ring.
  Qed.

  Context `{!ShiftLSpec A B sl}.

  Global Instance: Proper ((=) ==> (=) ==> (=)) (≪) | 1.
  Proof. apply shiftl_proper. Qed.

  Lemma shiftl_nat_pow `{!NatPowSpec A B np} x n : x ≪ n = x * 2 ^ n.
  Proof.
    revert n. apply naturals.induction.
      solve_proper.
     rewrite nat_pow_0. now rewrite 2!right_identity.
    intros ? E. rewrite nat_pow_S, shiftl_S, E. ring.
  Qed.

  Global Instance: LeftAbsorb (≪) 0.
  Proof. intro. rewrite shiftl_nat_pow. ring. Qed.

  Lemma shiftl_order x y z: x ≪ y ≪ z  = x ≪ z ≪ y.
  Proof. rewrite 4!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_order_4a x y1 y2 y3: x ≪ y1 ≪ y2 ≪ y3  = x ≪ y3 ≪ y2 ≪ y1.
  Proof. rewrite 6!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_order_4b x y1 y2 y3: x ≪ y1 ≪ y2 ≪ y3  = x ≪ y2 ≪ y3 ≪ y1.
  Proof. rewrite 6!shiftl_nat_pow. ring. Qed.

  Lemma mult_shiftl x y z: x * (y ≪ z) = (x * y) ≪ z.
  Proof. rewrite 2!shiftl_nat_pow. ring. Qed.

  Lemma mult_shiftl_1 x y: x ≪ y = x * (1 ≪ y).
  Proof. rewrite 2!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_plus_base x y z: (x + y) ≪ z  = x ≪ z + y ≪ z.
  Proof. rewrite 3!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_plus_exp x y z: x ≪ (y + z) = x ≪ y ≪ z.
  Proof. rewrite 3!shiftl_nat_pow. rewrite nat_pow_exp_plus. ring. Qed.

  Lemma mult_r_shiftl_shiftl x y z1 z2 : (x * (y ≪ z1)) ≪ z2 = (x * y) ≪ (z1 + z2).
  Proof. rewrite 3!shiftl_nat_pow. rewrite nat_pow_exp_plus. ring. Qed.

  Lemma mult_l_shiftl_shiftl x y z1 z2 : ((x ≪ z1) * y) ≪ z2 = (x * y) ≪ (z1 + z2).
  Proof. rewrite 3!shiftl_nat_pow. rewrite nat_pow_exp_plus. ring. Qed.

  Lemma opp_shiftl `{GroupInv A} `{!Ring A} x y : (-x) ≪ y = -(x ≪ y).
  Proof.
    rewrite 2!shiftl_nat_pow.
    rewrite rings.opp_mult. symmetry. rewrite rings.opp_mult at 1.
    ring.
  Qed.

  Context `{!NoZeroDivisors A} `{!NeZero (1:A)} `{!NeZero (2:A)} `{∀z, NeZero z → RightCancellation (.*.) z}.

  Lemma shiftl_nonzero x y: x ≠ 0 → x ≪ y ≠ 0.
  Proof with auto.
    intros E1 E2. rewrite shiftl_nat_pow in E2. 
    apply (no_zero_divisors x). split... 
    exists (2 ^ y); split...
    apply nat_pow_nonzero.
    apply (ne_zero 2).
  Qed.

  (* x ≪ b = y ≪ b → x = y *)
  Lemma shiftl_inj n : Injective (flip shiftl n).
  Proof with auto.
    repeat (split; try apply _).
    intros x y E. unfold flip in E. do 2 rewrite shiftl_nat_pow in E.
    apply (rings.right_cancellation_ne_0 (.*.) (2 ^ n))...
    apply nat_pow_nonzero. apply (ne_zero 2).
  Qed.
End shift_left_naturals.

Section preservation.
  Context `{Naturals B} `{SemiRing A1} `{!ShiftLSpec A1 B sl1} `{SemiRing A2} `{!ShiftLSpec A2 B sl2} 
    {f : A1 → A2} `{!SemiRing_Morphism f}.

  Lemma preserves_shiftl x (n : B) : f (x ≪ n) = (f x) ≪ n.
  Proof.
    do 2 rewrite shiftl_nat_pow.
    rewrite rings.preserves_mult.
    rewrite preserves_nat_pow.
    now rewrite rings.preserves_2.
  Qed.
End preservation.

Section default_shiftl.
  Context `{SemiRing A} `{Naturals B} `{!NatPowSpec A B pw}.

  Global Instance default_shiftl: ShiftL A B | 10 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl.
  Proof. now apply shiftl_spec_from_nat_pow. Qed.
End default_shiftl.

Section shift_left_integers.
  Context `{Field A} `{Integers B} `{∀ x y : A, Decision (x = y)} `{!NeZero (2:A)}.

  Add Ring A: (rings.stdlib_semiring_theory A).
  Add Ring B: (rings.stdlib_ring_theory B).

  Lemma shiftl_spec_from_int_pow `{!IntPowSpec A B ip} (sl : ShiftL A B) :
    (∀ x n, x ≪ n = x * 2 ^ n) → ShiftLSpec A B sl.
  Proof.
    intros spec.
    split.
      intros ? ? E1 ? ? E2.
      do 2 rewrite spec. now rewrite E1, E2.
     intro x. rewrite spec, int_pow_0. ring.
    intros x n. do 2 rewrite spec. rewrite int_pow_S. ring.
    apply (ne_zero (2:A)).
  Qed.

  Context `{!ShiftLSpec A B sl}.

  Global Instance: Proper ((=) ==> (=) ==> (=)) (≪) | 1.
  Proof. apply shiftl_proper. Qed.

  Lemma shiftl_int_pow `{!IntPowSpec A B ipw} x n : x ≪ n = x * 2 ^ n.
  Proof. 
    revert n. apply integers.biinduction.
      solve_proper.
     rewrite shiftl_0, int_pow_0. ring.
    intros n; split; intros IH. 
     rewrite shiftl_S, IH, int_pow_S. ring.
     apply (ne_zero (2:A)). 
    apply (left_cancellation (.*.) 2).
    rewrite <-shiftl_S, IH.
    rewrite int_pow_S. ring.
    apply (ne_zero (2:A)).
  Qed.
End shift_left_integers.

Section preservation_integers.
  Context `{Integers B} `{Ring A1} `{!ShiftLSpec A1 B sl1} `{Ring A2} `{!ShiftLSpec A2 B sl2} 
    {f : A1 → A2} `{!SemiRing_Morphism f} `{!LeftCancellation (.*.) (2:A2)}.

  Add Ring Ba: (rings.stdlib_ring_theory B).

  Lemma preserves_shiftl_int x (n : B) : f (x ≪ n) = (f x) ≪ n.
  Proof.
    revert n. apply integers.biinduction.
      solve_proper.
     now do 2 rewrite shiftl_0.
    intros n; split; intros IH.
     do 2 rewrite shiftl_S.
     now rewrite rings.preserves_mult, rings.preserves_2, IH.
    apply (left_cancellation (.*.) 2).
    rewrite <-(rings.preserves_2 (f:=f)) at 1. 
    rewrite <-rings.preserves_mult, <-shiftl_S, IH.
    now rewrite shiftl_S.
  Qed.
End preservation_integers.

Section default_shiftl_integers.
  Context `{Field A} `{Integers B} `{!IntPowSpec A B ipw} `{∀ x y : A, Decision (x = y)} `{!NeZero (2:A)}.

  Global Instance default_shiftl_int: ShiftL A B | 9 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl_int.
  Proof. now apply shiftl_spec_from_int_pow. Qed.
End default_shiftl_integers.
