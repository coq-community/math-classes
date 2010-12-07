Require
  theory.naturals theory.integers orders.orders.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.nat_pow.

(* * Properties of Shift Left *)
Section shift_left_properties.
  Context `{SemiRing A} `{Naturals B} `{!NatPow A B} `{sl : !ShiftLeft A B}.

  Lemma shiftl_correct x y : x ≪ y = x * 2  ^ y.
  Proof.
    unfold shiftl. unfold shiftl_sig. 
    destruct sl. simpl. auto.
  Qed.

  Global Instance shiftl_proper: Proper ((=) ==> (=) ==> (=)) (≪).
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    rewrite (shiftl_correct x1 x2). rewrite (shiftl_correct y1 y2).
    rewrite E1, E2. reflexivity. 
  Qed.

  Add Ring A2: (rings.stdlib_semiring_theory A).
  Add Ring B2: (rings.stdlib_semiring_theory B).

  Global Instance: LeftAbsorb (≪) 0.
  Proof. intro. rewrite shiftl_correct. ring. Qed.

  Global Instance: RightIdentity (≪) 0.
  Proof. intro. rewrite shiftl_correct. rewrite nat_pow_0. ring. Qed.

  Lemma shiftl_order x y z: x ≪ y ≪ z  = x ≪ z ≪ y.
  Proof. do 4 rewrite shiftl_correct. ring. Qed.

  Lemma shiftl_order_4a x y1 y2 y3: x ≪ y1 ≪ y2 ≪ y3  = x ≪ y3 ≪ y2 ≪ y1.
  Proof. do 6 rewrite shiftl_correct. ring. Qed.

  Lemma shiftl_order_4b x y1 y2 y3: x ≪ y1 ≪ y2 ≪ y3  = x ≪ y2 ≪ y3 ≪ y1.
  Proof. do 6 rewrite shiftl_correct. ring. Qed.

  Lemma mult_shiftl x y z: x * (y ≪ z) = (x * y) ≪ z.
  Proof. do 2 rewrite shiftl_correct. ring. Qed.

  Lemma mult_shiftl_1 x y: x ≪ y = x * (1 ≪ y).
  Proof. do 2 rewrite shiftl_correct. ring. Qed.

  Lemma shiftl_sum_base x y z: (x + y) ≪ z  = x ≪ z + y ≪ z.
  Proof. do 3 rewrite shiftl_correct. ring. Qed.

  Lemma shiftl_sum_exp x y z: x ≪ (y + z) = x ≪ y ≪ z.
  Proof. do 3 rewrite shiftl_correct. rewrite nat_pow_exp_sum. ring. Qed.

  Lemma mult_r_shiftl_shiftl x y z1 z2 : (x * (y ≪ z1)) ≪ z2 = (x * y) ≪ (z1 + z2).
  Proof. do 3 rewrite shiftl_correct. rewrite nat_pow_exp_sum. ring. Qed.

  Lemma mult_l_shiftl_shiftl x y z1 z2 : ((x ≪ z1) * y) ≪ z2 = (x * y) ≪ (z1 + z2).
  Proof. do 3 rewrite shiftl_correct. rewrite nat_pow_exp_sum. ring. Qed.

  Context `{GroupInv A} .

  Lemma opp_shiftl `{!Ring A} x y : (-x) ≪ y = -(x ≪ y).
  Proof.
    do 2 rewrite shiftl_correct.
    rewrite rings.ring_opp_mult. symmetry. rewrite rings.ring_opp_mult at 1.
    ring.
  Qed.

  Context `{!NoZeroDivisors A} `{!NeZero (1:A)} `{!NeZero (2:A)} `{∀z, NeZero z → RightCancellation ring_mult z}.

  Lemma shiftl_nonzero x y: x ≠ 0 → x ≪ y ≠ 0.
  Proof with auto.
    intros E1 E2. rewrite shiftl_correct in E2. 
    apply (no_zero_divisors x). split... 
    exists (2 ^ y); split...
    apply nat_pow_nonzero.
    apply (ne_zero 2).
  Qed.

  (* x ≪ b = y ≪ b → x = y *)
  Lemma shiftl_inj n : Injective (flip shiftl n).
  Proof with auto.
    repeat (split; try apply _).
    intros x y E. unfold flip in E. do 2 rewrite shiftl_correct in E.
    apply (rings.right_cancellation_ne_zero ring_mult (2 ^ n))...
    apply nat_pow_nonzero. apply (ne_zero 2).
  Qed.
End shift_left_properties.

(* * Default Shift Left implementation using Nat Pow*)
Global Program Instance default_shiftl `{SemiRing A} `{Naturals B} `{!NatPow A B} : ShiftLeft A B | 10 
  := λ x y, x * 2 ^ y.
Next Obligation. reflexivity. Qed.

(* * Properties of Shift Right *)
Section shift_right_properties.
  Context `{SemiRing A} `{Naturals B}.
  Context `{!NatPow A B} 
    `{sr : !ShiftRight A B}
    `{sl : !ShiftLeft A B}
    `{!NoZeroDivisors A} 
    `{!NeZero (1:A)} 
    `{!NeZero (2:A)} 
    `{!∀ z, NeZero z → LeftCancellation ring_mult z}.

  Hint Resolve orders.strictly_precedes_weaken.

  Lemma shiftr_correct (x : A) y : x ≤ (x ≫ y) * 2 ^ y < 2 * x.
  Proof.
    unfold shiftr. unfold shiftr_sig. 
    destruct sr. simpl. assumption.
  Qed.
  
  Lemma shiftr_shiftl_correct (x : A) y : x ≤ (x ≫ y) ≪ y < 2 * x.
  Proof.
    rewrite shiftl_correct. apply shiftr_correct. 
  Qed.
End shift_right_properties.

(*
  Lemma shiftl_shiftr_correct x y : x = (x ≪ y) ≫ y.
  Proof with auto.
    unfold shiftr. unfold shiftr_sig. 
    destruct sr as [z [E1 E2]]. simpl.
    apply (right_cancellation (≪) y). unfold flip.
    rewrite <-shiftl_correct in E1, E2. 
    apply (antisymmetry (≤))...
  Qed.

  Global Instance shiftr_proper: Proper ((=) ==> (=) ==> (=)) shiftr.
  Proof with auto. 
    intros x1 x2 E y1 y2 F. 
    unfold shiftr. unfold shiftr_sig. 
    destruct (sr x1 y1) as [z1 [Ez1 Fz1]], (sr x2 y2) as [z2 [Ez2 Fz2]]. simpl.
    rewrite F in Ez1, Fz1. 
    apply (rings.mult_injective (2 ^ y2)).
      apply nat_pow_nonzero, integers.two_nonzero.
    rewrite commutativity. symmetry. rewrite commutativity.
    transitivity x2. apply (antisymmetry (≤))...
    transitivity x1. symmetry... apply (antisymmetry (≤))...
  Qed.

  Add Ring A3: (rings.stdlib_semiring_theory A).
  Add Ring B3: (rings.stdlib_semiring_theory B).

  Global Instance: LeftAbsorb shiftr 0.
  Proof with auto; try reflexivity. 
    intros x. assert (0 = 0 ≪ x) as E. rewrite left_absorb...
    rewrite E at 1. symmetry. apply shiftl_shiftr_correct.
  Qed.  

  Global Instance: RightIdentity shiftr 0.
  Proof with auto; try reflexivity. 
    intros x. assert (x = x ≪ 0) as E. rewrite right_identity...
    rewrite E at 1. symmetry. apply shiftl_shiftr_correct.
  Qed.

  Lemma shiftr_sum_exp x y z: x ≫ (y + z) = x ≫ y ≫ z.
  Proof with auto; try reflexivity. 
    unfold shiftr. unfold shiftr_sig. 
    destruct (sr x y) as [z1 [Ez1 Fz1]]. simpl. 
    destruct (sr z1 z) as [z2 [Ez2 Fz2]]. simpl. 
    set (p:=(_ : RingPlus B)). (* why can't do this properly? *)
    destruct (sr x (@ring_plus B p y z)) as [z3 [Ez3 Fz3]]. simpl.
    apply (rings.mult_injective (2 ^ (y + z))).
      apply nat_pow_nonzero, integers.two_nonzero.
    rewrite commutativity. symmetry. rewrite commutativity. symmetry.
    transitivity x. apply (antisymmetry (≤))...

  Lemma shiftr_order x y z: x ≫ y ≫ z  = x ≫ z ≫ y.
  Proof with auto; try reflexivity.
    unfold shiftr. unfold shiftr_sig. 
    destruct (sr x y) as [z1 [Ez1 Fz1]], (sr x z) as [z2 [Ez2 Fz2]]. simpl.
    destruct (sr z1 z) as [z3 [Ez3 Fz3]], (sr z2 y) as [z4 [Ez4 Fz4]]. simpl.

  Lemma shiftr_order_4a x y1 y2 y3: x ≪ y1 ≪ y2 ≪ y3  = x ≪ y3 ≪ y2 ≪ y1.
  Proof. do 6 rewrite shiftl_correct. ring. Qed.

  Lemma shiftr_order_4b x y1 y2 y3: x ≪ y1 ≪ y2 ≪ y3  = x ≪ y2 ≪ y3 ≪ y1.
  Proof. do 6 rewrite shiftl_correct. ring. Qed.

  Lemma mult_shiftr x y z: x * (y ≪ z) = (x * y) ≪ z.
  Proof. do 2 rewrite shiftl_correct. ring. Qed.

  Lemma mult_shiftr_1 x y: x ≪ y = x * (1 ≪ y).
  Proof. do 2 rewrite shiftl_correct. ring. Qed.

  Lemma shiftr_sum_base x y z: (x + y) ≪ z  = x ≪ z + y ≪ z.
  Proof. do 3 rewrite shiftl_correct. ring. Qed.

  Lemma shiftr_sum_exp x y z: x ≪ (y + z) = x ≪ y ≪ z.
  Proof. do 3 rewrite shiftl_correct. rewrite nat_pow_exp_sum. ring. Qed.

  Context `{GroupInv A} .

  Lemma opp_shiftr `{!Ring A} x y : (-x) ≪ y = -(x ≪ y).
  Proof.
    do 2 rewrite shiftl_correct.
    rewrite rings.ring_opp_mult. symmetry. rewrite rings.ring_opp_mult at 1.
    ring.
  Qed.

  Context `{IntegersToRing A} `{!Integers A}.

  Lemma shiftr_nonzero x y: x ≠ 0 → x ≪ y ≠ 0.
  Proof with auto.
    intros E1 E2. rewrite shiftl_correct in E2. 
    apply (no_zero_divisors x). split... 
    exists (2 ^ y); split...
    apply nat_pow_nonzero.
    apply integers.two_nonzero.
  Qed.

  (* x ≪ b = y ≪ b → x = y *)
  Lemma shiftr_inj n : Injective (flip shiftl n).
  Proof.
    repeat (split; try apply _).
    intros x y E. unfold flip in E. do 2 rewrite shiftl_correct in E.
    apply rings.mult_injective with (2 ^ n).
    apply nat_pow_nonzero, integers.two_nonzero.
    rewrite commutativity, E. ring.
  Qed. 
End shift_right_properties.  

(* * Default Shift Left implementation using Nat Pow*)
Section default_shiftr.
  Context `{SemiRing A} 
    `{Naturals B} 
    `{!NatPow A B} 
    `{!DivEuclid A} 
    `{!NoZeroDivisors A} 
    `{!NeZero (1:A)}
    `{!NeZero (2:A)}

  Global Program Instance default_shiftr : ShiftRight A B | 10 
    := λ x y, div_euclid x (exist _ (2 ^ y) _).
  Next Obligation. eapply nat_pow_nonzero. apply (ne_zero 2). Qed.
  Next Obligation. admit. Qed.
End default_shiftr.
*)