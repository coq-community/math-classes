Require
  theory.naturals theory.integers.
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

  Global Instance shiftl_proper: Proper ((=) ==> (=) ==> (=)) shiftl.
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    rewrite (shiftl_correct x1 x2). rewrite (shiftl_correct y1 y2).
    rewrite E1, E2. reflexivity. 
  Qed.

  Add Ring A2: (rings.stdlib_semiring_theory A).
  Add Ring B2: (rings.stdlib_semiring_theory B).

  Global Instance: LeftAbsorb shiftl 0.
  Proof. intro. rewrite shiftl_correct. ring. Qed.

  Global Instance: RightIdentity shiftl 0.
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

  Context `{IntegersToRing A} `{!Integers A}.

  Lemma shiftl_nonzero x y: x ≠ 0 → x ≪ y ≠ 0.
  Proof with auto.
    intros E1 E2. rewrite shiftl_correct in E2. 
    apply (no_zero_divisors x). split... 
    exists (2 ^ y); split...
    apply nat_pow_nonzero.
    apply integers.two_nonzero.
  Qed.

  (* x ≪ b = y ≪ b → x = y *)
  Lemma shiftl_inj n : Injective (flip shiftl n).
  Proof.
    repeat (split; try apply _).
    intros x y E. unfold flip in E. do 2 rewrite shiftl_correct in E.
    apply rings.mult_injective with (2 ^ n).
    apply nat_pow_nonzero, integers.two_nonzero.
    rewrite commutativity, E. ring.
  Qed.
End shift_left_properties.

(*
(* * Shift Right *)
Section shift_right_properties.
  Context `{SemiRing A} `{Naturals B} `{!NatPow A B} `{Order A} `{sr : !ShiftRight A B}.

  Lemma shiftr_correct x y : x ≤ (x ≫ y) * 2 ^ y < x.
  Proof.
    unfold shiftr. unfold shiftr_sig. 
    destruct sr. simpl. auto.
  Qed.
  
  Context `{sl : !ShiftLeft A B}.
  Lemma shiftr_shiftl_correct x y : x ≤ (x ≫ y) ≪ y < x.
  Proof.
    unfold shiftr, shiftl, shiftr_sig, shiftl_sig.  destruct sl, sr. simpl in *. split. destruct a. destruct H2. Timeout 5 rewrite e1.
    rewrite shiftl_correct.
    unfold shiftr. unfold shiftr_sig. 
    destruct sr. simpl. auto.
  Qed.

  Lemma shiftl_shiftr_correct x y : x = (x ≪ y) ≫ y.
  
  Global Instance shiftr_proper: Proper ((=) ==> (=) ==> (=)) shiftr.
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    rewrite (shiftl_correct x1 x2). rewrite (shiftl_correct y1 y2).
    rewrite E1, E2. reflexivity. 
  Qed.

  Add Ring A3: (rings.stdlib_semiring_theory A).
  Add Ring B3: (rings.stdlib_semiring_theory B).

  Global Instance: LeftAbsorb shiftl 0.
  Proof. intro. rewrite shiftl_correct. ring. Qed.

  Global Instance: RightIdentity shiftl 0.
  Proof. intro. rewrite shiftl_correct. rewrite nat_pow_0. ring. Qed.

  Lemma shiftr_order x y z: x ≪ y ≪ z  = x ≪ z ≪ y.
  Proof. do 4 rewrite shiftl_correct. ring. Qed.

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
End shift_right_properties.  *)

Global Program Instance default_shiftl `{SemiRing A} `{Naturals B} `{!NatPow A B} : ShiftLeft A B | 10 
  := λ x y, x * 2 ^ y.
Next Obligation. reflexivity. Qed.