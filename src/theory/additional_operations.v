Require
  theory.naturals theory.integers.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra 
  interfaces.naturals interfaces.integers interfaces.additional_operations.

(* * Ring Minus *)
Section ring_minus_properties.
  Context `{Ring R} `{minus : !RingMinus R}.

  Lemma ring_minus_correct x y : x - y = x + -y.
  Proof.
    unfold ring_minus. unfold ring_minus_sig. 
    destruct minus as [z E]. simpl. auto.
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> (=)) ring_minus.
  Proof.
    intros x1 y1 E1 x2 y2 E2.
    rewrite ring_minus_correct. rewrite ring_minus_correct.
    rewrite E1, E2. reflexivity.
  Qed.
End ring_minus_properties.


(* * Field Div *)
Section field_div_properties.
  Context `{Field R} `{div : !FieldDiv R}.

  Lemma field_div_correct x y : x / y = x * //y.
  Proof.
    unfold field_div. unfold field_div_sig. 
    destruct div as [z E]. simpl. auto.
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> (=)) field_div.
  Proof.
    intros x1 y1 E1 x2 y2 E2.
    rewrite (field_div_correct x1 x2). rewrite (field_div_correct y1 y2).
    rewrite E1, E2. reflexivity.
  Qed.
End field_div_properties.


(* * Nat Pow *)
Section nat_pow_properties.
  Context `{SemiRing A} `{Naturals B}.

  Add Ring A: (rings.stdlib_semiring_theory A).
  Add Ring B: (rings.stdlib_semiring_theory B).

  Global Instance nat_pow_spec_proper: Proper ((=) ==> (=) ==> (=) ==> iff) nat_pow_spec.
  Proof with eauto.
    intros x1 x2 E n1 n2 F y1 y2 G. 
    split; intro. eapply nat_pow_spec_proper'...
    eapply nat_pow_spec_proper'; try symmetry...
  Qed.

  Tactic Notation "gen_eq" constr(c) "as" ident(x) :=
    set (x := c) in *;
    let H := fresh in (assert (H : x = c) by reflexivity; clearbody x; revert H).

  Lemma nat_pow_spec_unique x n y1 y2 : 
    nat_pow_spec x n y1 → nat_pow_spec x n y2 → y1 = y2.
  Proof with eauto; try reflexivity.
    intros E F. generalize dependent y2. 
    induction E as [ | | ? ? ? ? ? ? G1 G2 G3]. 
    
    intros.
    gen_eq (0:B) as n. induction F as [ |  | ? ? ? ? ? ? G1 G2 G3 ]; intros...
    destruct (naturals.nz_one_plus_zero n)...
    rewrite <-G3. apply IHF. rewrite G2...

    intros.
    gen_eq (1+n) as m. generalize dependent n. generalize dependent y. 
    induction F as [ | | ? ? ? ? ? ? G1 G2 G3 ]; intros ? ? ? ? G4.
    destruct (naturals.nz_one_plus_zero n). symmetry...
    apply sg_mor... apply IHE. 
    apply (injective (ring_plus 1)) in G4. symmetry in G4. eapply nat_pow_spec_proper...
    rewrite <-G1, <-G3. apply (IHF _ n)... eapply nat_pow_spec_proper...
    intros. apply IHE. symmetry in G1. eapply nat_pow_spec_proper... rewrite G2...
 
    intros. rewrite <-G3. apply IHE. eapply nat_pow_spec_proper... 
  Qed.

  Section nat_pow_spec_from_properties.
  Context (f : A → B → A) ( f_proper : Proper ((=) ==> (=) ==> (=)) f )
    ( f_0 : ∀x, f x 0 = 1 ) ( f_S : ∀ x n,  f x (1+n) = x * (f x n) ).

  Lemma nat_pow_spec_from_properties x n : nat_pow_spec x n (f x n).
  Proof with eauto; try reflexivity.
    revert n. apply naturals.induction.
    intros ? ? E. rewrite E...
    rewrite f_0. apply nat_pow_spec_0...
    intros. rewrite f_S. eapply nat_pow_spec_S...
  Qed.
  End nat_pow_spec_from_properties.

  Context `{np : !NatPow A B}.
  Global Instance: Proper ((=) ==> (=) ==> (=)) nat_pow.
  Proof with eauto.
    intros x1 x2 E y1 y2 F. 
    unfold nat_pow, nat_pow_sig. do 2 destruct np. simpl.
    eapply nat_pow_spec_unique...
    eapply nat_pow_spec_proper... reflexivity. 
  Qed.

  Lemma nat_pow_0 x : x ^ 0 = 1.
  Proof with eauto.
   unfold nat_pow, nat_pow_sig. destruct np. simpl.
   eapply nat_pow_spec_unique... apply nat_pow_spec_0.
  Qed.

  Lemma nat_pow_S x n : x ^ (1+n) = x * x ^ n.
  Proof with eauto.
   unfold nat_pow, nat_pow_sig. do 2 destruct np. simpl.
   eapply nat_pow_spec_unique... eapply nat_pow_spec_S...
  Qed.

  Instance: RightIdentity nat_pow 1.
  Proof. 
    intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
    rewrite nat_pow_S, nat_pow_0. ring.
  Qed.
  
  Lemma nat_pow_exp_sum (x y: B) (n: A) : 
    nat_pow n (x + y) = nat_pow n x * nat_pow n y.
  Proof with auto.
    generalize dependent x. apply naturals.induction.
    intros ? ? E. rewrite E. tauto.
    rewrite nat_pow_0, left_identity. ring.
    intros x E. 
    rewrite <-associativity.
    do 2 rewrite nat_pow_S.
    rewrite E. ring.
  Qed.
  
  (* Todo: get rid of {inv: GroupInv R} *)
  Context {inv: GroupInv A} `{!IntegralDomain A}.

  Lemma nat_pow_nonzero  (x: B) (n: A) : n ≠ 0 → n ^ x ≠ 0.
  Proof with eauto.
    revert x.
    change (∀ x : B, (λ x, n ≠ 0 → n ^ x ≠ 0) x). apply naturals.induction.
    intros x1 x2 E. rewrite E. tauto.
    intros. rewrite nat_pow_0. firstorder.
    intros x E F G. rewrite nat_pow_S in G.
    apply (intdom_nozeroes A n); split... 
  Qed. 
End nat_pow_properties.

(* * Shift Left *)
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

(* * Default implementations *)
Global Program Instance default_ring_minus `{Ring R}: RingMinus R | 10 := λ x y, x + -y.
Next Obligation. reflexivity. Qed.

Global Program Instance default_field_div `{Field R} : FieldDiv R | 10 := λ x y, x * // `y.
Next Obligation. reflexivity. Qed.

Section nat_pow_default.
  Context A B `{SemiRing A} `{Naturals B}.
  
  Fixpoint nat_pow_rec (x: A) (n : nat) : A := match n with
  | 0 => 1
  | S n => x * (nat_pow_rec x n)
  end.

  Instance: Proper ((=) ==> (=) ==> (=)) nat_pow_rec.
  Proof with try reflexivity.
   intros x y E a ? [].
   induction a; simpl...
   rewrite IHa, E...
  Qed.

  Let nat_pow_default x n := nat_pow_rec x (naturals_to_semiring B nat n).
  Program Instance: NatPow A B | 10 := nat_pow_default.
  Next Obligation with try reflexivity.
    apply nat_pow_spec_from_properties; unfold nat_pow_default.
    intros ? ? E ? ? F. rewrite E, F...
    intros. rewrite rings.preserves_0. simpl...
    intros. rewrite rings.preserves_plus, rings.preserves_1, <-peano_naturals.S_nat_1_plus. simpl...
  Qed.
End nat_pow_default.

Global Program Instance default_shiftl `{SemiRing A} `{Naturals B} `{!NatPow A B} : ShiftLeft A B | 10 
  := λ x y, x * 2 ^ y.
Next Obligation. reflexivity. Qed.