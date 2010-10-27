Require Import
  Morphisms Ring Program
  integers naturals
  abstract_algebra 
  canonical_names rings.

(* Todo, move theory to a seperate file *)
Section nat_pow.
  Context `{SemiRing R}.
  
  Add Ring R: (stdlib_semiring_theory R).

  Fixpoint nat_pow (x: R) (n : nat) : R := match n with
  | 0 => 1
  | S n => x * (nat_pow x n)
  end.

  Global Instance: Proper ((=) ==> (=) ==> (=)) nat_pow.
  Proof with try reflexivity.
   intros x y E a ? [].
   induction a; simpl...
   rewrite IHa, E...
  Qed.

  Lemma nat_pow_exp_sum (x y: nat) (n: R) : 
    nat_pow n (x + y) = nat_pow n x * nat_pow n y.
  Proof with auto.
    induction x as [|x]; simpl... 
    ring.
    rewrite IHx. ring. 
  Qed.
  
  (* Todo: get rid of {inv: GroupInv R} *)
  Context {inv: GroupInv R} `{!IntegralDomain R}.

  Lemma nat_pow_nonzero  (x: nat) (n: R) : n ≠ 0 → nat_pow n x ≠ 0.
  Proof with eauto. 
    induction x; simpl; repeat intro.
    firstorder.
    apply (intdom_nozeroes R n); split... 
  Qed. 
End nat_pow.

Section shift_left.
  Context A B `{SemiRing A} `{Naturals B}.

  Class ShiftLeft := shiftl_sig: ∀ (x : A) (y : B), 
    { z: A | z = x * nat_pow (1+1) (naturals_to_semiring B nat y) }.
  Global Program Instance: ShiftLeft | 10 := λ x y, x * nat_pow (1+1) (naturals_to_semiring B nat y).
  Next Obligation. reflexivity. Qed.
End shift_left.

Definition shiftl `{ShiftLeft}: A → B → A := λ x y, proj1_sig (shiftl_sig A B x y).
Infix "≪" := shiftl (at level 33, left associativity).

Section shift_left_properties.
  Context `{SemiRing A} `{Naturals B} `{sl : !ShiftLeft A B}.

  Lemma shiftl_correct x y : x ≪ y = x * nat_pow (1+1) (naturals_to_semiring B nat y).
  Proof.
    unfold shiftl. unfold shiftl_sig. 
    destruct sl as [z E]. simpl. auto.
  Qed.

  Global Instance shiftl_proper: Proper ((=) ==> (=) ==> (=)) (@shiftl A B _ _ _ _ _ _).
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    rewrite (shiftl_correct x1 x2). rewrite (shiftl_correct y1 y2).
    rewrite E1, E2. reflexivity. 
  Qed.

  Add Ring A: (stdlib_semiring_theory A).
  Add Ring B: (stdlib_semiring_theory B).

  Global Instance: LeftAbsorb shiftl 0.
  Proof. intro. rewrite shiftl_correct. ring. Qed.

  Global Instance: RightIdentity shiftl 0.
  Proof. intro. rewrite shiftl_correct. rewrite preserves_0. simpl. apply right_identity. Qed.

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
  Proof. do 3 rewrite shiftl_correct. rewrite preserves_plus, nat_pow_exp_sum. ring. Qed.

  Lemma shiftl_nonzero `{GroupInv A} `{IntegersToRing A} `{!Integers A} x y: 
    x ≠ 0 → x ≪ y ≠ 0.
  Proof with auto.
   intros. rewrite shiftl_correct. intro.
   apply (no_zero_divisors x); split... 
   exists (nat_pow (1+1) (naturals_to_semiring B nat y)); split...
   apply nat_pow_nonzero.
   apply two_nonzero.
  Qed.

  Context `{GroupInv A} .
  Lemma opp_shiftl `{!Ring A} x y : (-x) ≪ y = -(x ≪ y).
  Proof.
   do 2 rewrite shiftl_correct. 
   rewrite ring_opp_mult. symmetry. rewrite ring_opp_mult at 1.
   ring.
  Qed.

  Context`{IntegersToRing A}.
  (* x ≪ b = y ≪ b → x = y *)
  Lemma shiftl_inj `{!Integers A} b : Injective (flip shiftl b).
  Proof.
   repeat (split; try apply _).
   intros x y E. unfold flip in E. do 2 rewrite shiftl_correct in E.
   apply mult_injective with (nat_pow (1 + 1) (naturals_to_semiring B nat b)).
    apply nat_pow_nonzero, two_nonzero.
   rewrite commutativity, E. ring.
  Qed.
End shift_left_properties.