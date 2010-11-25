(* This module should never be Import-ed, only Require-d. *)

Require ua_homomorphisms.
Require Import
  Morphisms Ring
  abstract_algebra interfaces.naturals theory.rings theory.categories.

Instance nat_equiv: Equiv nat := eq.

Instance: RingPlus nat := plus.
Instance: RingZero nat := 0%nat.
Instance: RingOne nat := 1%nat.
Instance: RingMult nat := mult.

(* propers: *)
Instance: Proper (equiv ==> equiv ==> equiv) plus.
Proof. unfold equiv, nat_equiv. apply _. Qed.
Instance: Proper (equiv ==> equiv ==> equiv) mult.
Proof. unfold equiv, nat_equiv. apply _. Qed.

(* properties: *)
Instance: Associative plus := Plus.plus_assoc.
Instance: Associative mult := Mult.mult_assoc.
Instance: Commutative plus := Plus.plus_comm.
Instance: Commutative mult := Mult.mult_comm.
Instance: Distribute mult plus :=
  { distribute_l := Mult.mult_plus_distr_l; distribute_r := Mult.mult_plus_distr_r }.
Instance: LeftIdentity plus 0 := Plus.plus_0_l.
Instance: RightIdentity plus 0 := Plus.plus_0_r.
Instance: LeftIdentity mult 1 := Mult.mult_1_l.
Instance: RightIdentity mult 1 := Mult.mult_1_r.
Instance: LeftAbsorb mult 0 := Mult.mult_0_l.

(* structures: *)
Instance: Setoid nat.
Instance: SemiGroup nat (op:=plus).
Instance: SemiGroup nat (op:=mult).
Instance: Monoid _ (op:=plus) (unit:=0%nat).
Instance: Monoid _ (op:=mult) (unit:=1%nat).
Instance: CommutativeMonoid _ (op:=mult) (unit:=1%nat).
Instance: CommutativeMonoid _ (op:=plus) (unit:=0%nat).
Instance nat_semiring: SemiRing nat.

(* misc *)
Global Instance: ∀ x y: nat, Decision (x = y) := Peano_dec.eq_nat_dec.

Add Ring nat: (theory.rings.stdlib_semiring_theory nat).

Close Scope nat_scope.

Module for_another_semiring.
Section contents.

  Context `{SemiRing R}.

  Let toR := naturals_to_semiring nat R.

  Add Ring R: (stdlib_semiring_theory R).

  Instance f_proper: Proper (equiv ==> equiv) toR.
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

  Let f_preserves_0: toR 0 = 0.
  Proof. reflexivity. Qed.

  Let f_preserves_1: toR 1 = 1.
  Proof. unfold naturals_to_semiring. simpl. ring. Qed.

  Let f_preserves_plus a a': toR (a + a') = toR a + toR a'.
  Proof with ring.
   induction a. change (toR a' = 0 + toR a')...
   change (toR (a + a') + 1 = toR (a) + 1 + toR a'). rewrite IHa...
  Qed.

  Let f_preserves_mult a a': toR (a * a') = toR a * toR a'.
  Proof with ring.
   induction a. change (0 = 0 * toR a')...
   change (toR (a' + a * a') = (toR a + 1) * toR a').
   rewrite f_preserves_plus, IHa...
  Qed.

  Global Instance: SemiRing_Morphism (naturals_to_semiring nat R).
   repeat (constructor; try apply _).
      apply f_preserves_plus.
     apply f_preserves_0.
    apply f_preserves_mult.
   apply f_preserves_1.
  Qed.

End contents.
End for_another_semiring.

Lemma S_nat_plus_1 x : S x ≡ x + 1.
Proof. rewrite commutativity. reflexivity. Qed.

Lemma S_nat_1_plus x : S x ≡ 1 + x.
Proof. reflexivity. Qed.

Instance: Initial (semiring.object nat).
Proof.
  intros. apply natural_initial. intros. 
  intro x. induction x. 
  replace 0%nat with (ring_zero:nat) by reflexivity.
  do 2 rewrite preserves_0. reflexivity.
  rewrite S_nat_1_plus.
  do 2 rewrite preserves_plus, preserves_1. 
  rewrite IHx. reflexivity.
Qed.

Global Instance nat_Naturals: Naturals nat.

Lemma predefined_le_coincides (x y: nat): (x <= y)%nat → x ≤ y.
Proof.
 induction 1 as [| n _ [m []]]. exists 0. rewrite preserves_0. ring.
 exists (S m).
 change (x + naturals_to_semiring nat nat (1 + m) =
    1 + (x + naturals_to_semiring nat nat m)).
 rewrite preserves_plus, preserves_1. ring. 
Qed.

Lemma predefined_le_coincides_rev (x y: nat): x ≤ y → (x <= y)%nat.
Proof. intros [z []]. auto with arith. Qed.

Program Instance le_nat_dec (x y: nat): Decision (x ≤ y) :=
  match Compare_dec.le_lt_dec x y with
  | left E => left (predefined_le_coincides _ _ E)
  | right E => right _
  end.

Next Obligation.
 intro. apply (Lt.lt_not_le y x). assumption.
 apply predefined_le_coincides_rev. assumption.
Qed. 

Instance: TotalOrder (sr_precedes (R:=nat)).
Proof.
 intros x y. destruct (Compare_dec.le_lt_dec x y); [left | right];
  apply predefined_le_coincides; auto with arith.
Qed.

Program Instance: NatDistance nat := λ x y: nat,
  if decide (x ≤ y) then minus y x else minus x y.

Next Obligation. destruct H as [x0 []]. left. rewrite Minus.minus_plus. reflexivity. Qed.

Next Obligation.
 destruct (total_order x y). intuition.
 right.
 change ((y + (x - y))%nat = x).
 rewrite (Minus.le_plus_minus_r y x). reflexivity.
 apply predefined_le_coincides_rev. assumption.
Qed.

(* Two simple omissions in the standard library that we prove for nats and then
 lift to arbitrary Naturals in theory.naturals: *)

Lemma Mult_mult_reg_l: ∀ n m p: nat, ~ p = 0 → mult p n = mult p m → n = m.
Proof.
 destruct p. intuition.
 intros. apply Le.le_antisym; apply Mult.mult_S_le_reg_l with p; rewrite H0; constructor.
Qed.

Lemma Mult_nz_mult_nz (x y: nat): ~ y = 0 → ~ x = 0 → ~ y * x = 0.
Proof. intros A B C. destruct (Mult.mult_is_O y x C); intuition. Qed.

(* On occasion we will be confronted with nat's minus operation, for which
 we prove a simple conditional preservation property: *)

Lemma preserves_minus `{Ring R} (f: nat → R) `{!SemiRing_Morphism f}
  x y (P: (y <= x)%nat): f (x - y)%nat = f x + - f y.
Proof.
 rewrite (Minus.le_plus_minus _ _ P: x = (y + (x - y)%nat)) at 2.
 rewrite preserves_plus, commutativity, associativity, plus_opp_l, plus_0_l.
 reflexivity.
Qed.
