(* This module should never be Import-ed, only Require-d. *)

Set Automatic Introduction.

Require
  theory.categories.
Require Import
  Morphisms Ring
  abstract_algebra interfaces.naturals theory.rings.

Instance nat_equiv: Equiv nat := eq.

Instance: RingPlus nat := plus.
Instance: RingZero nat := 0%nat.
Instance: RingOne nat := 1%nat.
Instance: RingMult nat := mult.

(* propers: *)
Instance: Proper (equiv ==> equiv ==> equiv) plus.
Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper (equiv ==> equiv ==> equiv) mult.
Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

(* properties: *)
Instance: Associative plus := Plus.plus_assoc.
Instance: Associative mult := Mult.mult_assoc.
Instance: Commutative plus := Plus.plus_comm.
Instance: Commutative mult := Mult.mult_comm.
Instance: Distribute mult plus :=
  { distribute_l := Mult.mult_plus_distr_l; distribute_r := Mult.mult_plus_distr_r }.

Instance: SemiGroup nat (op:=plus).
Instance: SemiGroup nat (op:=mult).
Instance: Monoid _ (op:=plus) (unit:=0%nat) := { monoid_lunit := Plus.plus_0_l; monoid_runit := Plus.plus_0_r }.
Instance: Monoid _ (op:=mult) (unit:=1%nat) := { monoid_lunit := Mult.mult_1_l; monoid_runit := Mult.mult_1_r }.
Instance nat_semiring: SemiRing nat := { mult_0_l := Mult.mult_0_l }.

(* misc *)
Global Instance: forall x y: nat, Decision (x == y) := Peano_dec.eq_nat_dec.

Add Ring nat: (theory.rings.stdlib_semiring_theory nat).

Close Scope nat_scope.

Module for_another_semiring.
Section contents.

  Context `{SemiRing R}.

  Let toR := naturals_to_semiring nat R.

  Add Ring R: (stdlib_semiring_theory R).

  Instance f_proper: Proper (equiv ==> equiv) toR.
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

  Let f_preserves_0: toR 0 == 0.
  Proof. reflexivity. Qed.

  Let f_preserves_1: toR 1 == 1.
  Proof. unfold naturals_to_semiring. simpl. ring. Qed.

  Let f_preserves_plus a a': toR (a + a') == toR a + toR a'.
  Proof with ring.
   induction a. change (toR a' == 0 + toR a')...
   change (toR (a + a') + 1 == toR (a) + 1 + toR a'). rewrite IHa...
  Qed.

  Let f_preserves_mult a a': toR (a * a') == toR a * toR a'.
  Proof with ring.
   induction a. change (0 == 0 * toR a')...
   change (toR (a' + a * a') == (toR a + 1) * toR a').
   rewrite f_preserves_plus, IHa...
  Qed.

  Instance f_mor: SemiRing_Morphism (naturals_to_semiring nat R).
   repeat (constructor; try apply _).
      apply f_preserves_plus.
     apply f_preserves_0.
    apply f_preserves_mult.
   apply f_preserves_1.
  Qed.

End contents.
End for_another_semiring.

Lemma initial: categories.proves_initial (fun x =>
   @varieties.semiring.arrow_from_morphism_from_instance_to_object nat _  _ _ _ _ _ x _
    (@for_another_semiring.f_mor _ _ _ _ _ _ (varieties.semiring.from_object x))).
Proof.
 intros y [x h] [] a. simpl in *. 
 pose proof (varieties.semiring.from_object y).
 pose proof (@varieties.semiring.morphism_from_ua nat nat_equiv y _ _ _ x h _ _ tt).
 induction a. symmetry. apply preserves_0.
 change (naturals_to_semiring nat (y tt) a + 1 == x tt (1 + a)).
 rewrite IHa, preserves_plus, preserves_1.
 apply commutativity.
Qed.

Global Instance nat_Naturals: Naturals nat.
Proof @Build_Naturals nat _ _ _ _ _ _ _ (@for_another_semiring.f_mor) initial.

Lemma predefined_le_coincides (x y: nat): (x <= y)%nat -> x <= y.
Proof.
 induction 1 as [| n _ [m []]]. reflexivity.
 exists (S m). change (x + (1 + m) == 1 + (x + m)). ring.
Qed.

Lemma predefined_le_coincides_rev (x y: nat): x <= y -> (x <= y)%nat.
Proof. intros [z []]. auto with arith. Qed.

Program Instance: forall x y: nat, Decision (x <= y) :=
  match Compare_dec.le_lt_dec x y with
  | left E => left (predefined_le_coincides _ _ E)
  | right E => right _
  end.

Next Obligation.
 intro. apply (Lt.lt_not_le y x). assumption.
 apply predefined_le_coincides_rev. assumption.
Qed. 

Instance: TotalOrder natural_precedes.
Proof.
 intros x y. destruct (Compare_dec.le_lt_dec x y); [left | right];
  apply predefined_le_coincides; auto with arith.
Qed.

Program Instance: NatDistance nat := fun (x y: nat) =>
  if decide (natural_precedes x y) then minus y x else minus x y.

Next Obligation. destruct H as [x0 []]. left. rewrite Minus.minus_plus. reflexivity. Qed.

Next Obligation.
 destruct (total_order x y). intuition.
 right.
 change ((y + (x - y))%nat == x).
 rewrite (Minus.le_plus_minus_r y x). reflexivity.
 apply predefined_le_coincides_rev. assumption.
Qed.

(* Two simple omissions in the standard library that we prove for nats and then
 lift to arbitrary Naturals in theory.naturals: *)

Lemma Mult_mult_reg_l: forall n m p: nat, ~ p = 0 -> mult p n = mult p m -> n = m.
Proof.
 destruct p. intuition.
 intros. apply Le.le_antisym; apply Mult.mult_S_le_reg_l with p; rewrite H0; constructor.
Qed.

Lemma Mult_nz_mult_nz (x y: nat): ~ y == 0 -> ~ x == 0 -> ~ y * x == 0.
Proof. intros A B C. destruct (Mult.mult_is_O y x C); intuition. Qed.
