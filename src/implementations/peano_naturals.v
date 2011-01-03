(* This module should never be Import-ed, only Require-d. *)

Require 
  ua_homomorphisms
  orders.orders theory.rings.
Require Import
  Morphisms Ring Arith_base
  abstract_algebra interfaces.naturals theory.categories
  interfaces.additional_operations.

Instance nat_equiv: Equiv nat := eq.

Instance: RingPlus nat := plus.
Instance: RingZero nat := 0%nat.
Instance: RingOne nat := 1%nat.
Instance: RingMult nat := mult.

(* propers: *)
Instance: Proper ((=) ==> (=) ==> (=)) plus.
Proof. unfold equiv, nat_equiv. apply _. Qed.
Instance: Proper ((=) ==> (=) ==> (=)) mult.
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
Instance: SemiRing nat.

(* misc *)
Global Instance: ∀ x y: nat, Decision (x = y) := eq_nat_dec.

Add Ring nat: (rings.stdlib_semiring_theory nat).

Close Scope nat_scope.

Instance: NaturalsToSemiRing nat :=
  λ _ _ _ _ _, fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Module for_another_semiring.
Section contents.

  Context `{SemiRing R}.

  Let toR := naturals_to_semiring nat R.

  Add Ring R: (rings.stdlib_semiring_theory R).

  Instance f_proper: Proper ((=) ==> (=)) toR.
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
  intros x y E. unfold equiv, nat_equiv in E. subst y. induction x. 
  replace 0%nat with (ring_zero:nat) by reflexivity.
  do 2 rewrite rings.preserves_0. reflexivity.
  rewrite S_nat_1_plus.
  do 2 rewrite rings.preserves_plus, rings.preserves_1. 
  rewrite IHx. reflexivity.
Qed.

(* [nat] is indeed a model of the naturals *)
Instance: Naturals nat.

(* Order *)
Instance: Order nat := le.

Instance: SemiRingOrder le.
Proof with trivial.
  repeat (split; try apply _).
     intros x y E. apply Le.le_antisym...
    intros E.
    assert (y ≡ x + (y - x))%nat as F. apply le_plus_minus...
    exists (y - x)%nat. split...
    apply plus_le_reg_l with x.
    rewrite <-F... rewrite Plus.plus_0_r...
   intros [z [Ez1 Ez2]].
   rewrite Ez2. apply le_plus_trans...
  intros x E1 y E2.
  change (0 * 0 <= x * y)%nat. apply mult_le_compat...
Qed.

Instance: TotalOrder le.
Proof. intros x y. destruct (le_ge_dec x y); intuition. Qed.

Instance le_nat_dec: Decision (x ≤ y) := le_dec.

(* Misc *)
Program Instance: CutMinus nat := λ x y, minus x y.
Next Obligation with trivial.
  split; intros E.
   symmetry. rewrite commutativity.
   apply le_plus_minus, orders.sprecedes_weaken...
  apply orders.sprecedes_precedes in E. destruct E as [E|E].
   rewrite E. apply minus_diag.
  apply not_le_minus_0. apply orders.not_precedes_sprecedes...
Qed.

(* Two simple omissions in the standard library that we prove for nats and then
 lift to arbitrary Naturals in theory.naturals: *)
Lemma Mult_mult_reg_l: ∀ n m p: nat, ~ p = 0 → mult p n = mult p m → n = m.
Proof.
 destruct p. intuition.
 intros E F. apply Le.le_antisym; apply Mult.mult_S_le_reg_l with p; rewrite F; constructor.
Qed.

Lemma Mult_nz_mult_nz (x y: nat): ~ y = 0 → ~ x = 0 → ~ y * x = 0.
Proof. intros A B C. destruct (Mult.mult_is_O y x C); intuition. Qed.
