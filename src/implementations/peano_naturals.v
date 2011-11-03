Require
  ua_homomorphisms.
Require Import
  Morphisms Ring Arith_base
  abstract_algebra interfaces.naturals theory.categories
  interfaces.additional_operations interfaces.orders orders.semirings.

Instance nat_equiv: Equiv nat := eq.
Instance nat_plus: Plus nat := Peano.plus.
Instance nat_0: Zero nat := 0%nat.
Instance nat_1: One nat := 1%nat.
Instance nat_mult: Mult nat := Peano.mult.

Instance: SemiRing nat.
Proof.
  repeat (split; try apply _); repeat intro.
         now apply plus_assoc.
        now apply plus_0_r.
       now apply plus_comm.
      now apply mult_assoc.
     now apply mult_1_l.
    now apply mult_1_r.
   now apply mult_comm.
  now apply mult_plus_distr_l.
Qed.

(* misc *)
Instance: Injective S.
Proof. repeat (split; try apply _). intros ?? E. now injection E. Qed.

Global Instance nat_dec: ∀ x y: nat, Decision (x = y) := eq_nat_dec.

Add Ring nat: (rings.stdlib_semiring_theory nat).

Close Scope nat_scope.

Instance: NaturalsToSemiRing nat :=
  λ _ _ _ _ _, fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Section for_another_semiring.
  Context `{SemiRing R}.

  Notation toR := (naturals_to_semiring nat R).

  Add Ring R: (rings.stdlib_semiring_theory R).

  Instance: Proper ((=) ==> (=)) toR.
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
End for_another_semiring.

Lemma O_nat_0 : O ≡ 0.
Proof. reflexivity. Qed.

Lemma S_nat_plus_1 x : S x ≡ x + 1.
Proof. rewrite commutativity. reflexivity. Qed.

Lemma S_nat_1_plus x : S x ≡ 1 + x.
Proof. reflexivity. Qed.

Lemma nat_induction (P : nat → Prop) :
  P 0 → (∀ n, P n → P (1 + n)) → ∀ n, P n.
Proof nat_ind P.

Instance: Initial (semirings.object nat).
Proof.
  intros. apply natural_initial. intros.
  intros x y E. unfold equiv, nat_equiv in E. subst y. induction x.
  replace 0%nat with (zero:nat) by reflexivity.
  rewrite 2!rings.preserves_0. reflexivity.
  rewrite S_nat_1_plus.
  rewrite 2!rings.preserves_plus, 2!rings.preserves_1.
  now rewrite IHx.
Qed.

(* [nat] is indeed a model of the naturals *)
Instance: Naturals nat := {}.

(* Misc *)
Instance: NoZeroDivisors nat.
Proof. intros x [Ex [y [Ey1 Ey2]]]. destruct (Mult.mult_is_O x y Ey2); intuition. Qed.

Instance: ∀ z : nat, PropHolds (z ≠ 0) → LeftCancellation (.*.) z.
Proof. intros z Ez x y. now apply NPeano.Nat.mul_cancel_l. Qed.

(* Order *)
Instance nat_le: Le nat := Peano.le.
Instance nat_lt: Lt nat := Peano.lt.

Instance: FullPseudoSemiRingOrder nat_le nat_lt.
Proof.
  assert (TotalRelation nat_le).
   intros x y. now destruct (le_ge_dec x y); intuition.
  assert (PartialOrder nat_le).
   split; try apply _. intros x y E. now apply Le.le_antisym.
  assert (SemiRingOrder nat_le).
   repeat (split; try apply _).
      intros x y E. exists (y - x)%nat. now apply le_plus_minus.
     intros. now apply Plus.plus_le_compat_l.
    intros. now apply plus_le_reg_l with z.
   intros x y ? ?. change (0 * 0 <= x * y)%nat. now apply Mult.mult_le_compat.
  apply dec_full_pseudo_srorder.
  now apply NPeano.Nat.le_neq.
Qed.

Instance: OrderEmbedding S.
Proof. repeat (split; try apply _). exact le_n_S. exact le_S_n. Qed.

Instance: StrictOrderEmbedding S.
Proof. split; try apply _. Qed.

Instance nat_le_dec: Decision (x ≤ y) := le_dec.

Instance nat_cut_minus: CutMinus nat := minus.
Instance: CutMinusSpec nat nat_cut_minus.
Proof.
  split.
   symmetry. rewrite commutativity.
   now apply le_plus_minus.
  intros x y E. destruct (orders.le_equiv_lt x y E) as [E2|E2].
   rewrite E2. now apply minus_diag.
  apply not_le_minus_0. now apply orders.lt_not_le_flip.
Qed.
