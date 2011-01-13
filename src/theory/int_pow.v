(* Require
  theory.naturals orders.semiring theory.integers theory.fields.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.nat_pow.

(* * Properties of Int Pow *)
Section int_pow_properties.
  Context `{Field A} 
    `{!LeftCancellation (=) (λ x, x ≠ 0) ring_mult}
    `{∀ x y, Decision (x = y)}
    `{Integers B}
    `{!RingMinus B}.

  Add Ring A: (rings.stdlib_semiring_theory A).
  Add Ring B: (rings.stdlib_ring_theory B).

  Context `{ip : !IntPow A B}.
  Global Instance: Proper ((=) ==> (=) ==> (=)) (^).
  Proof with eauto.
    intros x1 y1 E1 x2 y2 E2. 
    unfold pow, int_pow, int_pow_sig. 
    destruct ip as [z1 [F1 G1]], ip as [z2 [F2 G2]]. simpl.
    destruct (orders.precedes_or_precedes_neq 0 x2).
     eapply nat_pow_spec_unique...
     eapply nat_pow_spec_proper... reflexivity. 
     apply F2. rewrite <-E2...
    apply fields.dec_mult_inv_inj.
    eapply nat_pow_spec_unique...
    eapply nat_pow_spec_proper... apply inv_proper... 
    reflexivity.
    apply G2. rewrite <-E2...
  Qed.

  Lemma int_pow_0 x : x ^ (0:B) = 1.
  Proof with eauto.
    unfold pow, int_pow, int_pow_sig. destruct ip as [z [Fz Gz]]. simpl.
    eapply nat_pow_spec_unique. 
    apply Fz. reflexivity.
    apply nat_pow_spec_0.
  Qed.

  Lemma int_pow_S_pos (x : A) (n : B) : 0 ≤ n → x ^ (1+n) = x * x ^ n.
  Proof with eauto.
    intros E.
    unfold pow, int_pow, int_pow_sig. 
    destruct ip as [z1 [F1 G1]], ip as [z2 [F2 G2]]. simpl.
    eapply nat_pow_spec_unique. 
    apply F1. apply semiring.sr_precedes_nonneg_plus_compat...
     apply semiring.sr_precedes_0_1...
    apply nat_pow_spec_S...
  Qed.
  
  Lemma int_pow_S_neg (x : A) (n : B) : x ≠ 0 → n < 0 → x ^ (1+n) = x * x ^ n.
  Proof with eauto.
    intros E1 E2.
    unfold pow, int_pow, int_pow_sig. 
    destruct ip as [z1 [F1 G1]], ip as [z2 [F2 G2]]. simpl.
    apply fields.dec_mult_inv_inj.
    eapply nat_pow_spec_unique.
     apply G1. admit.
    assert (-(1 + n) = 1 + -(1) + -(n + 1)) as E2 by ring. (* rewrite hangs... *)
    eapply nat_pow_spec_proper.  reflexivity. apply E2.
     rewrite fields.dec_mult_inv_distr, fields.dec_mult_inv_involutive. reflexivity.
    apply nat_pow_spec_S.
    apply G2.
    admit.
  Qed.

  Instance: RightIdentity (^) (1:B).
  Proof. 
    intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
    rewrite int_pow_S_pos, int_pow_0. ring.
    reflexivity.
  Qed.

  Instance: LeftAbsorb (pow (B:=B)) (1 : A).
  Proof with auto. 
    intro. 
    pattern y. apply integers.induction; clear y.
       intros ? ? E. rewrite E. tauto.
      apply int_pow_0.
     intros n E F.
     rewrite int_pow_S_pos... rewrite F. ring.
    intros n E F. admit. (*rewrite int_pow_S_neg in F... ring_simplify in F... *)
  Qed.

  Lemma int_pow_zero (x: B) : x ≠ 0 → 0 ^ x = 0.
  Proof with eauto.
    pattern x. apply integers.induction; clear x.
       intros ? ? E. rewrite E. tauto.
      intro E. destruct E. reflexivity.
     intros x E F G. rewrite int_pow_S_pos... ring.
    intros x E F G. admit. (* rewrite <-rings.mult_1_l. rewrite <-int_pow_S_neg... ring. *)
  Qed. 

  Lemma int_pow_exp_sum (x y: B) (n: A) : 
    n ^ (x + y) = n ^ x * n ^ y.
  Proof with auto.
    pattern x. apply integers.induction; clear x.
      intros ? ? E. rewrite E. tauto.
     rewrite int_pow_0, left_identity. ring.
    intros ? ? E. 
     rewrite <-associativity.
     rewrite int_pow_S_pos. rewrite int_pow_S_pos. rewrite E. ring.
    destruct (decide (n = 0)) as [F|F].
    rewrite <-associativity in E.
    do 2 rewrite int_pow_S in E. 
    apply (left_cancellation ring_mult n).
  Qed.
  
  Context `{!NoZeroDivisors A} `{!ZeroNeOne A}.

  Lemma nat_pow_nonzero (x: B) (n: A) : n ≠ 0 → n ^ x ≠ 0.
  Proof with eauto.
    pattern x. apply naturals.induction; clear x.
    intros x1 x2 E. rewrite E. tauto.
    intros. rewrite nat_pow_0. apply not_symmetry. apply zero_ne_one.
    intros x E F G. rewrite nat_pow_S in G.
    apply (no_zero_divisors n); split... 
  Qed. 
End nat_pow_properties.

(* Very slow default implementation by translation into Peano *)
Section int_pow_default.
  Context `{Field A} 
    `{!LeftCancellation (=) (λ x, x ≠ 0) ring_mult}
    `{∀ x y, Decision (x = y)}
    `{Integers B}.
  
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
  Global Program Instance: NatPow A B | 10 := nat_pow_default.
  Next Obligation with simpl; try reflexivity.
    apply nat_pow_spec_from_properties; unfold nat_pow_default.
    intros ? ? E ? ? F. rewrite E, F...
    intros. rewrite rings.preserves_0...
    intros. rewrite rings.preserves_plus, rings.preserves_1, <-peano_naturals.S_nat_1_plus...
  Qed.
End nat_pow_default.
*)