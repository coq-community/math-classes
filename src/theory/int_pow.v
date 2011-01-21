Require
  theory.naturals orders.semirings orders.integers orders.fields.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.nat_pow theory.int_abs.

(* * Properties of Int Pow *)
Section int_pow_properties.
Context `{Field A} 
  `{∀ z, NeZero z → LeftCancellation (.*.) z}
  `{∀ x y, Decision (x = y)} `{!DecMultInv A}
  `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB}.

Add Ring A : (rings.stdlib_semiring_theory A).
Add Ring B : (rings.stdlib_ring_theory B).

Section int_pow_spec_from_properties.
  Context (f : A → B → A) {f_proper : Proper ((=) ==> (=) ==> (=)) f}
    ( f_0 : ∀x, f x 0 = 1 ) ( f_S : ∀ x n, 0 ≤ n → f x (1+n) = x * (f x n) ).

  Lemma int_pow_spec_from_properties_nonneg x n : 0 ≤ n → nat_pow_spec x n (f x n).
  Proof with auto; try reflexivity.
    intros E. pattern n. apply integers.induction_nonneg...
      intros a b F. 
      eapply nat_pow_spec_proper...
      rewrite F...
     eapply nat_pow_spec_proper... apply nat_pow_spec_0...
    intros. eapply nat_pow_spec_proper...
    eapply nat_pow_spec_S...
  Qed.

  Context ( f_inv : ∀ x n,  f x (-n) = /(f x n) ).
  Lemma int_pow_spec_from_properties x n : 
    (0 ≤ n → nat_pow_spec x n (f x n)) ∧ (n ≤ 0 → nat_pow_spec x (-n) (/ (f x n))).
  Proof with trivial.
    split.
     apply int_pow_spec_from_properties_nonneg.
    intros. eapply (nat_pow_spec_proper _ _ (reflexivity _) _ _ (reflexivity _)).
     symmetry...
    apply int_pow_spec_from_properties_nonneg.
    apply rings.flip_nonpos_inv...
  Qed.
End int_pow_spec_from_properties.

Context `{ip : !IntPow A B}.
Global Instance: Proper ((=) ==> (=) ==> (=)) (^).
Proof with eauto.
  intros x y E1 n m E2. 
  unfold pow, int_pow, int_pow_sig. 
  destruct ip as [z1 [Ez1 Fz1]], ip as [z2 [Ez2 Fz2]]. simpl.
  destruct (total_order 0 n).
   eapply nat_pow_spec_unique...
   eapply nat_pow_spec_proper... reflexivity.
   apply Ez2. rewrite <-E2...
  apply (injective (/)).
  eapply nat_pow_spec_unique...
  eapply nat_pow_spec_proper... apply inv_proper... 
  reflexivity.
  apply Fz2. rewrite <-E2...
Qed.

Lemma int_pow_0 x : x ^ (0:B) = 1.
Proof with eauto.
  unfold pow, int_pow, int_pow_sig. destruct ip as [z [Fz Gz]]. simpl.
  eapply nat_pow_spec_unique. 
  apply Fz. reflexivity.
  apply nat_pow_spec_0.
Qed.

Lemma int_pow_mult_inv (x : A) (n : B) : x ^(-n) = /(x ^ n).
Proof with auto.
  unfold pow, int_pow, int_pow_sig. 
  destruct (ip x n) as [z2 [Ez2 Fz2]]. destruct ip as [z1 [Ez1 Fz1]]. simpl.
  destruct (total_order 0 n).
   apply (injective (/)).
   eapply nat_pow_spec_unique.
    apply Fz1, rings.flip_nonneg_inv...
   eapply (nat_pow_spec_proper _ _ (reflexivity _)).
     apply rings.inv_involutive.
    apply fields.dec_mult_inv_involutive.
   apply Ez2...
  eapply nat_pow_spec_unique.
   apply Ez1, rings.flip_nonpos_inv...
  apply Fz2...
Qed.

Lemma int_pow_mult_inv_alt (x : A) (n : B) : x ^n = /(x ^ (-n)).
Proof.
  rewrite <-int_pow_mult_inv.
  rewrite rings.inv_involutive.
  reflexivity.
Qed.

Lemma int_pow_S_nonneg (x : A) (n : B) : 0 ≤ n → x ^ (1+n) = x * x ^ n.
Proof with eauto.
  intros E.
  unfold pow, int_pow, int_pow_sig. 
  destruct ip as [z1 [F1 G1]], ip as [z2 [F2 G2]]. simpl.
  eapply nat_pow_spec_unique. 
  apply F1. apply semirings.nonneg_plus_compat...
   apply semirings.precedes_0_1...
  apply nat_pow_spec_S...
Qed.

Lemma int_pow_S (x : A) (n : B) : x ≠ 0 →  x ^ (1+n) = x * x ^ n.
Proof with auto.
  intros E.
  destruct (orders.precedes_or_sprecedes 0 n).
   apply int_pow_S_nonneg...
   rewrite int_pow_mult_inv_alt, (int_pow_mult_inv_alt _ n).
  setoid_replace (-n) with (1 - (1 + n)) by ring.
  rewrite int_pow_S_nonneg.
  rewrite fields.dec_mult_inv_distr. rewrite associativity. 
  rewrite fields.dec_mult_inverse... ring.
  apply rings.flip_nonpos_inv...
  rewrite commutativity.
  apply integers.precedes_sprecedes_alt...
Qed.

Lemma int_pow_nat_pow `{Naturals N} `{!NatPow A N} (x : A) (n : N) :
  x ^ (naturals_to_semiring N B n) = x ^ n.
Proof.
  revert n. apply naturals.induction.
    intros ? ? E. rewrite E. reflexivity.
   rewrite rings.preserves_0, int_pow_0, nat_pow_0. reflexivity.
  intros n E.
  rewrite rings.preserves_plus, rings.preserves_1.
  rewrite int_pow_S_nonneg, nat_pow_S.
   rewrite E. reflexivity.
  apply naturals.to_semiring_nonneg.
Qed.

Instance: RightIdentity (^) (1:B).
Proof. 
  intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
  rewrite int_pow_S_nonneg, int_pow_0. ring.
  reflexivity.
Qed.

Instance: LeftAbsorb (pow (B:=B)) (1 : A).
Proof with auto. 
  intro n. 
  pattern n. apply integers.induction; clear n.
     intros ? ? E. rewrite E. tauto.
    apply int_pow_0.
   intros n E F.
   rewrite int_pow_S_nonneg... rewrite F. ring.
  intros n E F. 
  setoid_replace n with (1 + (n - 1)) in F by ring.
  rewrite int_pow_S in F. ring_simplify in F...
  apply (ne_zero 1).
Qed.

Lemma int_pow_exp_sum (n m: B) (x : A) : 
  x ≠ 0 → x ^ (n + m) = x ^ n * x ^ m.
Proof with auto.
  intros nonneg.
  pattern n. apply integers.induction; clear n.
     intros ? ? E. rewrite E. tauto.
    rewrite int_pow_0, left_identity. ring.
   intros ? ? E. 
   rewrite <-associativity.
   rewrite int_pow_S... rewrite E. rewrite int_pow_S... ring.
  intros ? ? E.
  apply (rings.left_cancellation_ne_0 (.*.) x)... rewrite associativity.
  rewrite <-int_pow_S... rewrite <-int_pow_S...
  setoid_replace (1 + (n - 1 + m)) with (n + m) by ring.
  setoid_replace (1 + (n - 1)) with n by ring...
Qed.

Lemma int_pow_of_0 (n : B) : n ≠ 0 → 0 ^ n = 0.
Proof with auto.
  pattern n. apply integers.induction; clear n.
     intros ? ? E. rewrite E. tauto.
    intro E. destruct E. reflexivity.
   intros. rewrite int_pow_S_nonneg... ring.
  intros n ? ? ?. rewrite int_pow_mult_inv_alt.
  setoid_replace (-(n - 1)) with (1 - n) by ring.
  rewrite int_pow_S_nonneg. 
   rewrite left_absorb. apply fields.dec_mult_inv_0.
  apply rings.flip_nonpos_inv...
Qed.

Lemma int_pow_nonzero (x : A) (n : B) : x ≠ 0 → x ^ n ≠ 0.
Proof with eauto.
  intros nonneg.
  pattern n. apply integers.induction; clear n.
     intros x1 x2 E. rewrite E. reflexivity.
    intros. rewrite int_pow_0. apply (ne_zero 1).
   intros n E1 ? E2. rewrite int_pow_S_nonneg in E2...
   apply (no_zero_divisors x); split...
  intros n ? E1 E2. apply E1.
  setoid_replace n with (1 + (n - 1)) by ring.
  rewrite int_pow_S, E2... ring. 
Qed. 

Context `{oA : Order A} `{!RingOrder oA} `{!TotalOrder oA}.

Lemma int_pow_nonneg (x : A) (n : B) : 0 < x → 0 < x ^ n.
Proof with auto.
  intros nonneg.
  pattern n. apply integers.induction; clear n.
     intros x1 x2 E. rewrite E. reflexivity.
    intros. rewrite int_pow_0. apply semirings.sprecedes_0_1.
   intros n E1 E2. rewrite int_pow_S_nonneg...
   apply semirings.pos_mult_compat...
  intros n E1 E2.
  assert (GtZero x)...
  apply (maps.strictly_order_preserving_back (x *.)). unfold flip.
  rewrite <-int_pow_S.
   rewrite right_absorb. setoid_replace (1 + (n - 1)) with n by ring...
  apply not_symmetry. apply orders.neq_precedes_sprecedes...
Qed. 
End int_pow_properties.

Section preservation.
  Context 
    `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB}
    `{Field A1} `{∀ z : A1, NeZero z → LeftCancellation (.*.) z} `{∀ x y : A1, Decision (x = y)} `{!DecMultInv A1} `{!IntPow A1 B}
    `{Field A2} `{∀ z : A2, NeZero z → LeftCancellation (.*.) z} `{∀ x y : A2, Decision (x = y)} `{!DecMultInv A2} `{!IntPow A2 B}
    {f : A1 → A2} `{!OrderPreserving f} `{!SemiRing_Morphism f} `{!Injective f}.

  Add Ring B2 : (rings.stdlib_ring_theory B).

  Lemma preserves_int_pow x (n : B) : f (x ^ n) = (f x) ^ n.
  Proof with auto.
    revert n. apply integers.induction.
       intros ? ? E1. rewrite E1. reflexivity.
      rewrite int_pow_0, int_pow_0. apply rings.preserves_1.
     intros n E F. 
     rewrite int_pow_S_nonneg, rings.preserves_mult, F...
     rewrite int_pow_S_nonneg... reflexivity.
    intros n E F.
    destruct (decide (x = 0)) as [G | G].
     rewrite G. rewrite rings.preserves_0. 
     assert (n - 1 ≠ 0).
      apply orders.neq_precedes_sprecedes, integers.precedes_sprecedes_alt.
      ring_simplify...
     repeat rewrite int_pow_of_0...
     apply rings.preserves_0.
    assert (f x ≠ 0). apply rings.injective_not_0...
    apply (rings.left_cancellation_ne_0 (.*.) (f x))...
    rewrite <-int_pow_S, <-rings.preserves_mult, <-int_pow_S...
    setoid_replace (1 + (n - 1)) with n by ring...
  Qed.
End preservation.

(* Very slow default implementation by translation into Peano *)
Section int_pow_default.
  Context `{Field A} 
    `{∀ z, NeZero z → LeftCancellation (.*.) z}
    `{∀ x y, Decision (x = y)} `{!DecMultInv A}
    `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB}.

  Let int_pow_default (x : A) (n : B) : A := 
    match (decide (0 ≤ n)) with
    | left _ => x ^ (int_abs B nat n)
    | right _ => /(x ^ (int_abs B nat n))
    end.

  Global Program Instance: IntPow A B | 10 := int_pow_default.
  Next Obligation with try contradiction; auto using semirings.precedes_0_1.
    apply int_pow_spec_from_properties; unfold int_pow_default.
       admit.
      intros y.
      case (decide _); intros E.
       rewrite int_abs_0. apply nat_pow_0.
      destruct E. reflexivity.
     intros y m E.
     case (decide _); case (decide _); intros E1 E2...
      rewrite int_abs_nonneg_plus, int_abs_1...
      apply nat_pow_S.
     destruct E2. apply semirings.nonneg_plus_compat_l...
    intros y m.
    case (decide _); case (decide _); intros E1 E2...
       setoid_replace m with (0 : B).
        rewrite rings.opp_0, int_abs_0, nat_pow_0. symmetry. apply fields.dec_mult_inv_1.
       apply (antisymmetry (≤))... apply rings.flip_nonpos_inv...
      rewrite fields.dec_mult_inv_involutive, int_abs_opp. reflexivity.
     rewrite int_abs_opp. reflexivity.
    setoid_replace m with (0 : B).
     rewrite rings.opp_0, int_abs_0, nat_pow_0. rewrite fields.dec_mult_inv_1 at 2. reflexivity.
    apply (antisymmetry (≤)).
     apply orders.precedes_flip...
    apply rings.flip_nonneg_inv.
    apply orders.precedes_flip...
  Qed.
End int_pow_default.
