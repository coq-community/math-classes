Require
  theory.naturals orders.semirings orders.integers orders.fields.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.nat_pow theory.int_abs.

(* * Properties of Int Pow *)
Section int_pow_properties.
Context `{Field A} `{∀ x y, Decision (x = y)} `{!DecMultInv A}
  `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB} `{!IntPowSpec A B ipw}.

Add Ring A : (rings.stdlib_ring_theory A).
Add Ring B : (rings.stdlib_ring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) (^) | 1.
Proof. apply int_pow_proper. Qed.

Lemma int_pow_S_nonneg (x : A) (n : B) : 0 ≤ n → x ^ (1+n) = x * x ^ n.
Proof.
  intros E1.
  destruct (decide (x = 0)) as [Ex|Ex].
   rewrite Ex. rewrite int_pow_base_0. ring.
   intros E2. destruct semirings.not_precedes_1_0. 
   rewrite <-E2. now apply semirings.nonneg_plus_compat_r.
  now rewrite int_pow_S.
Qed.

Lemma int_pow_mult_inv (x : A) (n : B) : x ^ (-n) = /(x ^ n).
Proof with auto; try reflexivity.
  pattern n. apply integers.induction; clear n.
     solve_proper.
    now rewrite rings.opp_0, int_pow_0, fields.dec_mult_inv_1.
   intros n E1 E2.
   rewrite int_pow_S_nonneg, fields.dec_mult_inv_distr, <-E2...
   destruct (decide (x = 0)) as [E3|E3].
    rewrite E3, int_pow_base_0, fields.dec_mult_inv_0. ring.
    rewrite commutativity. apply rings.flip_opp_nonzero. apply not_symmetry.
    apply integers.precedes_sprecedes in E1. now destruct E1.
   apply (rings.left_cancellation_ne_0 (.*.) x)...
   rewrite <-int_pow_S...
   setoid_replace (1 - (1 + n)) with (-n) by ring.
   rewrite associativity, fields.dec_mult_inverse... ring.
  intros n E1 E2.
  setoid_replace (-(n - 1)) with (1 + -n) by ring.
  rewrite int_pow_S_nonneg, E2...
   destruct (decide (x = 0)) as [E3|E3].
    rewrite E3, left_absorb.
    rewrite int_pow_base_0, fields.dec_mult_inv_0...
    intros E4. destruct semirings.not_precedes_1_0. 
    apply rings.flip_nonpos_inv.
    apply (order_preserving_back (n +)). 
    rewrite E4. now ring_simplify.
   apply (rings.left_cancellation_ne_0 (.*.) (/x))...
    now apply fields.dec_mult_inv_nonzero.
   rewrite <-fields.dec_mult_inv_distr, <-int_pow_S...
   setoid_replace (1 + (n - 1)) with n by ring.
   rewrite associativity, (commutativity (/x)), fields.dec_mult_inverse... ring.
  now apply rings.flip_nonpos_inv.
Qed.

Lemma int_pow_mult_inv_alt (x : A) (n : B) : x ^ n = /(x ^ (-n)).
Proof.
  rewrite <-int_pow_mult_inv.
  now rewrite rings.inv_involutive.
Qed.

Lemma int_pow_nat_pow `{Naturals N} `{!NatPowSpec A N pw} {f : N → B} `{!SemiRing_Morphism f} (x : A) (n : N) :
  x ^ (f n) = x ^ n.
Proof.
  revert n. apply naturals.induction.
    solve_proper.
   now rewrite rings.preserves_0, int_pow_0, nat_pow_0.
  intros n E.
  rewrite rings.preserves_plus, rings.preserves_1.
  rewrite int_pow_S_nonneg, nat_pow_S.
   now rewrite E.
  rewrite <-(rings.preserves_0 (f:=f)).
  apply (order_preserving _).
  now apply naturals.naturals_nonneg.
Qed.

Global Instance int_pow_1: RightIdentity (^) (1:B).
Proof. 
  intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
  rewrite int_pow_S_nonneg, int_pow_0. 
   ring.
  reflexivity.
Qed.

Global Instance Int_pow_of_1: LeftAbsorb (^) 1.
Proof with auto. 
  intro n. 
  pattern n. apply integers.induction; clear n.
     solve_proper.
    now apply int_pow_0.
   intros n E F.
   rewrite int_pow_S_nonneg... 
   rewrite F. ring.
  intros n E F. 
  setoid_replace n with (1 + (n - 1)) in F by ring.
  rewrite int_pow_S in F. 
   now ring_simplify in F.
  now apply (ne_zero 1).
Qed.

Lemma int_pow_exp_plus (n m : B) (x : A) : 
  x ≠ 0 → x ^ (n + m) = x ^ n * x ^ m.
Proof with auto.
  intros nonneg.
  pattern n. apply integers.induction; clear n.
     solve_proper.
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
     solve_proper.
    intro E. now destruct E.
   intros. rewrite int_pow_S_nonneg... ring.
  intros n ? ? ?. rewrite int_pow_mult_inv_alt.
  setoid_replace (-(n - 1)) with (1 - n) by ring.
  rewrite int_pow_S_nonneg. 
   rewrite left_absorb. apply fields.dec_mult_inv_0.
  now apply rings.flip_nonpos_inv.
Qed.

Lemma int_pow_nonzero (x : A) (n : B) : x ≠ 0 → x ^ n ≠ 0.
Proof with eauto.
  intros nonneg.
  pattern n. apply integers.induction; clear n.
     solve_proper.
    intros. rewrite int_pow_0. apply (ne_zero 1).
   intros n E1 ? E2. rewrite int_pow_S_nonneg in E2...
   apply (no_zero_divisors x); split...
  intros n ? E1 E2. apply E1.
  setoid_replace n with (1 + (n - 1)) by ring.
  rewrite int_pow_S, E2... ring. 
Qed. 

Context `{oA : Order A} `{!RingOrder oA} `{!TotalOrder oA}.

Lemma int_pow_pos (x : A) (n : B) : 0 < x → 0 < x ^ n.
Proof with auto.
  intros nonneg.
  pattern n. apply integers.induction; clear n.
     solve_proper.
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

Lemma int_pow_nonneg (x : A) (n : B) : 0 ≤ x → 0 ≤ x ^ n.
Proof with auto.
  intros E.
  apply orders.sprecedes_precedes in E.
  destruct E as [E|E].
   rewrite <-E.
   destruct (decide (n = 0)) as [E2|E2].
    rewrite E2.
    rewrite int_pow_0.
    apply semirings.precedes_0_1.
   now rewrite int_pow_of_0.
  now apply int_pow_pos.
Qed. 

Lemma int_pow_ge1 (x : A) (n : B) : 1 ≤ x → 0 ≤ n → 1 ≤ x ^ n.
Proof with auto using semirings.precedes_0_1.
  intros E1 E2.
  pattern n. apply integers.induction_nonneg...
    intros ? ? E. now rewrite E...
   now rewrite int_pow_0.
  intros ? E3 E4.
  rewrite int_pow_S.
   rewrite <-rings.mult_1_r.
   apply semirings.nonneg_mult_compat_both...
  apply not_symmetry, orders.neq_precedes_sprecedes.
  apply orders.sprecedes_trans_l with 1...
  now apply semirings.sprecedes_0_1.
Qed.

Lemma int_pow_exp_precedes (x : A) (n m : B) : 1 ≤ x → n ≤ m → x ^ n ≤ x ^ m.
Proof.
  intros ? E2.
  assert (0 < x) as [? ?]. 
   apply orders.sprecedes_trans_l with 1.
    now apply semirings.sprecedes_0_1.
   easy.
  apply srorder_plus in E2. destruct E2 as [z [E2a E2b]].
  rewrite E2b.
  rewrite int_pow_exp_plus.
   rewrite <-rings.mult_1_r.
   apply semirings.nonneg_mult_compat_both.
      now apply int_pow_nonneg.
     apply semirings.precedes_0_1.
    now ring_simplify.
   now apply int_pow_ge1.
   now apply not_symmetry.
Qed. 
End int_pow_properties.

Section preservation.
  Context 
    `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB}
    `{Field A1} `{∀ x y : A1, Decision (x = y)} `{!DecMultInv A1} `{!IntPowSpec A1 B ip1}
    `{Field A2} `{∀ x y : A2, Decision (x = y)} `{!DecMultInv A2} `{!IntPowSpec A2 B ip2}
    {f : A1 → A2} `{!OrderPreserving f} `{!SemiRing_Morphism f} `{!Injective f}.

  Add Ring B2 : (rings.stdlib_ring_theory B).

  Lemma preserves_int_pow x (n : B) : f (x ^ n) = (f x) ^ n.
  Proof with auto.
    revert n. apply integers.induction.
       solve_proper.
      rewrite int_pow_0, int_pow_0. now apply rings.preserves_1.
     intros n E F. 
     rewrite int_pow_S_nonneg, rings.preserves_mult, F...
     now rewrite int_pow_S_nonneg.
    intros n E F.
    destruct (decide (x = 0)) as [G|G].
     rewrite G. rewrite rings.preserves_0. 
     assert (n - 1 ≠ 0).
      apply orders.neq_precedes_sprecedes, integers.precedes_sprecedes_alt.
      ring_simplify...
     repeat rewrite int_pow_base_0...
     now apply rings.preserves_0.
    assert (f x ≠ 0). apply rings.injective_not_0...
    apply (rings.left_cancellation_ne_0 (.*.) (f x))...
    rewrite <-int_pow_S, <-rings.preserves_mult, <-int_pow_S...
    now setoid_replace (1 + (n - 1)) with n by ring.
  Qed.
End preservation.

(* Very slow default implementation by translation into Peano *)
Section int_pow_default.
  Context `{Field A} `{∀ x y, Decision (x = y)} `{!DecMultInv A}
    `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB}.

  Add Ring B3 : (rings.stdlib_ring_theory B).

  Global Instance int_pow_default: Pow A B | 10 := λ x n,
    match (decide (0 ≤ n)) with
    | left _ => x ^ int_abs B nat n
    | right _ => /(x ^ int_abs B nat n)
    end.

  Global Instance: IntPowSpec A B int_pow_default.
  Proof with try contradiction; auto using semirings.precedes_0_1.
    split; unfold pow, int_pow_default.
       intros ? ? E1 ? ? E2.
       now (case (decide _); case (decide _); rewrite E1, E2)...
      intros x. case (decide _); intros E.
      rewrite int_abs_0. 
       now apply nat_pow_0.
      now destruct E.
     intros n ?. case (decide _); intros E.
      now apply nat_pow_base_0, int_abs_nonzero.
     rewrite nat_pow_base_0. 
     apply fields.dec_mult_inv_0.
     now apply int_abs_nonzero.
    intros x n E. case (decide _); case (decide _); intros E1 E2.
       rewrite int_abs_nonneg_plus, int_abs_1...
       now rewrite nat_pow_S.
      setoid_replace n with (-(1):B).
       rewrite rings.plus_opp_r, int_abs_0, nat_pow_0. 
       rewrite int_abs_opp, int_abs_1, right_identity. 
       symmetry. now apply fields.dec_mult_inverse.
      apply (antisymmetry (≤)).
       apply orders.not_precedes_sprecedes in E1.
       apply integers.precedes_sprecedes_alt in E1. 
       apply (order_preserving_back (+1)).
       unfold flip. ring_simplify...
      apply (order_preserving_back (1+)). now rewrite rings.plus_opp_r.
     destruct E2. apply semirings.nonneg_plus_compat_l...
     rewrite <-int_abs_opp, <-(int_abs_opp n).
     setoid_replace (-n) with (1 - (1 + n)) by ring.
     rewrite (int_abs_nonneg_plus 1 (-(1 + n))), int_abs_1...
      rewrite nat_pow_S. 
      rewrite fields.dec_mult_inv_distr, associativity.
      now rewrite fields.dec_mult_inverse, left_identity...
     apply rings.flip_nonpos_inv.
     now apply orders.not_precedes_sprecedes.
  Qed.
End int_pow_default.
