Require
  theory.naturals orders.semirings orders.integers orders.fields.
Require Import 
  Program Morphisms Setoid Ring Field
  abstract_algebra interfaces.naturals interfaces.integers interfaces.additional_operations
  theory.nat_pow theory.int_abs.

(* * Properties of Int Pow *)
Section int_pow_properties.
Context `{Field A} `{∀ x y, Decision (x = y)} `{!DecMultInv A}
  `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB} `{!IntPowSpec A B ipw}.

Add Field A : (fields.stdlib_field_theory A).
Add Ring B : (rings.stdlib_ring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) (^) | 0.
Proof. apply int_pow_proper. Qed.

Lemma int_pow_S_nonneg (x : A) (n : B) : 0 ≤ n → x ^ (1+n) = x * x ^ n.
Proof.
  intros En.
  destruct (decide (x = 0)) as [Ex | Ex].
   rewrite Ex. rewrite int_pow_base_0. ring.
   intros E. destruct semirings.not_precedes_1_0. 
   rewrite <-E. now apply semirings.nonneg_plus_compat_r.
  now rewrite int_pow_S.
Qed.

Lemma int_pow_opp (x : A) (n : B) : x ^ (-n) = /(x ^ n).
Proof.
  destruct (decide (x = 0)) as [Ex | Ex].
   rewrite Ex.
   destruct (decide (n = 0)) as [En | En].
    now rewrite En, rings.opp_0, int_pow_0, fields.dec_mult_inv_1.
   rewrite 2!int_pow_base_0; trivial.
    now rewrite fields.dec_mult_inv_0.
   now apply rings.flip_opp_nonzero.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now rewrite rings.opp_0, int_pow_0, fields.dec_mult_inv_1.
  intros n.
  setoid_replace (-n) with (1 - (1 + n)) by ring.
  rewrite 2!int_pow_S, fields.dec_mult_inv_distr; trivial.
  split; intros E.
   rewrite <-E. now field.
  rewrite E, associativity, fields.dec_mult_inverse; trivial.
  ring.
Qed.

Lemma int_pow_opp_alt (x : A) (n : B) : x ^ n = /(x ^ (-n)).
Proof.
  rewrite <-int_pow_opp.
  now rewrite rings.opp_involutive.
Qed.

Lemma int_pow_mult (x y : A) (n : B) : (x * y) ^ n = x ^ n * y ^ n.
Proof.
  destruct (decide (x * y = 0)) as [Exy | Exy].
   rewrite Exy.
   destruct (decide (n = 0)) as [En | En].
    rewrite En, 3!int_pow_0. ring.
   destruct (zero_product x y Exy) as [E|E]; rewrite E, int_pow_base_0; trivial; ring.
  revert n. apply integers.biinduction.
    solve_proper.
   rewrite 3!int_pow_0. ring.
  intros n.
  rewrite 3!int_pow_S; trivial.
    split; intros E.
     rewrite E. ring.
    apply (rings.left_cancellation_ne_0 (.*.) (x * y)); trivial.
    rewrite E. ring.
   intros E. apply Exy. rewrite E. ring.
  intros E. apply Exy. rewrite E. ring.
Qed.

Lemma int_pow_mult_inv (x : A) (n : B) : (/x) ^ n = /(x ^ n).
Proof.
  destruct (decide (x = 0)) as [Ex | Ex].
   rewrite Ex, fields.dec_mult_inv_0.
   destruct (decide (n = 0)) as [En | En].
    now rewrite En, int_pow_0, fields.dec_mult_inv_1.
   now rewrite int_pow_base_0, fields.dec_mult_inv_0.
  revert n. apply integers.biinduction.
    solve_proper.
   now rewrite 2!int_pow_0, fields.dec_mult_inv_1.
  intros n.
  assert (/x ≠ 0) by now apply fields.dec_mult_inv_nonzero.
  rewrite 2!int_pow_S, fields.dec_mult_inv_distr; trivial.
  split; intros E.
   now rewrite E.
  now apply (rings.left_cancellation_ne_0 (.*.) (/x)).
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

Global Instance int_pow_base_1: LeftAbsorb (^) 1.
Proof. 
  intro n. pattern n. apply integers.biinduction; clear n.
    solve_proper.
   now apply int_pow_0.
  intros n. rewrite int_pow_S, left_identity.
   easy.
  now apply (rings.ne_0 1).
Qed.

Lemma int_pow_exp_plus (n m : B) (x : A) : 
  x ≠ 0 → x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros nonneg.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   rewrite int_pow_0, left_identity. ring.
  intros n. rewrite <-associativity, 2!int_pow_S; trivial.
  split; intros E.
   rewrite E. ring.
  apply (rings.left_cancellation_ne_0 (.*.) x); trivial.
  rewrite E. ring.
Qed.

Global Instance int_pow_nonzero (x : A) (n : B) : PropHolds (x ≠ 0) → PropHolds (x ^ n ≠ 0).
Proof with eauto.
  intros nonneg. unfold PropHolds.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   rewrite int_pow_0. apply (rings.ne_0 1).
  intros n. rewrite int_pow_S; trivial.
  split; intros E1 E2; destruct E1.
   apply (left_cancellation (.*.) x).
   now rewrite right_absorb.
  rewrite E2. ring.
Qed. 

Lemma int_pow_exp_mult (x : A) (n m : B) : 
  x ^ (n * m) = (x ^ n) ^ m.
Proof.
  destruct (decide (x = 0)) as [Ex|Ex].
   rewrite Ex.
   destruct (decide (n = 0)) as [En|En].
    rewrite En, left_absorb, int_pow_0. 
    now rewrite left_absorb.
   destruct (decide (m = 0)) as [Em|Em].
    now rewrite Em, right_absorb, 2!int_pow_0.
   rewrite 3!int_pow_base_0; try easy.
   intros E. now destruct (zero_product n m E).
  pattern m. apply integers.biinduction; clear m.
    solve_proper.
   rewrite right_absorb. now rewrite 2!int_pow_0.
  intros m. split; intros E.
   rewrite int_pow_S, <-E.
    rewrite distribute_l, right_identity.
    now rewrite int_pow_exp_plus.
   now apply int_pow_nonzero.
  rewrite int_pow_S in E.
  rewrite distribute_l, right_identity, int_pow_exp_plus in E.
    apply (rings.left_cancellation_ne_0 (.*.) (x ^ n)).
     now apply int_pow_nonzero.
    now rewrite E.
   easy.
  now apply int_pow_nonzero.
Qed.

Context `{oA : Order A} `{!RingOrder oA} `{!TotalOrder oA}.

Global Instance int_pow_pos (x : A) (n : B) : PropHolds (0 < x) → PropHolds (0 < x ^ n).
Proof.
   intros nonneg. unfold PropHolds.
  pattern n. apply integers.biinduction; clear n.
    solve_proper.
   intros. rewrite int_pow_0. apply semirings.sprecedes_0_1.
  intros n; split; intros E.
   rewrite int_pow_S.
    now apply semirings.pos_mult_scompat.
   apply not_symmetry. now apply orders.neq_precedes_sprecedes.
  apply (maps.strictly_order_preserving_back (x *.)).
  rewrite <-int_pow_S.
   now rewrite right_absorb.
  apply not_symmetry. now apply orders.neq_precedes_sprecedes.
Qed. 

Global Instance int_pow_nonneg (x : A) (n : B) : PropHolds (0 ≤ x) → PropHolds (0 ≤ x ^ n).
Proof.
  intros E.
  apply orders.sprecedes_precedes in E.
  destruct E as [E|E].
   rewrite <-E.
   destruct (decide (n = 0)) as [En|En].
    rewrite En.
    rewrite int_pow_0.
    apply semirings.precedes_0_1.
   unfold PropHolds. now rewrite int_pow_base_0.
  now apply int_pow_pos.
Qed. 

Lemma int_pow_ge1 (x : A) (n : B) : 1 ≤ x → 0 ≤ n → 1 ≤ x ^ n.
Proof.
  intros. pattern n. apply integers.induction_nonneg; trivial.
    solve_proper.
   now rewrite int_pow_0.
  intros.
  rewrite int_pow_S.
   rewrite <-rings.mult_1_r.
   apply semirings.mult_compat; try apply semirings.precedes_0_1; auto.
  apply not_symmetry, orders.neq_precedes_sprecedes.
  apply orders.sprecedes_trans_l with 1; trivial.
  now apply semirings.sprecedes_0_1.
Qed.

Lemma int_pow_gt1 (x : A) (n : B) : 1 < x → 0 < n → 1 < x ^ n.
Proof.
  intros Ex En.
  apply integers.precedes_sprecedes_alt in En.
  apply srorder_plus in En. destruct En as [z [Ez1 Ez2]]. ring_simplify in Ez2.
  rewrite Ez2.
  pattern z. apply integers.induction_nonneg; try assumption.
    solve_proper.
   now rewrite left_identity, right_identity.
  intros.
  rewrite <-associativity, int_pow_S.
   apply semirings.gt1_mult_scompat_l; firstorder.
  apply not_symmetry, orders.neq_precedes_sprecedes.
  apply orders.sprecedes_trans_r with 1; trivial.
  now apply semirings.precedes_0_1.
Qed.

Lemma int_pow_exp_precedes (x : A) (n m : B) : 
  1 ≤ x → n ≤ m → x ^ n ≤ x ^ m.
Proof.
  intros ? E.
  assert (0 < x) as [? ?]. 
   apply orders.sprecedes_trans_l with 1.
    now apply semirings.sprecedes_0_1.
   easy.
  apply srorder_plus in E. destruct E as [z [Ea Eb]].
  rewrite Eb.
  rewrite int_pow_exp_plus.
   rewrite <-rings.mult_1_r.
   apply semirings.mult_compat.
      now apply int_pow_nonneg.
     apply semirings.precedes_0_1.
    now ring_simplify.
   now apply int_pow_ge1.
  now apply not_symmetry.
Qed.

Lemma int_pow_exp_sprecedes (x : A) (n m : B) : 
  1 < x → n < m → x ^ n < x ^ m.
Proof.
  intros E1 E2.
  apply integers.precedes_sprecedes_alt in E2.
  apply srorder_plus in E2. destruct E2 as [z [Ea Eb]].
  rewrite Eb.
  rewrite <-associativity, int_pow_exp_plus.
   rewrite <-(rings.mult_1_r (x ^ n)) at 1.
   assert (PropHolds (0 < x ^ n)).
    apply int_pow_pos. red. transitivity 1; trivial. apply semirings.sprecedes_0_1.
   apply (strictly_order_preserving (x^n *.)).
   apply int_pow_gt1; trivial.
   apply integers.precedes_sprecedes_alt.
   rewrite commutativity. now apply (order_preserving (1+)).
  apply not_symmetry, orders.sprecedes_trans_r with 1; trivial.
  now apply semirings.precedes_0_1.
Qed.

Lemma int_pow_exp_precedes_back (x : A) (n m : B) : 
  1 < x → x ^ n ≤ x ^ m → n ≤ m.
Proof.
  intros ? E1.
  destruct (total_order n m) as [E2|E2]; trivial. 
  apply orders.sprecedes_precedes in E2. destruct E2 as [E2|E2].
   now rewrite E2.
  contradict E1.
  apply orders.not_precedes_sprecedes.
  now apply int_pow_exp_sprecedes.
Qed.

Lemma int_pow_exp_sprecedes_back (x : A) (n m : B) : 
  1 < x → x ^ n < x ^ m → n < m.
Proof.
  intros ? E1.
  destruct (orders.precedes_or_sprecedes m n) as [E2|E2]; trivial.
  contradict E1.
  apply orders.not_sprecedes_precedes. 
  apply int_pow_exp_precedes; firstorder.
Qed.

Lemma int_pow_inj (x : A) (n m : B) : 
  1 < x → x ^ n = x ^ m → n = m.
Proof.
  intros ? E.
  apply (antisymmetry (≤)); apply int_pow_exp_precedes_back with x; trivial; rewrite E; reflexivity.
Qed.
End int_pow_properties.

Section preservation.
  Context 
    `{Integers B}
    `{Field A1} `{∀ x y : A1, Decision (x = y)} `{!DecMultInv A1} `{!IntPowSpec A1 B ip1}
    `{Field A2} `{∀ x y : A2, Decision (x = y)} `{!DecMultInv A2} `{!IntPowSpec A2 B ip2}
    {f : A1 → A2} `{!SemiRing_Morphism f} `{!Injective f}.

  Add Ring B2 : (rings.stdlib_ring_theory B).

  Lemma preserves_int_pow x (n : B) : f (x ^ n) = (f x) ^ n.
  Proof.
    destruct (decide (x = 0)) as [Ex | Ex].
     rewrite Ex, rings.preserves_0.
     destruct (decide (n = 0)) as [En|En].
      rewrite En, 2!int_pow_0.
      now apply rings.preserves_1.
     rewrite 2!int_pow_base_0; trivial.
     now apply rings.preserves_0.
    revert n. apply integers.biinduction.
      solve_proper.
     rewrite int_pow_0, int_pow_0. 
     now apply rings.preserves_1.
    intros n. 
    assert (PropHolds (f x ≠ 0)) by now apply rings.injective_ne_0.
    rewrite 2!int_pow_S, rings.preserves_mult; trivial.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) (f x)).
  Qed.
End preservation.

Section exp_preservation.
  Context `{Field A} `{∀ x y : A, Decision (x = y)} `{!DecMultInv A}
   `{Integers B1} `{Integers B2} `{!IntPowSpec A B1 pw1} `{!IntPowSpec A B2 pw2} 
    {f : B1 → B2} `{!SemiRing_Morphism f}.

  Lemma preserves_int_pow_exp x (n : B1) : x ^ (f n) = x ^ n.
  Proof.
    destruct (decide (x = 0)) as [Ex | Ex].
     rewrite Ex.
     destruct (decide (n = 0)) as [En|En].
      now rewrite En, rings.preserves_0, 2!int_pow_0.
     rewrite 2!int_pow_base_0; try easy.
     now apply rings.injective_ne_0.
    revert n. apply integers.biinduction.
      solve_proper.
     rewrite rings.preserves_0.
     now rewrite 2!int_pow_0.
    intros n.
    rewrite rings.preserves_plus, rings.preserves_1.
    rewrite 2!int_pow_S by trivial.
    split; intros E.
     now rewrite E.
    now apply (rings.left_cancellation_ne_0 (.*.) x).
  Qed.
End exp_preservation.

(* Very slow default implementation by translation into Peano *)
Section int_pow_default.
  Context `{Field A} `{∀ x y, Decision (x = y)} `{!DecMultInv A}
    `{Integers B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB}.

  Add Ring B3 : (rings.stdlib_ring_theory B).

  Global Instance int_pow_default: Pow A B | 10 := λ x n,
    match (decide_rel (≤) 0 n) with
    | left _ => x ^ int_abs B nat n
    | right _ => /x ^ int_abs B nat n
    end.

  Global Instance: IntPowSpec A B int_pow_default.
  Proof.
    split; unfold pow, int_pow_default.
       intros ? ? E1 ? ? E2.
       now (case (decide_rel _); case (decide_rel _); rewrite E1, E2).
      intros x. case (decide_rel _); intros E.
       now rewrite int_abs_0. 
      now destruct E.
     intros n ?. case (decide_rel _); intros E.
      now apply nat_pow_base_0, int_abs_nonzero.
     rewrite nat_pow_base_0. 
     apply fields.dec_mult_inv_0.
     now apply int_abs_nonzero.
    intros x n E. case (decide_rel _); case (decide_rel _); intros E1 E2.
       rewrite int_abs_nonneg_plus, int_abs_1.
         reflexivity.
        apply (rings.ge_0 1).
       easy.
      setoid_replace n with (-1 : B).
       rewrite rings.plus_opp_r, int_abs_0, nat_pow_0. 
       rewrite int_abs_opp, int_abs_1, right_identity. 
       symmetry. now apply fields.dec_mult_inverse.
      apply (antisymmetry (≤)).
       apply orders.not_precedes_sprecedes in E1.
       apply integers.precedes_sprecedes_alt in E1. 
       apply (order_preserving_back (+1)).
       now ring_simplify.
      apply (order_preserving_back (1+)). now rewrite rings.plus_opp_r.
     destruct E2. apply semirings.nonneg_plus_compat_l.
       apply (rings.ge_0 1).
      easy.
     rewrite <-int_abs_opp, <-(int_abs_opp n).
     setoid_replace (-n) with (1 - (1 + n)) by ring.
     rewrite (int_abs_nonneg_plus 1 (-(1 + n))), int_abs_1.
       rewrite nat_pow_S. 
       rewrite fields.dec_mult_inv_distr, associativity.
       now rewrite fields.dec_mult_inverse, left_identity.
      apply (rings.ge_0 1).
     apply rings.flip_nonpos_opp.
     now apply orders.not_precedes_sprecedes.
  Qed.
End int_pow_default.
