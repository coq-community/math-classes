Require
  MathClasses.theory.naturals MathClasses.orders.semirings MathClasses.orders.integers MathClasses.orders.dec_fields.
Require Import
  Coq.setoid_ring.Ring Coq.setoid_ring.Field
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.integers
  MathClasses.interfaces.additional_operations MathClasses.interfaces.orders
  MathClasses.theory.nat_pow MathClasses.theory.int_abs MathClasses.theory.dec_fields.

(* * Properties of Int Pow *)
Section int_pow_properties.
Context `{DecField A} `{∀ x y, Decision (x = y)} `{Integers B} `{!IntPowSpec A B ipw}.

Add Field A : (dec_fields.stdlib_field_theory A).
Add Ring B : (rings.stdlib_ring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) ((^) : A → B → A) | 0.
Proof int_pow_proper.

Global Instance int_pow_mor_1: ∀ x : A, Setoid_Morphism (x^) | 0.
Proof. split; try apply _. Qed.

Global Instance int_pow_mor_2: ∀ n : B, Setoid_Morphism (^n) | 0.
Proof. split; try apply _. solve_proper. Qed.

Lemma int_pow_S_nonneg `{Apart B} `{!TrivialApart B} `{!FullPseudoSemiRingOrder (A:=B) Ble Blt} (x : A) (n : B) :
  0 ≤ n → x ^ (1+n) = x * x ^ n.
Proof.
  intros En. destruct (decide (x = 0)) as [Ex | Ex].
   rewrite Ex. rewrite int_pow_base_0. ring.
   intros E. destruct semirings.not_le_1_0.
   rewrite <-E. now apply semirings.nonneg_plus_le_compat_r.
  now rewrite int_pow_S.
Qed.

Lemma int_pow_negate (x : A) (n : B) : x ^ (-n) = /(x ^ n).
Proof.
  destruct (decide (x = 0)) as [Ex | Ex].
   rewrite Ex.
   destruct (decide (n = 0)) as [En | En].
    now rewrite En, rings.negate_0, int_pow_0, dec_recip_1.
   rewrite 2!int_pow_base_0; trivial.
    now rewrite dec_recip_0.
   now apply rings.flip_negate_ne_0.
  revert n. apply biinduction. 
    solve_proper.
   now rewrite rings.negate_0, int_pow_0, dec_recip_1.
  intros n.
  setoid_replace (-n) with (1 - (1 + n)) by ring.
  rewrite 2!int_pow_S, dec_recip_distr; trivial.
  split; intros E.
   rewrite <-E. now field.
  rewrite E, associativity, dec_recip_inverse; trivial.
  ring.
Qed.

Lemma int_pow_negate_alt (x : A) (n : B) : x ^ n = /(x ^ (-n)).
Proof.
  rewrite <-int_pow_negate.
  now rewrite rings.negate_involutive.
Qed.

Lemma int_pow_mult (x y : A) (n : B) : (x * y) ^ n = x ^ n * y ^ n.
Proof.
  destruct (decide (x * y = 0)) as [Exy | Exy].
   rewrite Exy.
   destruct (decide (n = 0)) as [En | En].
    rewrite En, 3!int_pow_0. ring.
   destruct (zero_product x y Exy) as [E|E]; rewrite E, int_pow_base_0; trivial; ring.
  revert n. apply biinduction. 
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

Lemma int_pow_recip (x : A) (n : B) : (/x) ^ n = /(x ^ n).
Proof.
  destruct (decide (x = 0)) as [Ex | Ex].
   rewrite Ex, dec_recip_0.
   destruct (decide (n = 0)) as [En | En].
    now rewrite En, int_pow_0, dec_recip_1.
   now rewrite int_pow_base_0, dec_recip_0.
  revert n. apply biinduction.
    solve_proper.
   now rewrite 2!int_pow_0, dec_recip_1.
  intros n.
  assert (/x ≠ 0) by now apply dec_recip_ne_0.
  rewrite 2!int_pow_S, dec_recip_distr; trivial.
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
  apply semirings.preserves_nonneg.
  now apply naturals.nat_nonneg.
Qed.

Global Instance int_pow_1: RightIdentity (^) (1:B).
Proof.
  intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
  rewrite int_pow_S_nonneg, int_pow_0; [ring | reflexivity].
Qed.

Lemma int_pow_2 x : x ^ (2:B) = x * x.
Proof. now rewrite int_pow_S_nonneg, int_pow_1 by solve_propholds. Qed.

Lemma int_pow_3 x : x ^ (3:B) = x * (x * x).
Proof. now rewrite int_pow_S_nonneg, int_pow_2 by solve_propholds. Qed.

Lemma int_pow_4 x : x ^ (4:B) = x * (x * (x * x)).
Proof. now rewrite int_pow_S_nonneg, int_pow_3 by solve_propholds. Qed.

Global Instance int_pow_base_1: LeftAbsorb (^) (1:A).
Proof.
  red. apply biinduction.
    solve_proper.
   now apply int_pow_0.
  intros n. rewrite int_pow_S, left_identity.
   easy.
  now apply (rings.is_ne_0 1).
Qed.

Lemma int_pow_exp_plus (n m : B) (x : A) :
  x ≠ 0 → x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros nonneg.
  revert n. apply biinduction.
    solve_proper.
   rewrite int_pow_0, left_identity. ring.
  intros n. rewrite <-associativity, 2!int_pow_S; trivial.
  split; intros E.
   rewrite E. ring.
  apply (rings.left_cancellation_ne_0 (.*.) x); trivial.
  rewrite E. ring.
Qed.

Instance int_pow_ne_0 (x : A) (n : B) : PropHolds (x ≠ 0) → PropHolds (x ^ n ≠ 0).
Proof.
  intros nonneg. unfold PropHolds.
  revert n. apply biinduction.
    solve_proper.
   rewrite int_pow_0. apply (rings.is_ne_0 1).
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
  revert m. apply biinduction.
    solve_proper.
   rewrite right_absorb. now rewrite 2!int_pow_0.
  intros m. split; intros E.
   rewrite int_pow_S, <-E.
    rewrite distribute_l, right_identity.
    now rewrite int_pow_exp_plus.
   now apply int_pow_ne_0.
  rewrite int_pow_S in E.
  rewrite distribute_l, right_identity, int_pow_exp_plus in E.
    apply (rings.left_cancellation_ne_0 (.*.) (x ^ n)).
     now apply int_pow_ne_0.
    now rewrite E.
   easy.
  now apply int_pow_ne_0.
Qed.

Context `{Apart A} `{!TrivialApart A} `{!FullPseudoSemiRingOrder (A:=A) Ale Alt}.
Context `{Apart B} `{!TrivialApart B} `{!FullPseudoSemiRingOrder (A:=B) Ble Blt}.

Instance int_pow_pos (x : A) (n : B) : PropHolds (0 < x) → PropHolds (0 < x ^ n).
Proof.
  intros nonneg. unfold PropHolds.
  revert n. apply biinduction.
    solve_proper.
   intros. rewrite int_pow_0. now apply semirings.lt_0_1.
  intros n; split; intros E.
   rewrite int_pow_S.
    now apply pos_mult_compat.
   apply not_symmetry. now apply orders.lt_ne.
  apply (strictly_order_reflecting (x *.)).
  rewrite <-int_pow_S.
   now rewrite right_absorb.
  apply not_symmetry. now apply orders.lt_ne.
Qed.

Instance int_pow_nonneg (x : A) (n : B) : PropHolds (0 ≤ x) → PropHolds (0 ≤ x ^ n).
Proof.
  intros E1. red in E1.
  destruct (orders.le_equiv_lt _ _ E1) as [E2|E2].
   rewrite <-E2.
   destruct (decide (n = 0)) as [En|En].
    rewrite En.
    rewrite int_pow_0.
    apply semirings.le_0_1.
   unfold PropHolds. now rewrite int_pow_base_0.
  now apply orders.lt_le, int_pow_pos.
Qed.

Lemma int_pow_ge_1 (x : A) (n : B) : 1 ≤ x → 0 ≤ n → 1 ≤ x ^ n.
Proof.
  intros E1 E2. revert n E2. apply integers.induction_nonneg; trivial.
    solve_proper.
   now rewrite int_pow_0.
  intros.
  rewrite int_pow_S.
   rewrite <-rings.mult_1_r.
   apply semirings.mult_le_compat; try apply semirings.le_0_1; auto.
  apply orders.lt_ne_flip.
  apply orders.lt_le_trans with 1; trivial.
  now apply semirings.lt_0_1.
Qed.

Lemma int_pow_gt_1 (x : A) (n : B) : 1 < x → 0 < n → 1 < x ^ n.
Proof.
  intros Ex En.
  apply nat_int.lt_iff_S_le in En.
  destruct (semirings.decompose_le En) as [z [Ez1 Ez2]]. ring_simplify in Ez2.
  rewrite Ez2. clear En Ez2 n.
  revert z Ez1. apply integers.induction_nonneg; try assumption.
    solve_proper.
   now rewrite left_identity, right_identity.
  intros n En E2.
  rewrite <-associativity, int_pow_S.
   apply semirings.gt_1_mult_lt_compat_l; auto.
   transitivity (1:A); [apply semirings.lt_0_1 | assumption].
  apply orders.lt_ne_flip.
  apply orders.le_lt_trans with 1; trivial.
  now apply semirings.le_0_1.
Qed.

(* Making these instances Global is not useful, we don't have PropHolds (1 ≤ x)
  instances and it will only slow down instance resolution (it increases the
  compilation time of dyadics from 1:35 to 2:28). *)
Instance int_pow_exp_le:
  ∀ x : A, PropHolds (1 ≤ x) → OrderPreserving (x^).
Proof.
  repeat (split; try apply _).
  assert (0 < x) by (apply orders.lt_le_trans with 1; [solve_propholds | easy]).
  intros n m E.
  destruct (semirings.decompose_le E) as [z [Ea Eb]].
  rewrite Eb.
  rewrite int_pow_exp_plus by now apply orders.lt_ne_flip.
  rewrite <-rings.mult_1_r at 1.
  apply (order_preserving (x ^ n *.)).
  now apply int_pow_ge_1.
Qed.

Instance int_pow_exp_lt:
  ∀ x : A, PropHolds (1 < x) → StrictlyOrderPreserving (x^).
Proof.
  repeat (split; try apply _).
  assert (0 < x) by (apply orders.le_lt_trans with 1; [solve_propholds | easy]).
  intros n m E.
  apply nat_int.lt_iff_plus_1_le in E.
  destruct (semirings.decompose_le E) as [z [Ea Eb]].
  rewrite Eb.
  rewrite <-associativity, int_pow_exp_plus by now apply orders.lt_ne_flip.
  rewrite <-(rings.mult_1_r (x ^ n)) at 1.
  apply (strictly_order_preserving (x^n *.)).
  apply int_pow_gt_1; trivial.
  now apply nat_int.le_iff_lt_S.
Qed.

Instance int_pow_exp_le_back:
  ∀ x : A, PropHolds (1 < x) → OrderReflecting (x^).
Proof.
  split; try apply _. intros n m E1.
  destruct (total (≤) n m) as [E2|E2]; trivial.
  destruct (orders.le_equiv_lt _ _ E2) as [E3|E3].
   now rewrite E3.
  contradict E1.
  apply orders.lt_not_le_flip.
  now apply (strictly_order_preserving (x^)).
Qed.

Instance int_pow_exp_lt_back:
  ∀ x : A, PropHolds (1 < x) → StrictlyOrderReflecting (x^).
Proof. intros ? E1. apply _. Qed.

Instance int_pow_inj:
  ∀ x : A, PropHolds (1 < x) → Injective (x^).
Proof.
  repeat (split; try apply _). intros n m E.
  apply (antisymmetry (≤)); apply (order_reflecting (x^)); trivial; rewrite E; reflexivity.
Qed.
End int_pow_properties.

(* Due to bug #2528 *)
Hint Extern 18 (PropHolds (_ ^ _ ≠ 0)) => eapply @int_pow_ne_0 : typeclass_instances.
Hint Extern 18 (PropHolds (0 ≤ _ ^ _)) => eapply @int_pow_nonneg : typeclass_instances.
Hint Extern 18 (PropHolds (0 < _ ^ _)) => eapply @int_pow_pos : typeclass_instances.

Section preservation.
  Context
    `{Integers B}
    `{DecField A1} `{∀ x y : A1, Decision (x = y)} `{!IntPowSpec A1 B ip1}
    `{DecField A2} `{∀ x y : A2, Decision (x = y)} `{!IntPowSpec A2 B ip2}
    {f : A1 → A2} `{!SemiRing_Morphism f}.

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
    revert n. apply biinduction.
      solve_proper.
     rewrite int_pow_0, int_pow_0.
     now apply rings.preserves_1.
    intros n.
    assert (f x ≠ 0) by now apply rings.injective_ne_0.
    rewrite 2!int_pow_S, rings.preserves_mult; trivial.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) (f x)).
  Qed.
End preservation.

Section exp_preservation.
  Context `{Field A} `{∀ x y : A, Decision (x = y)}
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
    revert n. apply biinduction.
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
  Context `{DecField A} `{∀ x y, Decision (x = y)}
    `{Integers B} `{Apart B} `{!TrivialApart B} `{!FullPseudoSemiRingOrder (A:=B) Ble Blt}.

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
      now apply nat_pow_base_0, int_abs_ne_0.
     rewrite nat_pow_base_0.
     apply dec_recip_0.
     now apply int_abs_ne_0.
    intros x n E. case (decide_rel _); case (decide_rel _); intros E1 E2.
       now rewrite int_abs_nonneg_plus, int_abs_1 by (auto;solve_propholds).
      setoid_replace n with (-1 : B).
       rewrite rings.plus_negate_r, int_abs_0, nat_pow_0.
       rewrite int_abs_negate, int_abs_1, right_identity.
       symmetry. now apply dec_recip_inverse.
      apply (antisymmetry (≤)).
       apply orders.not_le_lt_flip in E1.
       apply nat_int.lt_iff_plus_1_le in E1.
       apply (order_reflecting (+1)).
       now ring_simplify.
      apply (order_reflecting (1+)). now rewrite rings.plus_negate_r.
     destruct E2. apply semirings.nonneg_plus_compat; [solve_propholds | assumption].
     rewrite <-int_abs_negate, <-(int_abs_negate n).
     setoid_replace (-n) with (1 - (1 + n)) by ring.
     rewrite (int_abs_nonneg_plus 1 (-(1 + n))), int_abs_1.
       rewrite nat_pow_S.
       rewrite dec_recip_distr, associativity.
       now rewrite dec_recip_inverse, left_identity.
      now apply (rings.is_nonneg 1).
     now apply rings.flip_nonpos_negate, orders.le_flip.
  Qed.
End int_pow_default.
