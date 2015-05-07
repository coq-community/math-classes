Require
  MathClasses.orders.integers MathClasses.theory.dec_fields MathClasses.theory.nat_pow.
Require Import
  Coq.setoid_ring.Ring
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.integers
  MathClasses.interfaces.additional_operations MathClasses.interfaces.orders.

Section shiftl.
Context `{SemiRing A} `{!LeftCancellation (.*.) (2:A)} `{SemiRing B} `{!Biinduction B} `{!ShiftLSpec A B sl}.

Add Ring A: (rings.stdlib_semiring_theory A).
Add Ring B: (rings.stdlib_semiring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) ((≪) : A → B → A) | 1.
Proof shiftl_proper.

Global Instance shiftl_mor_1: ∀ x : A, Setoid_Morphism (x≪) | 0.
Proof. split; try apply _. Qed.

Global Instance shiftl_mor_2: ∀ n : B, Setoid_Morphism (≪n) | 0.
Proof. split; try apply _. solve_proper. Qed.

Lemma shiftl_nat_pow_alt `{Naturals B2} `{!NatPowSpec A B2 pw}
  `{!SemiRing_Morphism (f : B2 → B)} x n : x ≪ f n = x * 2 ^ n.
Proof.
  revert n. apply naturals.induction.
    solve_proper.
   rewrite rings.preserves_0, ?shiftl_0, nat_pow_0. ring.
  intros n E.
  rewrite rings.preserves_plus, rings.preserves_1, shiftl_S.
  rewrite E, nat_pow_S. ring.
Qed.

Lemma shiftl_nat_pow `{!NaturalsToSemiRing B} `{!Naturals B} `{!NatPowSpec A B np} x n :
  x ≪ n = x * 2 ^ n.
Proof. change (x ≪ id n = x * 2 ^ n). apply shiftl_nat_pow_alt. Qed.

Lemma shiftl_1 x : x ≪ (1:B) = 2 * x.
Proof. now rewrite <-(rings.plus_0_r 1), shiftl_S, shiftl_0. Qed.

Lemma shiftl_2 x : x ≪ (2:B) = 4 * x.
Proof. rewrite shiftl_S, shiftl_1. ring. Qed.

Global Instance shiftl_base_0: LeftAbsorb (≪) 0.
Proof.
  intros n. pattern n. apply biinduction; clear n.
    solve_proper.
   now apply shiftl_0.
  intros n; split; intros E.
   rewrite shiftl_S, E. ring.
  apply (left_cancellation (.*.) 2).
  rewrite <-shiftl_S, E. ring.
Qed.

Lemma shiftl_exp_plus x n m : x ≪ (n + m) = x ≪ n ≪ m.
Proof.
  pattern m. apply biinduction; clear m.
    solve_proper.
   now rewrite shiftl_0, rings.plus_0_r.
  intros m.
  setoid_replace (n + (1 + m)) with (1 + (n + m)) by ring.
  rewrite ?shiftl_S.
  split; intros E.
   now rewrite E.
  now apply (left_cancellation (.*.) 2).
Qed.

Lemma shiftl_order x n m: x ≪ n ≪ m  = x ≪ m ≪ n.
Proof. rewrite <-?shiftl_exp_plus. now rewrite commutativity. Qed.

Lemma shiftl_reverse (x : A) (n m : B) : n + m = 0 → x ≪ n ≪ m = x.
Proof. intros E. now rewrite <-shiftl_exp_plus, E, shiftl_0. Qed.

Lemma shiftl_mult_l x y n : x * (y ≪ n) = (x * y) ≪ n.
Proof.
  pattern n. apply biinduction; clear n.
    solve_proper.
   now rewrite ?shiftl_0.
  intros m.
  rewrite ?shiftl_S.
  split; intros E.
   rewrite <-E. ring.
  apply (left_cancellation (.*.) 2). rewrite <-E. ring.
Qed.

Lemma shiftl_mult_r x y n : (x ≪ n) * y = (x * y) ≪ n.
Proof. now rewrite commutativity, shiftl_mult_l, commutativity. Qed.

Lemma shiftl_base_plus x y n : (x + y) ≪ n  = x ≪ n + y ≪ n.
Proof.
  pattern n. apply biinduction; clear n.
    solve_proper.
   now rewrite ?shiftl_0.
  intros m. rewrite ?shiftl_S.
  split; intros E.
   rewrite E. ring.
  apply (left_cancellation (.*.) 2). rewrite E. ring.
Qed.

Lemma shiftl_base_nat_pow `{Naturals B2} `{!NatPowSpec A B2 pw} `{!SemiRing_Morphism (f : B2 → B)} x n m :
  (x ≪ n) ^ m = (x ^ m) ≪ (n * f m).
Proof.
  revert m. apply naturals.induction.
    solve_proper.
   rewrite ?nat_pow_0.
   now rewrite rings.preserves_0, rings.mult_0_r, shiftl_0.
  intros m E.
  rewrite rings.preserves_plus, rings.preserves_1.
  rewrite rings.plus_mult_distr_l, rings.mult_1_r, shiftl_exp_plus.
  rewrite !nat_pow_S, E.
  now rewrite shiftl_mult_l, shiftl_mult_r.
Qed.

Lemma shiftl_negate `{Negate A} `{!Ring A} x n : (-x) ≪ n = -(x ≪ n).
Proof.
  rewrite (rings.negate_mult x), (rings.negate_mult (x ≪ n)).
  symmetry. now apply shiftl_mult_l.
Qed.

Global Instance shiftl_inj: ∀ n, Injective (≪ n).
Proof.
  repeat (split; try apply _).
  pattern n. apply biinduction; clear n.
    solve_proper.
   intros x y E. now rewrite ?shiftl_0 in E.
  intros n; split; intros E1 x y E2.
   apply E1. rewrite ?shiftl_S in E2.
   now apply (left_cancellation (.*.) 2).
  apply E1. now rewrite ?shiftl_S, E2.
Qed.

Instance shiftl_ne_0 x n :
  PropHolds (x ≠ 0) → PropHolds (x ≪ n ≠ 0).
Proof.
  intros E1 E2. apply E1.
  apply (injective (≪ n)).
  now rewrite shiftl_base_0.
Qed.

Context `{Apart A} `{!FullPseudoSemiRingOrder (A:=A) Ale Alt} `{!PropHolds ((1:A) ≶ 0)}.

Let shiftl_strict_order_embedding (x y : A) (n : B) : x < y ↔ x ≪ n < y ≪ n.
Proof.
  revert n. apply (biinduction_iff (x < y) (λ n, x ≪ n < y ≪ n)).
    solve_proper.
   now rewrite 2!shiftl_0.
  intros n. rewrite !shiftl_S.
  split; intros E.
   now apply (strictly_order_preserving (2 *.)).
  now apply (strictly_order_reflecting (2 *.)).
Qed.

Global Instance: ∀ n, StrictOrderEmbedding (≪ n).
Proof.
  repeat (split; try apply _); intros.
   now apply shiftl_strict_order_embedding.
  eapply shiftl_strict_order_embedding. eassumption.
Qed.

Global Instance: ∀ n, OrderEmbedding (≪ n).
Proof.
  split.
   now apply maps.full_pseudo_order_preserving.
  now apply maps.full_pseudo_order_reflecting.
Qed.

Global Instance shiftl_strong_inj: ∀ n, StrongInjective (≪ n).
Proof. intros. apply maps.pseudo_order_embedding_inj. Qed.

Lemma shiftl_le_flip_r `{Negate B} `{!Ring B} (x y : A) (n : B) :
  x ≤ y ≪ (-n)  ↔  x ≪ n ≤ y.
Proof.
  split; intros E.
   apply (order_reflecting (≪ -n)).
   now rewrite shiftl_reverse by now apply rings.plus_negate_r.
  apply (order_reflecting (≪ n)).
  now rewrite shiftl_reverse by now apply rings.plus_negate_l.
Qed.

Lemma shiftl_le_flip_l `{Negate B} `{!Ring B} (x y : A) (n : B) :
  x ≪ (-n) ≤ y  ↔  x ≤ y ≪ n.
Proof. now rewrite <-shiftl_le_flip_r, rings.negate_involutive. Qed.

Instance shiftl_nonneg (x : A) (n : B) : PropHolds (0 ≤ x) → PropHolds (0 ≤ x ≪ n).
Proof.
  intro. rewrite <-(shiftl_base_0 n).
  now apply (order_preserving (≪ n)).
Qed.

Instance shiftl_pos (x : A) (n : B) : PropHolds (0 < x) → PropHolds (0 < x ≪ n).
Proof.
  intro. rewrite <-(shiftl_base_0 n).
  now apply (strictly_order_preserving (≪ n)).
Qed.
End shiftl.

(* Due to bug #2528 *)
Hint Extern 18 (PropHolds (_ ≪ _ ≠ 0)) => eapply @shiftl_ne_0 : typeclass_instances.
Hint Extern 18 (PropHolds (0 ≤ _ ≪ _)) => eapply @shiftl_nonneg : typeclass_instances.
Hint Extern 18 (PropHolds (0 < _ ≪ _)) => eapply @shiftl_pos : typeclass_instances.

Section preservation.
  Context `{SemiRing B} `{!Biinduction B}
    `{SemiRing A1} `{!ShiftLSpec A1 B sl1} `{SemiRing A2} `{!LeftCancellation (.*.) (2:A2)} `{!ShiftLSpec A2 B sl2}
    `{!SemiRing_Morphism (f : A1 → A2)}.

  Lemma preserves_shiftl x (n : B) : f (x ≪ n) = (f x) ≪ n.
  Proof.
    revert n. apply biinduction.
      solve_proper.
     now rewrite 2!shiftl_0.
    intros n; split; intros IH.
     rewrite 2!shiftl_S.
     now rewrite rings.preserves_mult, rings.preserves_2, IH.
    apply (left_cancellation (.*.) 2).
    rewrite <-(rings.preserves_2 (f:=f)) at 1.
    rewrite <-rings.preserves_mult, <-shiftl_S, IH.
    now rewrite shiftl_S.
  Qed.
End preservation.

Section exp_preservation.
  Context `{SemiRing B1} `{!Biinduction B1} `{SemiRing B2} `{!Biinduction B2}
   `{SemiRing A} `{!LeftCancellation (.*.) (2:A)} `{!ShiftLSpec A B1 sl1} `{!ShiftLSpec A B2 sl2}
   `{!SemiRing_Morphism (f : B1 → B2)}.

  Lemma preserves_shiftl_exp x (n : B1) : x ≪ f n = x ≪ n.
  Proof.
    revert n. apply biinduction.
      solve_proper.
     now rewrite rings.preserves_0, ?shiftl_0.
    intros n.
    rewrite rings.preserves_plus, rings.preserves_1, ?shiftl_S.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) 2).
  Qed.
End exp_preservation.

Section shiftl_dec_field.
  Context `{SemiRing R} `{Integers Z} `{!ShiftLSpec R Z sl}
     `{DecField F} `{∀ x y : F, Decision (x = y)} `{!PropHolds ((2:F) ≠ 0)} `{!IntPowSpec F Z ipw}
     `{!SemiRing_Morphism (f : R → F)}.

  Add Ring F: (rings.stdlib_ring_theory F).
  Add Ring Z: (rings.stdlib_ring_theory Z).

  Existing Instance int_pow_proper.

  Lemma shiftl_to_int_pow x n : f (x ≪ n) = f x * 2 ^ n.
  Proof.
    revert n. apply biinduction.
      solve_proper.
     now rewrite shiftl_0, int_pow_0, rings.mult_1_r.
    intros n.
    rewrite shiftl_S, int_pow_S by solve_propholds.
    rewrite rings.preserves_mult, rings.preserves_2.
    rewrite associativity, (commutativity (f x) 2), <-associativity.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) 2).
  Qed.

  Lemma shiftl_base_1_to_int_pow n : f (1 ≪ n) = 2 ^ n.
  Proof. now rewrite shiftl_to_int_pow, rings.preserves_1, rings.mult_1_l. Qed.

  Lemma shiftl_negate_1_to_half x : f (x ≪ -1) = f x / 2.
  Proof.
    rewrite shiftl_to_int_pow.
    apply (left_cancellation (.*.) 2).
    transitivity (f x * (2 * 2 ^ (-1))); [ring |].
    transitivity (f x * (2 / 2)); [| ring].
    rewrite dec_recip_inverse, <-int_pow_S by assumption.
    now rewrite rings.plus_negate_r, int_pow_0.
 Qed.

  Lemma shiftl_negate_1_to_fourth x : f (x ≪ -2) = f x / 4.
  Proof.
    rewrite shiftl_to_int_pow.
    apply (left_cancellation (.*.) (2 * 2)).
    transitivity (f x * (2 * (2 * 2 ^ (-2)))); [ring |].
    transitivity (f x * (4 / 4)); [| ring].
    assert ((4:F) ≠ 0).
     setoid_replace 4 with (2*2) by ring.
     solve_propholds.
    rewrite dec_recip_inverse, <-!int_pow_S by assumption.
    setoid_replace (1 + (1 - 2) : Z) with (0 : Z) by ring.
    now rewrite int_pow_0.
 Qed.
End shiftl_dec_field.

Section more_shiftl_dec_field.
  Context `{DecField A} `{Integers B} `{∀ x y : A, Decision (x = y)}
    `{!PropHolds ((2:A) ≠ 0)} `{!ShiftLSpec A B sl} `{!IntPowSpec A B ipw}.

  Lemma shiftl_int_pow x n : x ≪ n = x * 2 ^ n.
  Proof. change (id (x ≪ n) = id x * 2 ^ n). apply shiftl_to_int_pow. Qed.

  Lemma shiftl_base_1_int_pow n : 1 ≪ n = 2 ^ n.
  Proof. now rewrite shiftl_int_pow, rings.mult_1_l. Qed.

  Lemma shiftl_negate_1_half x : x ≪ (-1) = x / 2.
  Proof. change (id (x ≪ (-1)) = id x / 2). now apply shiftl_negate_1_to_half. Qed.

  Lemma shiftl_negate_1_fourth x : x ≪ (-2) = x / 4.
  Proof. change (id (x ≪ (-2)) = id x / 4). now apply shiftl_negate_1_to_fourth. Qed.
End more_shiftl_dec_field.

Section shiftl_field.
  Context `{Ring R} `{Integers Z} `{!ShiftLSpec R Z sl}
    `{Field F} `{!PropHolds ((2:F) ≶ 0)} `{Naturals N} `{!NatPowSpec F N npw}
    `{!SemiRing_Morphism (g : N → Z)} `{!SemiRing_Morphism (f : R → F)}.

  Add Ring F2: (rings.stdlib_ring_theory F).
  Add Ring Z2: (rings.stdlib_ring_theory Z).

  Lemma shiftl_negate_nat_pow x n : f (x ≪ (-g n)) * 2 ^ n = f x.
  Proof.
    pose proof nat_pow_proper.
    pattern n. apply naturals.induction; clear n.
      solve_proper.
     rewrite rings.preserves_0, rings.negate_0, shiftl_0.
     rewrite nat_pow_0. ring.
    intros n E.
    rewrite rings.preserves_plus, rings.preserves_1.
    etransitivity; [| eassumption].
    setoid_replace (-g n) with (1 - (1 + g n)) by ring.
    rewrite shiftl_S, rings.preserves_mult, rings.preserves_2.
    rewrite nat_pow_S. ring.
  Qed.

  Lemma shiftl_negate_to_recip_nat_pow x n P2n : f (x ≪ (-g n)) = f x // (2 ^ n)↾P2n.
  Proof.
    apply (right_cancellation (.*.) (2 ^ n)).
    rewrite shiftl_negate_nat_pow.
    transitivity (f x * (2 ^ n // (2 ^ n)↾P2n)); [| ring].
    rewrite fields.reciperse_alt. ring.
  Qed.
End shiftl_field.

Section default_shiftl_naturals.
  Context `{SemiRing A} `{Naturals B} `{!NatPowSpec A B pw}.

  Global Instance default_shiftl: ShiftL A B | 10 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl.
  Proof. now apply shiftl_spec_from_nat_pow. Qed.
End default_shiftl_naturals.

Typeclasses Opaque default_shiftl.

Section default_shiftl_integers.
  Context `{DecField A} `{!PropHolds ((2:A) ≠ 0)} `{Integers B} `{!IntPowSpec A B ipw}.

  Global Instance default_shiftl_int: ShiftL A B | 9 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl_int.
  Proof. now apply shiftl_spec_from_int_pow. Qed.
End default_shiftl_integers.

Typeclasses Opaque default_shiftl_int.
