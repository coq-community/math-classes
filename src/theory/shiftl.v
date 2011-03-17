Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.additional_operations theory.nat_pow.

Section shiftl.
  Context `{SemiRing A} `{SemiRing B} `{!ShiftLSpec A B sl}.

  Add Ring A1 : (rings.stdlib_semiring_theory A).

  Global Instance: Proper ((=) ==> (=) ==> (=)) (≪) | 1.
  Proof. apply shiftl_proper. Qed.

  Lemma shiftl_1 x : x ≪ (1:B) = 2 * x.
  Proof. now rewrite <-(rings.plus_0_r 1), shiftl_S, shiftl_0. Qed.

  Lemma shiftl_2 x : x ≪ (2:B) = 4 * x.
  Proof. rewrite shiftl_S, shiftl_1. ring. Qed.
End shiftl.

(* * Properties of [shiftl] on the naturals *)
Section shiftl_naturals.
  Context `{SemiRing A} `{Naturals B}.

  Add Ring A2: (rings.stdlib_semiring_theory A).
  Add Ring B2: (rings.stdlib_semiring_theory B).

  Lemma shiftl_spec_from_nat_pow `{!NatPowSpec A B np} (sl : ShiftL A B) :
    (∀ x n, x ≪ n = x * 2 ^ n) → ShiftLSpec A B sl.
  Proof.
    intros spec.
    split.
      intros ? ? E1 ? ? E2.
      rewrite 2!spec. now rewrite E1, E2.
     intro x. rewrite spec, nat_pow_0. ring.
    intros x n. rewrite 2!spec. rewrite nat_pow_S. ring.
  Qed.

  Context `{!ShiftLSpec A B sl}.

  Lemma shiftl_nat_pow `{!NatPowSpec A B np} x n : x ≪ n = x * 2 ^ n.
  Proof.
    revert n. apply naturals.induction.
      solve_proper.
     rewrite nat_pow_0. now rewrite 2!right_identity.
    intros ? E. rewrite nat_pow_S, shiftl_S, E. ring.
  Qed.

  Global Instance: LeftAbsorb (≪) 0.
  Proof. intro. rewrite shiftl_nat_pow. ring. Qed.

  Lemma shiftl_order x n m : x ≪ n ≪ m  = x ≪ m ≪ n.
  Proof. rewrite 4!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_mult x y n : x * (y ≪ n) = (x * y) ≪ n.
  Proof. rewrite 2!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_1_mult x n : x ≪ n = x * (1 ≪ n).
  Proof. rewrite 2!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_base_plus x y n : (x + y) ≪ n  = x ≪ n + y ≪ n.
  Proof. rewrite 3!shiftl_nat_pow. ring. Qed.

  Lemma shiftl_exp_plus x n m : x ≪ (n + m) = x ≪ n ≪ m.
  Proof. rewrite 3!shiftl_nat_pow. rewrite nat_pow_exp_plus. ring. Qed.

  Lemma shiftl_opp `{GroupInv A} `{!Ring A} x n : (-x) ≪ n = -(x ≪ n).
  Proof.
    rewrite 2!shiftl_nat_pow, rings.opp_mult. 
    symmetry. rewrite rings.opp_mult at 1. ring.
  Qed.

  Context `{!NoZeroDivisors A} `{!PropHolds ((1:A) ≠ 0)} `{!PropHolds ((2:A) ≠ 0)} 
    `{∀z, PropHolds (z ≠ 0) → RightCancellation (.*.) z}.

  Global Instance shiftl_nonzero x n : PropHolds (x ≠ 0) → PropHolds (x ≪ n ≠ 0).
  Proof. intros E. rewrite shiftl_nat_pow. solve_propholds. Qed.

  (* x ≪ b = y ≪ b → x = y *)
  Lemma shiftl_inj n : Injective (flip shiftl n).
  Proof with auto.
    repeat (split; try apply _).
    intros x y E. unfold flip in E. rewrite 2!shiftl_nat_pow in E.
    now apply (right_cancellation (.*.) (2 ^ n)).
  Qed.
End shiftl_naturals.

Section preservation.
  Context `{Naturals B} `{SemiRing A1} `{!ShiftLSpec A1 B sl1} `{SemiRing A2} `{!ShiftLSpec A2 B sl2} 
    {f : A1 → A2} `{!SemiRing_Morphism f}.

  Lemma preserves_shiftl x (n : B) : f (x ≪ n) = (f x) ≪ n.
  Proof.
    rewrite 2!shiftl_nat_pow.
    rewrite rings.preserves_mult.
    rewrite preserves_nat_pow.
    now rewrite rings.preserves_2.
  Qed.
End preservation.

Section exp_preservation.
  Context `{SemiRing A} `{Naturals B1} `{Naturals B2}  `{!ShiftLSpec A B1 sl1} `{!ShiftLSpec A B2 sl2} 
    {f : B1 → B2} `{!SemiRing_Morphism f}.

  Lemma preserves_shiftl_exp x (n : B1) : x ≪ f n = x ≪ n.
  Proof.
    rewrite 2!shiftl_nat_pow.
    now rewrite preserves_nat_pow_exp.
  Qed.
End exp_preservation.

Section default_shiftl.
  Context `{SemiRing A} `{Naturals B} `{!NatPowSpec A B pw}.

  Global Instance default_shiftl: ShiftL A B | 10 := λ x n, x * 2 ^ n.

  Global Instance: ShiftLSpec A B default_shiftl.
  Proof. now apply shiftl_spec_from_nat_pow. Qed.
End default_shiftl.
