Require
  MathClasses.theory.naturals.
Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.orders MathClasses.interfaces.additional_operations.

(* * Properties of Nat Pow *)
Section nat_pow_properties.
Context `{SemiRing A} `{Naturals B} `{!NatPowSpec A B pw}.

Add Ring A: (rings.stdlib_semiring_theory A).
Add Ring B: (rings.stdlib_semiring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) (^) | 0.
Proof nat_pow_proper.

Global Instance nat_pow_mor_1: ∀ x : A, Setoid_Morphism (x^) | 0.
Proof. split; try apply _. Qed.

Global Instance nat_pow_mor_2: ∀ n : B, Setoid_Morphism (^n) | 0.
Proof. split; try apply _. solve_proper. Qed.

Lemma nat_pow_base_0 (n : B) : n ≠ 0 → 0 ^ n = 0.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   intros E. now destruct E.
  intros. rewrite nat_pow_S. ring.
Qed.

Global Instance nat_pow_1: RightIdentity (^) (1:B).
Proof.
  intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
  rewrite nat_pow_S, nat_pow_0. ring.
Qed.

Lemma nat_pow_2 x : x ^ (2:B) = x * x.
Proof. now rewrite nat_pow_S, nat_pow_1. Qed.

Lemma nat_pow_3 x : x ^ (3:B) = x * (x * x).
Proof. now rewrite nat_pow_S, nat_pow_2. Qed.

Lemma nat_pow_4 x : x ^ (4:B) = x * (x * (x * x)).
Proof. now rewrite nat_pow_S, nat_pow_3. Qed.

Global Instance nat_pow_base_1: LeftAbsorb (^) 1.
Proof.
  intro.
  pattern y. apply naturals.induction; clear y.
    solve_proper.
   apply nat_pow_0.
  intros n E. rewrite nat_pow_S. rewrite E. ring.
Qed.

Lemma nat_pow_exp_plus (x : A) (n m : B) :
  x ^ (n + m) = x ^ n * x ^ m.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   rewrite nat_pow_0, left_identity. ring.
  intros n E.
  rewrite <-associativity.
  rewrite 2!nat_pow_S.
  rewrite E. ring.
Qed.

Lemma nat_pow_base_mult (x y : A) (n : B) :
  (x * y) ^ n = x ^ n * y ^ n.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   rewrite ?nat_pow_0. ring.
  intros n E.
  rewrite ?nat_pow_S.
  rewrite E. ring.
Qed.

Lemma nat_pow_exp_mult (x : A) (n m : B) :
  x ^ (n * m) = (x ^ n) ^ m.
Proof.
  pattern m. apply naturals.induction; clear m.
    solve_proper.
   rewrite right_absorb. now rewrite ?nat_pow_0.
  intros m E.
  rewrite nat_pow_S, <-E.
  rewrite distribute_l, right_identity.
  now rewrite nat_pow_exp_plus.
Qed.

Instance nat_pow_ne_0 `{!NoZeroDivisors A} `{!PropHolds ((1:A) ≠ 0)} (x : A) (n : B) :
  PropHolds (x ≠ 0) → PropHolds (x ^ n ≠ 0).
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
    intros. rewrite nat_pow_0. now apply (rings.is_ne_0 1).
  intros n E F G. rewrite nat_pow_S in G.
  unfold PropHolds in *.
  apply (no_zero_divisors x); split; eauto.
Qed.

Context `{Apart A} `{!FullPseudoSemiRingOrder (A:=A) Ale Alt} `{PropHolds (1 ≶ 0)}.

Instance: StrongSetoid A := pseudo_order_setoid.

Instance nat_pow_apart_0 (x : A) (n : B) : PropHolds (x ≶ 0) → PropHolds (x ^ n ≶ 0).
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   intros. now rewrite nat_pow_0.
  intros n E F. rewrite nat_pow_S.
  rewrite <-(rings.mult_0_r x).
  apply (strong_left_cancellation (.*.) x). now apply E.
Qed.

Instance nat_pow_nonneg (x : A) (n : B) : PropHolds (0 ≤ x) → PropHolds (0 ≤ x ^ n).
Proof.
  intros. pattern n. apply naturals.induction; clear n.
    solve_proper.
   rewrite nat_pow_0. apply _.
  intros. rewrite nat_pow_S. apply _.
Qed.

Instance nat_pow_pos (x : A) (n : B) : PropHolds (0 < x) → PropHolds (0 < x ^ n).
Proof.
  rewrite !lt_iff_le_apart.
  intros [? ?]. split.
   now apply nat_pow_nonneg.
  symmetry. apply nat_pow_apart_0.
  red. now symmetry.
Qed.

Lemma nat_pow_ge_1 (x : A) (n : B) : 1 ≤ x → 1 ≤ x ^ n.
Proof.
  intros. pattern n. apply naturals.induction.
    solve_proper.
   now rewrite nat_pow_0.
  intros. rewrite nat_pow_S.
  now apply semirings.ge_1_mult_compat.
Qed.
End nat_pow_properties.

(* Due to bug #2528 *)
Hint Extern 18 (PropHolds (_ ^ _ ≠ 0)) => eapply @nat_pow_ne_0 : typeclass_instances.
Hint Extern 18 (PropHolds (_ ^ _ ≶ 0)) => eapply @nat_pow_apart_0 : typeclass_instances.
Hint Extern 18 (PropHolds (0 ≤ _ ^ _)) => eapply @nat_pow_nonneg : typeclass_instances.
Hint Extern 18 (PropHolds (0 < _ ^ _)) => eapply @nat_pow_pos : typeclass_instances.

Section preservation.
  Context `{Naturals B} `{SemiRing A1} `{!NatPowSpec A1 B pw1} `{SemiRing A2} `{!NatPowSpec A2 B pw2}
    {f : A1 → A2} `{!SemiRing_Morphism f}.

  Add Ring B2 : (rings.stdlib_semiring_theory B).

  Lemma preserves_nat_pow x (n : B) : f (x ^ n) = (f x) ^ n.
  Proof.
    revert n. apply naturals.induction.
      solve_proper.
     rewrite nat_pow_0, nat_pow_0. now apply rings.preserves_1.
    intros n E.
    rewrite nat_pow_S, rings.preserves_mult, E.
    now rewrite nat_pow_S.
  Qed.
End preservation.

Section exp_preservation.
  Context `{SemiRing A} `{Naturals B1} `{Naturals B2} `{!NatPowSpec A B1 pw1} `{!NatPowSpec A B2 pw2}
    {f : B1 → B2} `{!SemiRing_Morphism f}.

  Lemma preserves_nat_pow_exp x (n : B1) : x ^ (f n) = x ^ n.
  Proof.
    revert n. apply naturals.induction.
      solve_proper.
     rewrite rings.preserves_0.
     now rewrite 2!nat_pow_0.
    intros n E.
    rewrite rings.preserves_plus, rings.preserves_1.
    rewrite 2!nat_pow_S.
    now rewrite E.
  Qed.
End exp_preservation.

(* Very slow default implementation by translation into Peano *)
Section nat_pow_default.
  Context `{SemiRing A}.

  Global Instance nat_pow_peano: Pow A nat :=
    fix nat_pow_rec (x: A) (n : nat) : A := match n with
    | 0 => 1
    | S n => x * @pow _ _ nat_pow_rec x n
    end.

  Instance: Proper ((=) ==> (=) ==> (=)) nat_pow_peano.
  Proof.
    intros ? ? E a ? [].
    induction a; try easy.
    simpl. now rewrite IHa, E.
  Qed.

  Global Instance: NatPowSpec A nat nat_pow_peano.
  Proof. split; try apply _; easy. Qed.

  Context `{Naturals B}.

  Global Instance default_nat_pow: Pow A B | 10 := λ x n, x ^ naturals_to_semiring B nat n.
  Global Instance: NatPowSpec A B default_nat_pow.
  Proof.
    split; unfold pow, default_nat_pow.
      solve_proper.
     intros x. now rewrite rings.preserves_0.
    intros x n. now rewrite rings.preserves_plus, rings.preserves_1.
  Qed.
End nat_pow_default.

Typeclasses Opaque default_nat_pow.
