Require
  theory.naturals orders.semirings orders.naturals.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.additional_operations.

(* * Properties of Nat Pow *)
Section nat_pow_properties.
Context `{SemiRing A} `{Naturals B} `{!NatPowSpec A B pw}.

Add Ring A: (rings.stdlib_semiring_theory A).
Add Ring B: (rings.stdlib_semiring_theory B).

Global Instance: Proper ((=) ==> (=) ==> (=)) (^) | 1.
Proof. apply nat_pow_proper. Qed.

Lemma nat_pow_base_0 (n : B) : n ≠ 0 → 0 ^ n = 0.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   intros E. now destruct E.
  intros. rewrite nat_pow_S. ring.
Qed.

Global Instance: RightIdentity (^) (1:B).
Proof. 
  intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
  rewrite nat_pow_S, nat_pow_0. ring.
Qed.

Global Instance: LeftAbsorb (^) 1.
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

Context `{!NoZeroDivisors A} `{!NeZero (1:A) }.

Lemma nat_pow_nonzero (x : A) (n : B) : x ≠ 0 → x ^ n ≠ 0.
Proof.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   intros. rewrite nat_pow_0. now apply (ne_zero 1).
  intros n E F G. rewrite nat_pow_S in G.
  apply (no_zero_divisors x); split; eauto.
Qed. 

Context `{oA : Order A} `{!SemiRingOrder oA} `{!TotalOrder oA} 
  `{∀ z : A, LeftCancellation (+) z}
  `{∀ z : A, NeZero z → LeftCancellation (.*.) z}.

Lemma nat_pow_pos (x : A) (n : B) : 0 < x → 0 < x ^ n.
Proof.
  intros nonneg.
  pattern n. apply naturals.induction; clear n.
    solve_proper.
   rewrite nat_pow_0. now apply semirings.sprecedes_0_1.
  intros n E. rewrite nat_pow_S.
  now apply semirings.pos_mult_scompat.
Qed.

End nat_pow_properties.

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
  Context `{SemiRing A} `{Naturals B}.
  
  Fixpoint nat_pow_rec (x: A) (n : nat) : A := match n with
  | 0 => 1
  | S n => x * nat_pow_rec x n
  end.

  Instance: Proper ((=) ==> (=) ==> (=)) nat_pow_rec.
  Proof.
    intros x y E a ? [].
    induction a; try easy.
    simpl. now rewrite IHa, E.
  Qed.

  Global Instance nat_pow_default: Pow A B | 10 := λ x n, nat_pow_rec x (naturals_to_semiring B nat n).
  Global Instance: NatPowSpec A B nat_pow_default.
  Proof.
    split; unfold pow, nat_pow_default.
      solve_proper.
     intros x. now rewrite rings.preserves_0.
    intros x n. now rewrite rings.preserves_plus, rings.preserves_1.
  Qed.
End nat_pow_default.
