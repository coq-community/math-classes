Require
  theory.naturals orders.semirings orders.naturals.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.naturals interfaces.additional_operations.

(* * Properties of Nat Pow spec *)
Section nat_pow_spec_properties.
  Context `{SemiRing A} 
    `{SemiRing B} {oB : Order B} `{!SemiRingOrder oB} `{!TotalOrder oB}
    `{∀ z : B, LeftCancellation (+) z} `{!NeZero (1:B)}.

  Global Instance nat_pow_spec_proper: 
    Proper ((=) ==> (=) ==> (=) ==> iff) (nat_pow_spec (A:=A) (B:=B)).
  Proof with eauto.
    intros x1 x2 E n1 n2 F y1 y2 G. 
    split; intro. eapply nat_pow_spec_proper'...
    eapply nat_pow_spec_proper'; try symmetry...
  Qed.

  Tactic Notation "gen_eq" constr(c) "as" ident(x) :=
    set (x := c) in *;
    let H := fresh in (assert (H : x = c) by reflexivity; clearbody x; revert H).

  Lemma nat_pow_spec_nonneg x (n : B) y : nat_pow_spec x n y → 0 ≤ n.
  Proof with auto.
    induction 1 as [ |  | ? ? ? ? ? ? ? G ].
    reflexivity.
    apply semirings.nonneg_plus_compat...
    apply semirings.precedes_0_1.
    rewrite <-G...
  Qed.

  Lemma nat_pow_spec_nz_one_plus_zero x (n : B) y : nat_pow_spec x n y → 1 + n ≠ 0.
  Proof.
    intros E F.
    destruct semirings.not_precedes_1_0.
    apply (order_preserving_back (n +)).
    rewrite commutativity, F, right_identity.
    eapply nat_pow_spec_nonneg; eassumption.
  Qed.

  Lemma nat_pow_spec_unique x (n : B) y1 y2 : 
    nat_pow_spec x n y1 → nat_pow_spec x n y2 → y1 = y2.
  Proof with eauto; try reflexivity.
    intros E F. generalize dependent y2. 
    induction E as [ | | ? ? ? ? ? ? G1 G2 G3]. 
      intros.
      gen_eq (0:B) as n. induction F as [ |  | ? ? ? ? ? ? G1 G2 G3 ]; intros...
       edestruct nat_pow_spec_nz_one_plus_zero...
      rewrite <-G3. apply IHF. rewrite G2...
     intros.
     gen_eq (1+n) as m. generalize dependent n. generalize dependent y. 
     induction F as [ | | ? ? ? ? ? ? G1 G2 G3 ]; intros ? ? ? ? G4.
       edestruct nat_pow_spec_nz_one_plus_zero... symmetry...
      apply sg_mor... apply IHE. 
      apply (left_cancellation (+) 1) in G4... 
      symmetry in G4. eapply nat_pow_spec_proper...
     rewrite <-G1, <-G3. apply (IHF _ n)... 
       eapply nat_pow_spec_proper...
      intros. apply IHE. symmetry in G1. eapply nat_pow_spec_proper... 
     rewrite G2...
    intros. rewrite <-G3. apply IHE. eapply nat_pow_spec_proper... 
  Qed.
End nat_pow_spec_properties.

(* * Properties of Nat Pow *)
Section nat_pow_properties.
  Context `{SemiRing A} `{Naturals B}.

  Add Ring A: (rings.stdlib_semiring_theory A).
  Add Ring B: (rings.stdlib_semiring_theory B).

  Section nat_pow_spec_from_properties.
  Context (f : A → B → A) {f_proper : Proper ((=) ==> (=) ==> (=)) f}
    ( f_0 : ∀x, f x 0 = 1 ) ( f_S : ∀ x n,  f x (1+n) = x * (f x n) ).

  Lemma nat_pow_spec_from_properties x n : nat_pow_spec x n (f x n).
  Proof with eauto; try reflexivity.
    revert n. apply naturals.induction.
    intros ? ? E. 
      apply nat_pow_spec_proper...
      rewrite E...
     eapply nat_pow_spec_proper... apply nat_pow_spec_0...
    intros. eapply nat_pow_spec_proper...
    eapply nat_pow_spec_S...
  Qed.
  End nat_pow_spec_from_properties.

  Context `{np : !NatPow A B}.
  Global Instance nat_pow_proper: Proper ((=) ==> (=) ==> (=)) (^).
  Proof with eauto.
    intros x1 x2 E y1 y2 F. 
    unfold pow, nat_pow, nat_pow_sig. do 2 destruct np. simpl.
    eapply nat_pow_spec_unique...
    eapply nat_pow_spec_proper... reflexivity. 
  Qed.

  Lemma nat_pow_0 x : x ^ 0 = 1.
  Proof with eauto.
   unfold pow, nat_pow, nat_pow_sig. destruct np. simpl.
   eapply nat_pow_spec_unique... apply nat_pow_spec_0.
  Qed.

  Lemma nat_pow_S x n : x ^ (1+n) = x * x ^ n.
  Proof with eauto.
   unfold pow, nat_pow, nat_pow_sig. do 2 destruct np. simpl.
   eapply nat_pow_spec_unique... eapply nat_pow_spec_S...
  Qed.

  Instance: RightIdentity (^) 1.
  Proof. 
    intro. assert ((1:B) = 1 + 0) as E by ring. rewrite E.
    rewrite nat_pow_S, nat_pow_0. ring.
  Qed.

  Instance: LeftAbsorb (^) 1.
  Proof. 
    intro. 
    pattern y. apply naturals.induction; clear y.
      intros ? ? E. rewrite E. tauto.
     apply nat_pow_0.
    intros n E. rewrite nat_pow_S. rewrite E. ring.
  Qed.
  
  Lemma nat_pow_exp_plus (x : A) (n m : B) : 
    x ^ (n + m) = x ^ n * x ^ m.
  Proof with auto.
    pattern n. apply naturals.induction; clear n.
      intros ? ? E. rewrite E. reflexivity.
     rewrite nat_pow_0, left_identity. ring.
    intros n E. 
    rewrite <-associativity.
    do 2 rewrite nat_pow_S.
    rewrite E. ring.
  Qed.
  
  Lemma nat_pow_base_mult (x y : A) (n : B) : 
    (x * y) ^ n = x ^ n * y ^ n.
  Proof with auto.
    pattern n. apply naturals.induction; clear n.
      intros ? ? E. rewrite E. reflexivity.
     repeat rewrite nat_pow_0. ring.
    intros n E. 
    repeat rewrite nat_pow_S.
    rewrite E. ring.
  Qed.

  Lemma nat_pow_exp_mult (x : A) (n m : B) : 
    x ^ (n * m) = (x ^ n) ^ m.
  Proof with auto.
    pattern m. apply naturals.induction; clear m.
      intros ? ? E. rewrite E. reflexivity.
     rewrite right_absorb. repeat rewrite nat_pow_0. reflexivity.
    intros m E. 
    rewrite nat_pow_S, <-E.
    rewrite distribute_l, right_identity.
    rewrite nat_pow_exp_plus. reflexivity.
  Qed.

  Context `{!NoZeroDivisors A} `{!NeZero (1:A) }.

  Lemma nat_pow_nonzero (x : A) (n : B) : x ≠ 0 → x ^ n ≠ 0.
  Proof with eauto.
    pattern n. apply naturals.induction; clear n.
      intros x1 x2 E. rewrite E. reflexivity.
     intros. rewrite nat_pow_0. apply (ne_zero 1).
    intros n E F G. rewrite nat_pow_S in G.
    apply (no_zero_divisors x); split... 
  Qed. 
End nat_pow_properties.

Section preservation.
  Context `{Naturals B} `{SemiRing A1} `{!NatPow A1 B} `{SemiRing A2} `{!NatPow A2 B} 
    {f : A1 → A2} `{!SemiRing_Morphism f}.

  Add Ring B2 : (rings.stdlib_semiring_theory B).

  Lemma preserves_nat_pow x (n : B) : f (x ^ n) = (f x) ^ n.
  Proof with auto.
    revert n. apply naturals.induction.
      intros ? ? E1. rewrite E1. reflexivity.
     rewrite nat_pow_0, nat_pow_0. apply rings.preserves_1.
    intros n E. 
    rewrite nat_pow_S, rings.preserves_mult, E.
    rewrite nat_pow_S. reflexivity.
  Qed.
End preservation.

(* Very slow default implementation by translation into Peano *)
Section nat_pow_default.
  Context `{SemiRing A} `{Naturals B}.
  
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
  Next Obligation with reflexivity.
    apply nat_pow_spec_from_properties; unfold nat_pow_default.
      intros ? ? E1 ? ? E2. rewrite E1, E2...
     intros. rewrite rings.preserves_0...
    intros. rewrite rings.preserves_plus, rings.preserves_1, <-peano_naturals.S_nat_1_plus...
  Qed.
End nat_pow_default.
