(* We don't actually make a structure, but prove a handful of useful things that
 help in signed_binary_positive_integers.v. *)

Require
  interfaces.naturals.
Require Import
  BinInt Morphisms Ring Arith
  abstract_algebra theory.rings peano_naturals.

Lemma xO_in_ring_terms p: xO p ≡ (p + p)%positive.
Proof with auto.
 unfold sg_op.
 induction p; simpl...
  rewrite Pplus_carry_spec, <- IHp...
 congruence.
Qed.

Lemma xI_in_ring_terms p: xI p ≡ (p + p + 1)%positive.
Proof. intros. rewrite <- xO_in_ring_terms. reflexivity. Qed.

Definition map_pos `{RingPlus R} `{RingOne R}: positive → R :=
  fix F (x: positive) :=
    match x with
    | (p~0)%positive => F p + F p
    | (p~1)%positive => F p + F p + 1
    | 1%positive => 1
    end.

Lemma map_pos_tri `{SemiRing R} `{SemiRing R'} (f: R → R') `{!SemiRing_Morphism f}: ∀ p, f (map_pos p) = map_pos p.
Proof.
 induction p; simpl;
 repeat (try rewrite preserves_plus; try rewrite preserves_1);
 try rewrite IHp; reflexivity.
Qed.

Section contents.
  Context `{SemiRing R}.

  Add Ring R: (stdlib_semiring_theory R).

  Lemma preserves_Psucc x: map_pos (Psucc x) = map_pos x + 1.
  Proof. induction x; simpl; try reflexivity. rewrite IHx. ring. Qed.

  Lemma preserves_Pplus x: ∀ y, map_pos (x + y) = map_pos x + map_pos y.
  Proof with try ring.
   induction x; destruct y; simpl; try rewrite IHx...
     rewrite Pplus_carry_spec, preserves_Psucc, IHx...
    rewrite preserves_Psucc...
   rewrite preserves_Psucc...
  Qed.

  Lemma Pmult_sr_mult p: ∀ n, Pmult_nat p n = map_pos p * n.
  Proof with try ring.
   induction p; simpl; intros; try rewrite IHp...
    change (n + map_pos p * (n + n) = (map_pos p + map_pos p + 1) * n)...
   change (map_pos p * (n + n) = (map_pos p + map_pos p) * n)...
  Qed.

  Lemma map_pos_nat_of_P p: map_pos p = nat_of_P p.
  Proof.
   unfold nat_of_P. intros.
   rewrite Pmult_sr_mult. replace 1%nat with (1:nat) by reflexivity.
   ring.
  Qed.

  Lemma preserves_Pmult x: ∀ y, map_pos (x * y) = map_pos x * map_pos y.
  Proof with try reflexivity; try ring.
   induction x; intros; simpl...
    rewrite preserves_Pplus.
    rewrite distribute_r.
    rewrite xO_in_ring_terms.
    rewrite preserves_Pplus.
    rewrite IHx...
   rewrite distribute_r.
   rewrite IHx...
  Qed.

End contents.

Lemma preserves_Pminus_nat x y: (y < x)%positive → map_pos (x - y) = minus (map_pos x) (map_pos y).
Proof.
 intros.
 repeat rewrite map_pos_nat_of_P.
 rewrite nat_of_P_minus_morphism. reflexivity.
 unfold Plt in H.
 now apply ZC2.
Qed.

Lemma preserves_minus `{Ring R} (f: nat → R) `{!SemiRing_Morphism f}
  x y (P: (y <= x)%nat): f (x - y)%nat = f x + - f y.
Proof.
 rewrite (Minus.le_plus_minus _ _ P: x = (y + (x - y)%nat)) at 2.
 rewrite preserves_plus, commutativity, associativity, plus_opp_l, plus_0_l.
 reflexivity.
Qed.

Lemma preserves_Pminus `{Ring R} x y: (y < x)%positive → map_pos (x - y) = map_pos x + - map_pos y.
Proof with try apply _; intuition.
 intros.
 rewrite <- (map_pos_tri (naturals.naturals_to_semiring nat R)).
 rewrite preserves_Pminus_nat...
 rewrite preserves_minus...
  rewrite map_pos_tri...
  rewrite map_pos_tri...
 rewrite 2!map_pos_nat_of_P.
 apply lt_le_weak, nat_of_P_lt_Lt_compare_morphism...
Qed.
