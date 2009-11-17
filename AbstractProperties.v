Require Import Structures RingOps.

(* various derived identities: *)

Lemma mult_0_r `{SemiRing}: forall x, x * 0 == 0.
Proof. intros. rewrite commutativity. apply mult_0_l. Qed.

Lemma inv_involutive `{Group}: forall x, - - x == x.
Proof.
 intros.
 rewrite <- (lunit x) at 2.
 rewrite <- (inv_l (- x)).
 rewrite <- associativity.
 rewrite inv_l.
 rewrite runit.
 reflexivity.
Qed.

Lemma inv_zero `{Group}: - mon_unit == mon_unit.
Proof. intros. rewrite <- (inv_l mon_unit) at 3. rewrite runit. reflexivity. Qed.

Lemma sg_inv_distr `{AbGroup}: forall x y, - (x & y) == - x & - y.
Proof.
 intros.
 rewrite <- (lunit (- x & - y)).
 rewrite <- (inv_l (x & y)).
 rewrite <- associativity.
 rewrite <- associativity.
 rewrite (commutativity (- x) (- y)).
 rewrite (associativity y).
 rewrite inv_r.
 rewrite lunit.
 rewrite inv_r.
 rewrite runit.
 reflexivity.
Qed.

Lemma plus_opp_distr `{Ring}: forall x y, - (x + y) == - x + - y.
Proof. intros. apply sg_inv_distr. Qed.

Lemma ring_plus_left_inj `{Ring}: forall a a' b, a + b == a' + b -> a == a'.
Proof.
 do 11 intro. intro H0.
 rewrite <- (plus_0_r a), <- (plus_0_r a').
 rewrite <- (plus_opp_r b).
 do 2 rewrite associativity.
 rewrite H0. reflexivity.
Qed.

Lemma ring_opp_mult `{Ring}: forall a, -a == -(1) * a.
Proof.
 intros.
 apply ring_plus_left_inj with a.
 rewrite <- (mult_1_l a) at 4.
 rewrite <- distribute_r.
 do 2 rewrite plus_opp_l.
 symmetry. apply mult_0_l.
Qed.

Lemma ring_distr_opp_mult `{Ring}: forall a b, -(a * b) == -a * b.
Proof. intros. rewrite ring_opp_mult, (ring_opp_mult a). apply associativity. Qed.

Lemma ring_opp_mult_opp `{Ring}: forall a b, -a * -b == a * b.
Proof.
 intros.
 rewrite <- ring_distr_opp_mult.
 rewrite commutativity.
 rewrite <- ring_distr_opp_mult.
 rewrite commutativity.
 apply inv_involutive.
Qed.

Lemma opp_0 `{Ring}: -0 == 0. Proof. intros. apply (@inv_zero A _ _ _ _ _). Qed.

Require Import Ring.

Section ring_props. Context `{Ring R}.

  Add Ring R: (Ring_ring_theory R).

  Lemma ring_distr_opp: forall a b, -(a+b) == -a+-b.
  Proof. intros. ring. Qed. (* hm, probably not worth a lemma then *)

  Lemma equal_by_zero_sum: forall x y, x + - y == 0 -> x == y.
  Proof. intros. rewrite <- (plus_0_l y). rewrite <- H0. ring. Qed.

  Lemma plus_reg_l: forall n m p, p + n == p + m -> n == m.
  Proof.
   intros.
   rewrite <- plus_0_l.
   rewrite <- (plus_opp_l p).
   rewrite <- associativity.
   rewrite H0.
   ring.
  Qed.

End ring_props.

Lemma mult_reg_l `{Field R} x: ~ x == 0 -> forall y z,  x * y == x * z -> y == z.
Proof.
 intros.
 rewrite <- mult_1_l.
 rewrite <- (mult_inverse (exist _ x H0)).
 simpl.
 rewrite (commutativity x).
 rewrite <- associativity.
 rewrite H1.
 rewrite associativity.
 rewrite (commutativity _ x).
 rewrite (mult_inverse (exist _ x H0)).
 apply mult_1_l.
Qed.
