Set Automatic Introduction.

Require Import Morphisms Structures RingOps FieldOps.

(* various derived identities: *)

Lemma mult_0_r `{SemiRing} x: x * 0 == 0.
Proof. rewrite commutativity. apply mult_0_l. Qed.

Lemma inv_involutive `{Group} x: - - x == x.
Proof.
 rewrite <- (monoid_lunit x) at 2.
 rewrite <- (inv_l (- x)).
 rewrite <- associativity.
 rewrite inv_l.
 rewrite monoid_runit.
 reflexivity.
Qed.

Instance group_inv_injective `{Group}: Injective group_inv.
Proof. intros x y E. rewrite <- (inv_involutive x), <- (inv_involutive y), E. reflexivity. Qed.

Lemma inv_zero `{Group}: - mon_unit == mon_unit.
Proof. rewrite <- (inv_l mon_unit) at 3. rewrite monoid_runit. reflexivity. Qed.

Lemma sg_inv_distr `{AbGroup} x y: - (x & y) == - x & - y.
Proof.
 rewrite <- (monoid_lunit (- x & - y)).
 rewrite <- (inv_l (x & y)).
 rewrite <- associativity.
 rewrite <- associativity.
 rewrite (commutativity (- x) (- y)).
 rewrite (associativity y).
 rewrite inv_r.
 rewrite monoid_lunit.
 rewrite inv_r.
 rewrite monoid_runit.
 reflexivity.
Qed.

Require Import Ring.

Section ring_props. Context `{Ring R}.

  Add Ring R: (Ring_ring_theory R).

  Lemma opp_swap x y: x + - y == - (y + - x).
  Proof. ring. Qed.

  Lemma plus_opp_distr x y: - (x + y) == - x + - y.
  Proof. apply sg_inv_distr. Qed.

  Lemma ring_plus_left_inj a a' b: a + b == a' + b -> a == a'.
  Proof.
   intro E.
   rewrite <- (plus_0_r a), <- (plus_0_r a').
   rewrite <- (plus_opp_r b).
   do 2 rewrite associativity.
   rewrite E. reflexivity.
  Qed.

  Lemma ring_opp_mult a: -a == -(1) * a.
  Proof.
   apply ring_plus_left_inj with a.
   rewrite <- (mult_1_l a) at 4.
   rewrite <- distribute_r.
   do 2 rewrite plus_opp_l.
   symmetry. apply mult_0_l.
  Qed.

  Lemma ring_distr_opp_mult a b: -(a * b) == -a * b.
  Proof. rewrite ring_opp_mult, (ring_opp_mult a). apply associativity. Qed.

  Lemma ring_opp_mult_opp a b: -a * -b == a * b.
  Proof.
   rewrite <- ring_distr_opp_mult.
   rewrite commutativity.
   rewrite <- ring_distr_opp_mult.
   rewrite commutativity.
   apply inv_involutive.
  Qed.

  Lemma opp_0: -0 == 0. Proof. apply (@inv_zero R _ _ _ _ _). Qed.

  Lemma ring_distr_opp a b: -(a+b) == -a+-b.
  Proof. ring. Qed. (* hm, probably not worth a lemma then *)

  Lemma equal_by_zero_sum x y: x + - y == 0 -> x == y.
  Proof. intro E. rewrite <- (plus_0_l y). rewrite <- E. ring. Qed.

  Lemma plus_reg_l n m p: p + n == p + m -> n == m.
  Proof.
   intro E.
   rewrite <- plus_0_l.
   rewrite <- (plus_opp_l p).
   rewrite <- associativity.
   rewrite E.
   ring.
  Qed.

End ring_props.

Section field_props. Context `{Field F} `{forall x y: F, Decision (x == y)}.

  Lemma mult_reg_l  x: ~ x == 0 -> forall y z: F, x * y == x * z -> y == z.
  Proof.
   intros E y z G.
   rewrite <- mult_1_l.
   rewrite <- (mult_inverse (exist _ x E)).
   simpl.
   rewrite (commutativity x).
   rewrite <- associativity.
   rewrite G.
   rewrite associativity.
   rewrite (commutativity _ x).
   rewrite (mult_inverse (exist _ x E)).
   apply mult_1_l.
  Qed.

  Global Instance: ZeroProduct F.
  Proof.
   intros x y E.
   destruct (decide (x == 0)). intuition.
   rewrite <- (mult_0_r x) in E.
   right. apply (mult_reg_l x f _ _ E).
  Qed.

  Lemma dec_mult_inverse (x: F): ~ x == 0 -> x * / x == 1.
  Proof.
   unfold dec_mult_inv. destruct decide. intuition.
   intros. apply (mult_inverse (exist _ x _)).
  Qed.

  Lemma inv_0: / 0 == 0.
  Proof. unfold dec_mult_inv. destruct decide; intuition. Qed.

  Lemma dec_mult_inv_distr (x y: F): / (x * y) == / x * / y.
  Proof with auto.
   pose proof (_: Proper (equiv ==> equiv) dec_mult_inv).
   destruct (decide (x == 0)) as [E|E]. rewrite E, mult_0_l, inv_0, mult_0_l. reflexivity.
   destruct (decide (y == 0)) as [G|G]. rewrite G, mult_0_r, inv_0, mult_0_r. reflexivity.
   assert (~ x * y == 0). intro U. destruct (zero_product _ _ U); intuition.
   apply mult_reg_l with (x * y)...
   rewrite dec_mult_inverse...
   rewrite (commutativity (/x)).
   rewrite <- associativity.
   rewrite (associativity y).
   rewrite dec_mult_inverse...
   rewrite mult_1_l.
   rewrite dec_mult_inverse...
   reflexivity.
  Qed.

  Lemma equal_by_one_quotient (x y: F): x */ y == 1 -> x == y.
  Proof.
   intros.
   pose proof dec_mult_inv_proper.
   assert (x * / y * y == 1 * y).
    rewrite H1.
    reflexivity.
   rewrite <- associativity in H3.
   rewrite (commutativity (/ y)) in H3.
   destruct (decide (y == 0)).
    exfalso.
    rewrite e0 in H1.
    rewrite inv_0 in H1.
    rewrite mult_0_r in H1.
    apply field_0neq1.
    assumption.
   rewrite dec_mult_inverse in H3; [| assumption].
   rewrite mult_1_r, mult_1_l in H3.
   assumption.
  Qed.

End field_props.
