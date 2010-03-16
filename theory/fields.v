Set Automatic Introduction.

Require
  Field_theory.
Require Import
  Morphisms Ring Program Field
  abstract_algebra theory.rings.

Section dec_mult_inv.

  Context
    `{e: Equiv A} `{RingZero A} `{mi: !MultInv A} `{Π x y: A, Decision (x = y)}
    `{!Equivalence e} `{mult_inv_proper: !Proper (sig_relation equiv _ ==> equiv) mi}.

  Global Instance dec_mult_inv_proper: Proper (e ==> e) dec_mult_inv.
  Proof with auto.
   unfold dec_mult_inv. intros x y E.
   destruct decide as [? | P]; destruct decide as [? | Q].
      reflexivity.
     exfalso. apply Q. rewrite <- E...
    exfalso. apply P. rewrite E...
   apply mult_inv_proper...
  Qed.

End dec_mult_inv.

Section field_props. Context `{Field F}.

  Lemma mult_inverse': Π x p, x * // exist _ x p = 1.
  Proof. intros. apply (mult_inverse (exist _ _ _)). Qed.

  Instance: NoZeroDivisors F.
  Proof.
   intros x [x_nonzero [y [y_nonzero E]]].
   apply x_nonzero.
   rewrite <- mult_1_r. rewrite <- (mult_inverse' y y_nonzero).
   rewrite associativity, E. apply left_absorb.
  Qed.

  Global Instance: IntegralDomain F.

  Add Ring R: (stdlib_ring_theory F).

  Lemma equal_quotients (a c: F) b d: a * ` d = c * ` b <-> a *// b = c *// d.
  Proof with try ring.
   split; intro E.
    transitivity (1 * (a * // b))...
    rewrite <- (mult_inverse d).
    transitivity (// d * (a * `d) * // b)...
    rewrite E.
    transitivity (// d * c * (`b * // b))...
    rewrite mult_inverse...
   transitivity (a * `d * 1)...
   rewrite <- (mult_inverse b).
   transitivity (a * // b * `d * ` b)...
   rewrite E.
   transitivity (c * (`d * // d) * `b)...
   rewrite mult_inverse...
  Qed. (* todo: should be cleanable *)

  Context `{Π x y: F, Decision (x = y)}.

  Definition stdlib_field_theory:
    Field_theory.field_theory 0 1 ring_plus ring_mult (λ x y => x + - y)
      group_inv (λ x y => x * / y) dec_mult_inv equiv.
  Proof with auto.
   intros.
   constructor.
      apply (theory.rings.stdlib_ring_theory _).
     intro. apply field_0neq1. symmetry...
    reflexivity.
   intros.
   rewrite commutativity.
   unfold dec_mult_inv.
   destruct decide. intuition.
   apply mult_inverse'.
  Qed.

  Add Field F: stdlib_field_theory.

  Lemma dec_mult_inverse (x: F): x ≠ 0 → x * / x = 1.
  Proof.
   unfold dec_mult_inv. destruct decide. intuition.
   intros. apply (mult_inverse (exist _ x _)).
  Qed.

  Global Instance: ZeroProduct F.
  Proof.
   intros x y E.
   destruct (decide (x = 0)) as [? | P]. intuition.
   rewrite <- (mult_0_r x) in E.
   right. apply (mult_injective x P _ _ E).
  Qed.

  Lemma inv_0: / 0 = 0.
  Proof. unfold dec_mult_inv. destruct decide; intuition. Qed.

  Lemma dec_mult_inv_distr (x y: F): / (x * y) = / x * / y.
  Proof.
   destruct (decide (x = 0)) as [E|E]. rewrite E, left_absorb, inv_0. ring.
   destruct (decide (y = 0)) as [G|G]. rewrite G, right_absorb, inv_0. ring.
   field. intuition.
  Qed.

  Lemma equal_by_one_quotient (x y: F): x */ y = 1 → x = y.
  Proof with auto; try field; auto.
   intro E.
   destruct (decide (y = 0)).
    exfalso. apply field_0neq1.
    rewrite <- E, e0, inv_0...
   transitivity (1 * y)...
   rewrite <- E...
  Qed.

End field_props.

Implicit Arguments stdlib_field_theory [[e] [plus0] [mult0] [inv] [zero] [one] [mult_inv0] [H] [H0]].
