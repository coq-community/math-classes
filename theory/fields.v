Set Automatic Introduction.

Require
  Field_theory.
Require Import
  Morphisms
  abstract_algebra theory.rings.

Section dec_mult_inv.

  Context
    `{e: Equiv A} `{RingZero A} `{!MultInv A} `{forall x y: A, Decision (x == y)}
    `{!Equivalence e} `{mult_inv_proper: !Proper (sig_relation equiv _ ==> equiv) mult_inv}.

  Global Instance dec_mult_inv_proper: Proper (e ==> e) dec_mult_inv.
  Proof with auto.
   unfold dec_mult_inv. intros x y E.
   destruct (decide (x == 0)) as [? | P]; destruct (decide (y == 0)) as [? | Q].
      reflexivity.
     exfalso. apply Q. rewrite <- E...
    exfalso. apply P. rewrite E...
   apply mult_inv_proper...
  Qed.

End dec_mult_inv.

Section field_props. Context `{Field F} `{forall x y: F, Decision (x == y)}.

  Lemma mult_inverse': forall x p, x * // exist _ x p == 1.
  Proof. intros. apply (mult_inverse (exist _ _ _)). Qed.

  Definition stdlib_field_theory:
    Field_theory.field_theory 0 1 ring_plus ring_mult (fun x y => x + - y)
      group_inv (fun x y => x * / y) dec_mult_inv equiv.
  Proof.
   intros.
   constructor.
      apply (theory.rings.stdlib_ring_theory _).
     intro.
     apply field_0neq1.
     symmetry.
     assumption.
    reflexivity.
   intros.
   rewrite commutativity.
   unfold dec_mult_inv.
   destruct (decide (p == 0)). intuition.
   apply mult_inverse'.
  Qed.

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
   destruct (decide (x == 0)) as [? | P]. intuition.
   rewrite <- (mult_0_r x) in E.
   right. apply (mult_reg_l x P _ _ E).
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
  Proof with auto.
   intro E.
   pose proof dec_mult_inv_proper.
   assert (x * / y * y == 1 * y).
    rewrite E.
    reflexivity.
   rewrite <- associativity in H2.
   rewrite (commutativity (/ y)) in H2.
   destruct (decide (y == 0)).
    exfalso.
    rewrite e0 in E.
    rewrite inv_0 in E.
    rewrite mult_0_r in E.
    apply field_0neq1...
   rewrite dec_mult_inverse in H2...
   rewrite mult_1_r, mult_1_l in H2...
  Qed. (* Ugly due to Coq bugs *)

End field_props.

Implicit Arguments stdlib_field_theory [[e] [plus0] [mult0] [inv] [zero] [one] [mult_inv0] [H] [H0]].
