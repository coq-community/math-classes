Set Automatic Introduction.

Require
  Field_theory.
Require Import
  Morphisms Ring Program Field
  abstract_algebra theory.rings.

Section dec_mult_inv.

  Context
    `{e: Equiv A} `{RingZero A} `{mi: !MultInv A} `{∀ x y: A, Decision (x = y)}
    `{!Equivalence e} `{mult_inv_proper: !Proper (sig_relation equiv _ ==> equiv) mi}.

  Global Instance dec_mult_inv_proper: Proper (e ==> e) dec_mult_inv.
  Proof with auto.
   unfold dec_mult_inv. intros x y E.
   case (decide _); case (decide _).
      reflexivity.
     intros P Q. exfalso. apply P. rewrite <- E...
    intros Q P. exfalso. apply P. rewrite E...
   intros; eapply mult_inv_proper...
  Qed.

End dec_mult_inv.

Section field_props. 
  Context `{Field F}.
  Add Ring R: (stdlib_ring_theory F).

  Lemma mult_inverse': ∀ x p, x * // exist _ x p = 1.
  Proof. intros. apply (mult_inverse (exist _ _ _)). Qed.

  Instance: NoZeroDivisors F.
  Proof.
   intros x [x_nonzero [y [y_nonzero E]]].
   apply x_nonzero.
   rewrite <- mult_1_r. rewrite <- (mult_inverse' y y_nonzero).
   rewrite associativity, E. apply left_absorb.
  Qed.

  Global Instance: IntegralDomain F.

  (* The non zero elements of a field form a CommutativeMonoid. *)
  Global Program Instance nonzero_one: RingOne { q : F | q ≠ 0 } := exist (λ x, x ≠ 0) 1 _.
  Next Obligation. intro E. symmetry in E. apply (field_0neq1 E). Qed.

  (* I am not using Program because now we can easily refer to this proof obligation *) 
  (* TODO: Use a type class for NonZero to clean up this ugly Lemma *)
  Lemma mult_ne_zero_sig (x y : {q : F | q ≠ 0}) : (λ x, x ≠ 0) (`x * `y).
  Proof with auto.
    destruct x. destruct y. simpl. 
    apply mult_ne_zero...
  Qed.
 
  Global Instance nonzero_mult: RingMult { x : F | x ≠ 0 } := λ x y, 
    exist (λ x, x ≠ 0) (`x *  `y) (mult_ne_zero_sig x y).

  Global Instance: Proper ((=) ==> (=) ==> (=)) nonzero_mult.
  Proof.
    intros [??] [??] E1 [??] [??] E2. 
    unfold equiv, sig_equiv, sig_relation in *. simpl in *.
    rewrite E1, E2.
    reflexivity.
  Qed.

  Global Instance: Associative nonzero_mult.
  Proof.
    intros [??] [??] [??].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply associativity.
  Qed.

  Global Instance: Commutative nonzero_mult.
  Proof.
    intros [??] [??].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply commutativity.
  Qed.

  Global Instance: LeftIdentity nonzero_mult nonzero_one.
  Proof.
    intros [? ?].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply left_identity.
  Qed.

  Global Instance: RightIdentity nonzero_mult nonzero_one.
  Proof.
    intros [? ?].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply right_identity.
  Qed.

  Global Instance: CommutativeMonoid { x : F | x ≠ 0 } (op:=nonzero_mult) (unit:=nonzero_one).
  Proof. repeat (split; try apply _). Qed.

  Lemma nonzero_mult_proj_dist (x y : {x : F | x ≠ 0}) : `x * `y = ` (x * y).
  Proof. reflexivity. Qed.

  Lemma nonzero_mult_proj_one (x y : {x : F | x ≠ 0}) : `1 = 1.
  Proof. reflexivity. Qed.

  Lemma equal_quotients (a c: F) b d: a * ` d = c * ` b ↔ a *// b = c *// d.
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

  Lemma quotients a c b d :
    a * //b + c * //d = (a * `d + c * `b) * // (b * d).
  Proof with auto.
    assert (a * // b = (a * `d) * // exist _ (`b * `d) (mult_ne_zero_sig b d)) as E1.
      apply equal_quotients. simpl. ring.
    assert (c * // d = (`b * c) * // exist _ (`b * `d) (mult_ne_zero_sig b d)) as E2.
      apply equal_quotients. simpl. ring.
    rewrite E1, E2.
    unfold "*" at 10. unfold nonzero_mult. ring.
  Qed.

  Context `{∀ x y: F, Decision (x = y)}.

  Definition stdlib_field_theory:
    Field_theory.field_theory 0 1 ring_plus ring_mult (λ x y, x + - y)
      group_inv (λ x y, x * / y) dec_mult_inv equiv.
  Proof with auto.
   intros.
   constructor.
      apply (theory.rings.stdlib_ring_theory _).
     intro. apply field_0neq1. symmetry...
    reflexivity.
   intros.
   rewrite commutativity.
   unfold dec_mult_inv.
   case (decide _). intuition.
   apply mult_inverse'.
  Qed.

  Add Field F: stdlib_field_theory.

  Lemma dec_mult_inverse (x: F): x ≠ 0 → x * / x = 1.
  Proof.
   unfold dec_mult_inv. case (decide _). intuition.
   intros. apply (mult_inverse (exist _ x _)).
  Qed.

  Lemma mult_inv_distr (x y : {x : F | x ≠ 0}) : // x * // y = // (x * y).
  Proof with auto.
    apply (theory.rings.mult_injective (` (x * y)))...
      destruct x. destruct y. simpl. apply mult_ne_zero...
    rewrite mult_inverse.
    rewrite <-nonzero_mult_proj_dist.
    assert (`x * `y * (// x * // y) = (`x * // x) * (`y * // y)) as E by ring. 
    rewrite E. repeat rewrite mult_inverse. ring.
  Qed.

  Global Instance: ZeroProduct F.
  Proof.
   intros x y E.
   destruct (decide (x = 0)) as [? | P]. intuition.
   rewrite <- (mult_0_r x) in E.
   right.
   pose proof (mult_injective x P).
   apply (injective (ring_mult x)).
   assumption.
  Qed.

  Lemma inv_0: / 0 = 0.
  Proof. unfold dec_mult_inv. case (decide _); intuition. Qed.

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

Module from_stdlib_field_theory.
 (* Without this module wrapping, the [Add Ring] below gives an error about some
  internal name conflict. Todo: report. *)
Section contents.

  Context `{H: @field_theory F zero one pl mu mi op div rinv e}
    `{!@Setoid F e}
    `{!Proper (e ==> e ==> e) pl}
    `{!Proper (e ==> e ==> e) mu}
    `{!Proper (e ==> e) rinv}
    `{!Proper (e ==> e) op}.

  Add Field F: H.

  Definition from_stdlib_field_theory: @Field F e pl mu zero one op (λ x, rinv (proj1_sig x)).
  Proof.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, group_inv; try field.
     destruct H.
     apply F_1_neq_0.
     symmetry.
     assumption.
    unfold sig_relation in H1.
    simpl in *.
    rewrite H1.
    reflexivity.
   destruct x.
   simpl.
   unfold mult_inv.
   simpl.
   destruct H.
   unfold ring_mult.
   assert (e (mu x (rinv x)) (mu (rinv x) x)) by ring.
   rewrite H1.
   auto.
  Qed.

End contents.
End from_stdlib_field_theory.
