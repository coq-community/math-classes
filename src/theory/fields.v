Set Automatic Introduction.

Require
  Field_theory Setoid.
Require Import
  Morphisms Ring Program Field
  abstract_algebra theory.rings.

(* * Field Div *)
Section field_div_properties.
  Context `{Field R} `{div : !FieldDiv R}.

  Lemma field_div_correct x y : x // y = x * //y.
  Proof.
    unfold field_div. unfold field_div_sig. 
    destruct div as [z E]. simpl. auto.
  Qed.

  Global Instance field_div_proper: Proper ((=) ==> (=) ==> (=)) field_div.
  Proof.
    intros x1 y1 E1 x2 y2 E2.
    rewrite (field_div_correct x1 x2). rewrite (field_div_correct y1 y2).
    rewrite E1, E2. reflexivity.
  Qed.

  Lemma field_div_0_l x y : x = 0 → x // y = 0.
  Proof.
    intros E. rewrite E, field_div_correct. rewrite left_absorb. reflexivity.
  Qed.

  Lemma field_div_diag x y : x = `y → x // y = 1.
  Proof.
    intros E. rewrite E, field_div_correct.
    apply mult_inverse.
  Qed.
End field_div_properties.

Global Program Instance default_field_div `{Field R} : FieldDiv R | 10 := λ x y, x * // `y.
Next Obligation. reflexivity. Qed.

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

Section field_is_integral_domain. 
  Context `{Field F}.

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
End field_is_integral_domain. 

(* The non zero elements of a field form a CommutativeMonoid. *)
Section non_zero_elements.
  Context `{Field F}.

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

  Instance: Proper ((=) ==> (=) ==> (=)) nonzero_mult.
  Proof.
    intros [??] [??] E1 [??] [??] E2. 
    unfold equiv, sig_equiv, sig_relation in *. simpl in *.
    rewrite E1, E2.
    reflexivity.
  Qed.

  Instance: Associative nonzero_mult.
  Proof.
    intros [??] [??] [??].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply associativity.
  Qed.

  Instance: Commutative nonzero_mult.
  Proof.
    intros [??] [??].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply commutativity.
  Qed.

  Instance: LeftIdentity nonzero_mult nonzero_one.
  Proof.
    intros [? ?].
    unfold equiv, sig_equiv, sig_relation in *. simpl in *. 
    apply left_identity.
  Qed.

  Instance: RightIdentity nonzero_mult nonzero_one.
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

End non_zero_elements.

Definition stdlib_field_theory F `{Field F} `{∀ x y: F, Decision (x = y)} `{minus : !RingMinus F} :
  Field_theory.field_theory 0 1 ring_plus ring_mult ring_minus
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

Section field_props.
  Context `{Field F}.
  Add Ring R: (stdlib_ring_theory F).

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

  Lemma mult_inv_inj `{!LeftCancellation (=) (λ x, x ≠ 0) ring_mult} x y : //x = //y → x = y.
  Proof with auto.
    intros E.
    unfold equiv, sig_equiv, sig_relation. fold equiv.
    apply (right_cancellation ring_mult (//x)).
      intros G.
      destruct zero_ne_one.
      rewrite <-(rings.mult_0_r (`x)), <-G.
      apply mult_inverse.
    rewrite mult_inverse, E, mult_inverse.
    reflexivity.
  Qed.

  Lemma quotients a c (b d : { q : F | q ≠ 0 }) :
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
  Add Field F: (stdlib_field_theory F).

  Lemma dec_mult_inverse (x: F): x ≠ 0 → x * / x = 1.
  Proof.
   unfold dec_mult_inv. case (decide _). intuition.
   intros. apply (mult_inverse (exist _ x _)).
  Qed.

  Lemma mult_inv_distr (x y : {x : F | x ≠ 0}) : // x * // y = // (x * y).
  Proof with auto.
    eapply (left_cancellation ring_mult (` (x * y))).
      destruct x. destruct y. simpl. apply mult_ne_zero...
    rewrite mult_inverse.
    rewrite <-nonzero_mult_proj_dist.
    assert (`x * `y * (// x * // y) = (`x * // x) * (`y * // y)) as E by ring. 
    rewrite E. repeat rewrite mult_inverse. ring.
  Qed.

  Global Instance: ZeroProduct F.
  Proof with auto.
   intros x y E.
   destruct (decide (x = 0)) as [? | P]...
   rewrite <- (mult_0_r x) in E.
   right. apply (left_cancellation ring_mult x)...
  Qed.

  Lemma dec_mult_inv_0: / 0 = 0.
  Proof. unfold dec_mult_inv. case (decide _); intuition. Qed.

  Lemma dec_mult_inv_distr (x y: F): / (x * y) = / x * / y.
  Proof.
   destruct (decide (x = 0)) as [E|E]. rewrite E, left_absorb, dec_mult_inv_0. ring.
   destruct (decide (y = 0)) as [G|G]. rewrite G, right_absorb, dec_mult_inv_0. ring.
   field. intuition.
  Qed.

  Lemma equal_by_one_quotient (x y: F): x */ y = 1 → x = y.
  Proof with auto; try field; auto.
   intro E.
   destruct (decide (y = 0)).
    exfalso. apply zero_ne_one.
    rewrite <- E, e0, dec_mult_inv_0...
   transitivity (1 * y)...
   rewrite <- E...
  Qed.

  Lemma mult_inv_nonzero x : // x ≠ 0.
  Proof with auto.
    intro E.
    apply zero_ne_one. 
    rewrite <-(mult_inverse x), E. ring.
  Qed.

  Lemma dec_mult_inv_nonzero x : x ≠ 0 → / x ≠ 0.
  Proof with auto.
    intros E1 E2.
    apply zero_ne_one. 
    rewrite <-(dec_mult_inverse x), E2... ring.
  Qed.

  Lemma dec_mult_inv_inj x y : /x = /y → x = y.
  Proof with try solve [intuition].
    intros E.
    destruct (decide (x = 0)) as [E2|E2].
     rewrite E2 in *. rewrite dec_mult_inv_0 in E.
     apply stable. intro. apply (dec_mult_inv_nonzero y)...
    apply (right_cancellation ring_mult (/x)).
     apply dec_mult_inv_nonzero...
    rewrite dec_mult_inverse, E, dec_mult_inverse...
    intros E3. rewrite E3, dec_mult_inv_0 in E. 
    apply (dec_mult_inv_nonzero x)...
  Qed.

  Lemma dec_mult_inv_involutive x : / / x = x.
  Proof with auto.
    destruct (decide (x = 0)) as [E|E].
    rewrite E. do 2 rewrite dec_mult_inv_0. reflexivity.
    apply (right_cancellation ring_mult (/x)).
     apply dec_mult_inv_nonzero...
    rewrite dec_mult_inverse...
    rewrite commutativity, dec_mult_inverse. reflexivity.
    apply dec_mult_inv_nonzero...
  Qed.
End field_props.

Section morphisms.
  Context `{Field F} `{Field F2} `{!Ring_Morphism (f : F → F2)}.

  Context `{∀ x y: F, Decision (x = y)} `{∀ x y: F2, Decision (x = y)}.
   
  Lemma preserves_dec_mult_inv `{!Injective f} x : f (/x) = /(f x).
  Proof with auto.
    case (decide (x = 0)) as [E | E].
    rewrite E, dec_mult_inv_0, preserves_0, dec_mult_inv_0. reflexivity.
    apply (right_cancellation ring_mult (f x)).
      apply injective_not_0...
    rewrite <-preserves_mult.
    rewrite commutativity, dec_mult_inverse...
    rewrite commutativity, dec_mult_inverse.
    apply preserves_1.
    apply injective_not_0...
  Qed.
End morphisms.

Section from_stdlib_field_theory.

  Context `(H: @field_theory F zero one pl mu mi op div rinv e)
    `{!@Setoid F e}
    `{!Proper (e ==> e ==> e) pl}
    `{!Proper (e ==> e ==> e) mu}
    `{!Proper (e ==> e) rinv}
    `{!Proper (e ==> e) op}.

  Add Field F2 : H.

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

End from_stdlib_field_theory.
