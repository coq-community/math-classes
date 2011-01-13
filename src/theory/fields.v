Require
  Field_theory Setoid.
Require Import
  Morphisms Ring Program Field
  abstract_algebra theory.rings.

Section field_properties. 
  Context `{Field F} `{div : !FieldDiv F}.
  Add Ring R: (stdlib_ring_theory F).

  Lemma mult_inverse_alt (x : F) (P : x ≠ 0) : x * // exist _ x P = 1.
  Proof. 
    rewrite <-(mult_inverse (exist _ x P)). reflexivity. 
  Qed.

  Instance: NoZeroDivisors F.
  Proof.
   intros x [x_nonzero [y [y_nonzero E]]].
   apply x_nonzero.
   rewrite <- mult_1_r. rewrite <- (mult_inverse_alt y y_nonzero).
   rewrite associativity, E. ring.
  Qed.

  Global Instance: IntegralDomain F.

  Lemma field_div_0_l x y : x = 0 → x // y = 0.
  Proof.
    intros E. rewrite E. apply left_absorb.
  Qed.

  Lemma field_div_diag x y : x = `y → x // y = 1.
  Proof.
    intros E. rewrite E. apply mult_inverse.
  Qed.

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

  Lemma mult_inv_inj `{∀ z, NeZero z → LeftCancellation ring_mult z} x y : //x = //y → x = y.
  Proof with auto.
    intros E.
    unfold equiv, sig_equiv, sig_relation. fold equiv.
    apply (left_cancellation_ne_0 ring_mult (//x)).
     intros G.
     destruct (ne_zero 1).
     rewrite <-(rings.mult_0_r (`x)), <-G.
     symmetry. apply mult_inverse.
    rewrite commutativity, mult_inverse. 
    rewrite E, commutativity, mult_inverse.
    reflexivity.
  Qed.

  Lemma mult_inv_distr_alt `{∀ z, NeZero z → LeftCancellation ring_mult z} x (Px : x ≠ 0) y (Py : y ≠ 0) (Pxy : x * y ≠ 0) : 
    // (exist _ (x * y) Pxy) = // (exist _ x Px) * // (exist _ y Py).
  Proof with auto; try ring.
    apply (left_cancellation_ne_0 ring_mult (x * y))...
    transitivity ((x * // (exist _ x Px)) *  (y * // (exist _ y Py)))...
    transitivity ((x * y) * // (exist _ (x * y) Pxy))...
    do 3 rewrite mult_inverse_alt...
  Qed.

  (* Properties of fields with decidable equality *)
  Context `{∀ x y: F, Decision (x = y)} `{dec_inv : !DecMultInv F}.

  Global Instance: ZeroProduct F.
  Proof with auto.
   intros x y E.
   destruct (decide (x = 0)) as [? | P]...
   rewrite <- (mult_0_r x) in E.
   right. apply (left_cancellation_ne_0 ring_mult x)...
  Qed.

  Lemma mult_inv_nonzero x : // x ≠ 0.
  Proof with auto.
    intro E.
    apply (ne_zero 1). 
    rewrite <-(mult_inverse x), E. ring.
  Qed.

  Lemma dec_mult_inverse (x: F) : x ≠ 0 → x * / x = 1.
  Proof.
    intro E. 
    unfold dec_mult_inv, dec_mult_inv_sig. 
    destruct dec_inv as [z [E1 E2]]. auto.
  Qed.

  Lemma dec_mult_inv_correct (x : F) (P : x ≠ 0) : /x = // (exist _ x P).
  Proof with auto.
    apply (left_cancellation_ne_0 ring_mult x)...
    rewrite dec_mult_inverse...
    symmetry. apply mult_inverse_alt.
  Qed.

  Lemma dec_mult_inv_0: / 0 = 0.
  Proof. 
    unfold dec_mult_inv, dec_mult_inv_sig. 
    destruct dec_inv as [z [E1 E2]]. apply E2. reflexivity.
  Qed.

  Lemma dec_mult_inv_1: / 1 = 1.
  Proof. 
    unfold dec_mult_inv, dec_mult_inv_sig. 
    destruct dec_inv as [z [E1 E2]]. simpl.
    rewrite <-E1. ring.
    apply (ne_zero _).
  Qed.

  Global Instance dec_mult_inv_proper: Proper ((=) ==> (=)) dec_mult_inv.
  Proof with auto.
    intros x1 x2 E.
    case (decide (x1 = 0)); intros E1; case (decide (x2 = 0)); intros E2.
       unfold dec_mult_inv, dec_mult_inv_sig.
       destruct (dec_inv x1) as [z1 [? Ez1]], (dec_inv x2) as [z2 [? Ez2]].
       simpl. rewrite Ez1, Ez2... reflexivity.
      destruct E2. rewrite <- E...
     destruct E1. rewrite E...
    apply (left_cancellation_ne_0 ring_mult x1)...
    rewrite dec_mult_inverse, E, dec_mult_inverse...
    reflexivity.
  Qed.

  Lemma dec_mult_inv_distr (x y: F): / (x * y) = / x * / y.
  Proof with auto.
    case (decide (x = 0)); intros E1. rewrite E1, left_absorb, dec_mult_inv_0. ring.
    case (decide (y = 0)); intros E2. rewrite E2, right_absorb, dec_mult_inv_0. ring.
    assert (x * y ≠ 0) as E3. apply mult_ne_zero...
    rewrite (dec_mult_inv_correct _ E1), (dec_mult_inv_correct _ E2), (dec_mult_inv_correct _ E3).
    apply mult_inv_distr_alt.
  Qed.

  Lemma equal_by_one_quotient (x y: F): x */ y = 1 → x = y.
  Proof with auto; try ring.
   intro E1.
   case (decide (y = 0)); intros E2.
    exfalso. apply (ne_zero 1).
    rewrite <- E1, E2, dec_mult_inv_0...
   transitivity ((y * /y) * x). rewrite dec_mult_inverse...
   transitivity ((x * /y) * y)... rewrite E1...
  Qed.

  Lemma dec_mult_inv_nonzero x : x ≠ 0 → / x ≠ 0.
  Proof with auto.
    intros E1 E2.
    apply (ne_zero 1). 
    rewrite <-(dec_mult_inverse x), E2... ring.
  Qed.

  Lemma dec_mult_inv_inj x y : /x = /y → x = y.
  Proof with try solve [intuition].
    intros E.
    destruct (decide (x = 0)) as [E2|E2].
     rewrite E2 in *. rewrite dec_mult_inv_0 in E.
     apply stable. intro. apply (dec_mult_inv_nonzero y)...
    apply (right_cancellation_ne_0 ring_mult (/x)).
     apply dec_mult_inv_nonzero...
    rewrite dec_mult_inverse, E, dec_mult_inverse...
    intros E3. rewrite E3, dec_mult_inv_0 in E. 
    apply (dec_mult_inv_nonzero x)...
  Qed.

  Lemma dec_mult_inv_involutive x : / / x = x.
  Proof with auto.
    destruct (decide (x = 0)) as [E|E].
    rewrite E. do 2 rewrite dec_mult_inv_0. reflexivity.
    apply (right_cancellation_ne_0 ring_mult (/x)).
     apply dec_mult_inv_nonzero...
    rewrite dec_mult_inverse...
    rewrite commutativity, dec_mult_inverse. reflexivity.
    apply dec_mult_inv_nonzero...
  Qed.

  Lemma equal_dec_quotients (a b c d : F) : b ≠ 0 → d ≠ 0 → (a * d = c * b ↔ a * /b = c * /d).
  Proof with trivial; try ring.
   split; intro E.
    apply (right_cancellation_ne_0 ring_mult b)...
    apply (right_cancellation_ne_0 ring_mult d)...
    transitivity (a * d * (b * /b))...
    transitivity (c * b * (d * /d))...
    rewrite E, dec_mult_inverse, dec_mult_inverse...
   transitivity (a * d * 1)...
   rewrite <-(dec_mult_inverse b)...
   transitivity (a * / b * d * b)...
   rewrite E.
   transitivity (c * (d * / d) * b)...
   rewrite dec_mult_inverse...
  Qed.

  Lemma dec_quotients (a c b d : F) : b ≠ 0 → d ≠ 0 → a * /b + c * /d = (a * d + c * b) * / (b * d).
  Proof with auto.
    intros A B.
    assert (a * / b = (a * d) * / (b * d)) as E1.
     apply ->equal_dec_quotients...
      ring.
     intros G. destruct (zero_product b d)...
    assert (c * / d = (b * c) * / (b * d)) as E2.
     apply ->equal_dec_quotients...
      ring.
     intros G. destruct (zero_product b d)...
    rewrite E1, E2. ring.
  Qed.

  Lemma dec_mult_inv_swap_l x y: x * /y = /(/x * y). 
  Proof. 
    rewrite dec_mult_inv_distr, dec_mult_inv_involutive.
    ring.
  Qed.

  Lemma dec_mult_inv_swap_r x y: /x * y = /(x * /y). 
  Proof. 
    rewrite dec_mult_inv_distr, dec_mult_inv_involutive.
    ring.
  Qed.
End field_properties.

Definition stdlib_field_theory F `{Field F} `{!DecMultInv F} :
  Field_theory.field_theory 0 1 ring_plus ring_mult (λ x y, x - y) group_inv (λ x y, x / y) dec_mult_inv (=).
Proof with auto.
  intros.
  constructor.
     apply (theory.rings.stdlib_ring_theory _).
    apply field_0neq1.
   reflexivity.
  intros.
  rewrite commutativity. apply dec_mult_inverse...
Qed.

Section morphisms.
  Context `{Field F1} `{Field F2} `{!Ring_Morphism (f : F1 → F2)} `{!DecMultInv F1} `{!DecMultInv F2}.

  Context `{∀ x y: F1, Decision (x = y)} `{∀ x y: F2, Decision (x = y)}.
   
  Lemma preserves_dec_mult_inv `{!Injective f} x : f (/x) = /(f x).
  Proof with auto.
    case (decide (x = 0)) as [E | E].
    rewrite E, dec_mult_inv_0, preserves_0, dec_mult_inv_0. reflexivity.
    apply (right_cancellation_ne_0 ring_mult (f x)).
      apply injective_not_0...
    rewrite <-preserves_mult.
    rewrite commutativity, dec_mult_inverse...
    rewrite commutativity, dec_mult_inverse.
    apply preserves_1.
    apply injective_not_0...
  Qed.
End morphisms.

(* The non zero elements of a field form a CommutativeMonoid. *)
Section non_zero_elements.
  Context `{Field F}.
  Add Ring R2 : (stdlib_ring_theory F).

  Global Program Instance nonzero_one: RingOne { q : F | q ≠ 0 } := exist (λ x, x ≠ 0) 1 _.
  Next Obligation. intro E. apply field_0neq1. assumption. Qed.

  (* I am not using Program because now we can easily refer to this proof obligation *) 
  Lemma mult_ne_zero_sig (x y : {q : F | q ≠ 0}) : (λ x, x ≠ 0) (`x * `y).
  Proof. destruct x, y. apply mult_ne_zero; assumption. Qed.
 
  Global Instance nonzero_mult: RingMult { x : F | x ≠ 0 } := λ x y, 
    exist (λ x, x ≠ 0) (`x *  `y) (mult_ne_zero_sig x y).

  Ltac solve := repeat intro; unfold equiv, sig_equiv, sig_relation in *; simpl in *.

  Instance: Proper ((=) ==> (=) ==> (=)) nonzero_mult.
  Proof.
    intros [??] [??] E1 [??] [??] E2. solve. 
    rewrite E1, E2. reflexivity.
  Qed.

  Instance: Associative nonzero_mult.
  Proof. solve. apply associativity. Qed.

  Instance: Commutative nonzero_mult.
  Proof. solve. apply commutativity. Qed.

  Instance: LeftIdentity nonzero_mult nonzero_one.
  Proof. solve. apply left_identity. Qed.

  Instance: RightIdentity nonzero_mult nonzero_one.
  Proof. solve. apply right_identity. Qed.

  Global Instance: CommutativeMonoid { x : F | x ≠ 0 } (op:=nonzero_mult) (unit:=nonzero_one).
  Proof. repeat (split; try apply _). Qed.

  Lemma nonzero_mult_proj_dist (x y : {x : F | x ≠ 0}) : `x * `y = ` (x * y).
  Proof. reflexivity. Qed.

  Lemma nonzero_mult_proj_one (x y : {x : F | x ≠ 0}) : `1 = 1.
  Proof. reflexivity. Qed.

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

  Lemma mult_inv_distr `{∀ z, NeZero z → LeftCancellation ring_mult z} (x y : {x : F | x ≠ 0}) : 
    // (x * y) = // x * // y.
  Proof. destruct x, y. apply mult_inv_distr_alt. Qed. 

End non_zero_elements.

Section from_stdlib_field_theory.
  Context `(ftheory : @field_theory F zero one pl mu mi op div rinv e)
    `{!@Setoid F e}
    `{!Proper (e ==> e ==> e) pl}
    `{!Proper (e ==> e ==> e) mu}
    `{!Proper (e ==> e) rinv}
    `{!Proper (e ==> e) op}.

  Add Field F2 : ftheory.

  Definition from_stdlib_field_theory: @Field F e pl mu zero one op (λ x, rinv (proj1_sig x)).
  Proof with auto.
   destruct ftheory.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, group_inv; try field...
   destruct x as [x Ex].
   unfold mult_inv, ring_mult.
   simpl.
   assert (e (mu x (rinv x)) (mu (rinv x) x)) as E by ring.
   rewrite E...
  Qed.
End from_stdlib_field_theory.

Program Instance dec_mult_inv_default `{Field F} `{∀ x y: F, Decision (equiv x y)} : DecMultInv F | 10
  := λ x, exist _ (if decide (equiv x 0) then 0 else // x) _.
Next Obligation.
  case (decide _); split; try solve [intuition].
  intros E. apply mult_inverse_alt.
Qed.
