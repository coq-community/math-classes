Require
  Field_theory Setoid.
Require Import
  Morphisms Ring Program Field
  abstract_algebra theory.rings.

Section field_properties. 
  Context `{Field F}.
  Add Ring R: (stdlib_ring_theory F).

  Global Instance: ∀ (x : F ₀), PropHolds (`x ≠ 0).
  Proof. now intros [x Px]. Qed.

  Global Instance mult_inv_nonzero x : PropHolds (// x ≠ 0).
  Proof.
    intro E.
    apply (ne_0 1). 
    rewrite <-(mult_inverse x), E. ring.
  Qed.

  Lemma mult_inverse_alt (x : F) (Px : x ≠ 0) : x * // x↾Px = 1.
  Proof. now rewrite <-(mult_inverse (x↾Px)). Qed.

  Instance: NoZeroDivisors F.
  Proof.
   intros x [x_nonzero [y [y_nonzero E]]].
   apply x_nonzero.
   rewrite <- mult_1_r. rewrite <- (mult_inverse_alt y y_nonzero).
   rewrite associativity, E. ring.
  Qed.

  Global Instance: IntegralDomain F.

  Lemma field_div_0_l x y : x = 0 → x // y = 0.
  Proof. intros E. rewrite E. apply left_absorb. Qed.

  Lemma field_div_diag x y : x = `y → x // y = 1.
  Proof. intros E. rewrite E. apply mult_inverse. Qed.

  Lemma equal_quotients (a c: F) b d : a * `d = c * `b ↔ a // b = c // d.
  Proof with try ring.
   split; intro E.
    transitivity (1 * (a // b))...
    rewrite <- (mult_inverse d).
    transitivity (// d * (a * `d) // b)...
    rewrite E.
    transitivity (// d * c * (`b // b))...
    rewrite mult_inverse...
   transitivity (a * `d * 1)...
   rewrite <- (mult_inverse b).
   transitivity (a // b * `d * `b)...
   rewrite E.
   transitivity (c * (`d // d) * `b)...
   rewrite mult_inverse...
  Qed. (* todo: should be cleanable *)

  Lemma mult_inv_inj `{∀ z, PropHolds (z ≠ 0) → LeftCancellation (.*.) z} x y : // x = // y → x = y.
  Proof.
    intros E.
    unfold equiv, sig_equiv. fold equiv.
    apply (left_cancellation (.*.) (//x)).
    rewrite commutativity, mult_inverse. 
    now rewrite E, commutativity, mult_inverse.
  Qed.

  Lemma mult_inv_distr_alt `{∀ z, PropHolds (z ≠ 0) → LeftCancellation (.*.) z} x (Px : x ≠ 0) y (Py : y ≠ 0) (Pxy : x * y ≠ 0) : 
    // (x * y)↾Pxy = // x↾Px * // y↾Py.
  Proof with auto; try ring.
    apply (left_cancellation_ne_0 (.*.) (x * y))...
    transitivity ((x // x↾Px) *  (y // y↾Py))...
    transitivity ((x * y) // (x * y)↾Pxy)...
    rewrite 3!mult_inverse_alt...
  Qed.

  (* Properties of fields with decidable equality *)
  Context `{∀ x y: F, Decision (x = y)} `{dec_inv : !DecMultInv F}.

  Global Instance: ZeroProduct F.
  Proof with auto.
   intros x y E.
   destruct (decide (x = 0)) as [? | P]...
   rewrite <-(mult_0_r x) in E.
   right. now apply (left_cancellation_ne_0 (.*.) x).
  Qed.

  Lemma dec_mult_inverse (x: F) : PropHolds (x ≠ 0) → x / x = 1.
  Proof.
    intro E. 
    unfold dec_mult_inv, dec_mult_inv_sig. 
    destruct dec_inv as [z [E1 E2]]. auto.
  Qed.

  Lemma dec_mult_inv_correct (x : F) (Px : x ≠ 0) : / x = // x↾Px.
  Proof with auto.
    apply (left_cancellation_ne_0 (.*.) x)...
    rewrite dec_mult_inverse...
    symmetry. apply mult_inverse_alt.
  Qed.

  Lemma dec_mult_inv_0: / 0 = 0.
  Proof. 
    unfold dec_mult_inv, dec_mult_inv_sig. 
    destruct dec_inv as [z [E1 E2]]. now apply E2.
  Qed.

  Lemma dec_mult_inv_1: / 1 = 1.
  Proof. 
    rewrite <-(rings.mult_1_l (/1)).
    apply dec_mult_inverse.
    apply (ne_0 1).
  Qed.

  Global Instance dec_mult_inv_proper: Proper ((=) ==> (=)) (/) | 1.
  Proof with auto.
    intros x1 x2 E.
    case (decide (x1 = 0)); intros E1; case (decide (x2 = 0)); intros E2.
       unfold dec_mult_inv, dec_mult_inv_sig.
       destruct (dec_inv x1) as [z1 [? Ez1]], (dec_inv x2) as [z2 [? Ez2]].
       simpl. now rewrite Ez1, Ez2.
      destruct E2. now rewrite <-E.
     destruct E1. now rewrite E.
    apply (left_cancellation_ne_0 (.*.) x1)...
    now rewrite dec_mult_inverse, E, dec_mult_inverse.
  Qed.

  Lemma dec_mult_inv_distr (x y: F): / (x * y) = / x * / y.
  Proof with auto.
    case (decide (x = 0)); intros E1. rewrite E1, left_absorb, dec_mult_inv_0. ring.
    case (decide (y = 0)); intros E2. rewrite E2, right_absorb, dec_mult_inv_0. ring.
    assert (x * y ≠ 0) as E3. apply mult_ne_zero...
    rewrite (dec_mult_inv_correct _ E1), (dec_mult_inv_correct _ E2), (dec_mult_inv_correct _ E3).
    apply mult_inv_distr_alt.
  Qed.

  Lemma equal_by_one_quotient (x y : F) : x / y = 1 → x = y.
  Proof with auto; try ring.
   intro E1.
   case (decide (y = 0)); intros E2.
    exfalso. apply (ne_0 1).
    rewrite <- E1, E2, dec_mult_inv_0...
   transitivity ((y * /y) * x). rewrite dec_mult_inverse...
   transitivity ((x * /y) * y)... rewrite E1...
  Qed.

  Lemma dec_mult_inv_zero x : / x = 0 ↔ x = 0.
  Proof with auto.
    split; intros E.
     destruct (decide (x = 0))...
     destruct (ne_0 1). 
     rewrite <-(dec_mult_inverse x), E... ring.
    rewrite E. apply dec_mult_inv_0.
  Qed.

  Lemma dec_mult_inv_nonzero_iff x : / x ≠ 0 ↔ x ≠ 0.
  Proof. firstorder using dec_mult_inv_zero. Qed.

  Global Instance dec_mult_inv_nonzero x : PropHolds (x ≠ 0) → PropHolds (/x ≠ 0).
  Proof. firstorder using dec_mult_inv_zero. Qed.

  Global Instance dec_mult_inv_inj: Injective (/).
  Proof with try solve [intuition].
    repeat (split; try apply _).
    intros x y E. 
    destruct (decide (y = 0)) as [E2|E2].
     rewrite E2 in *. rewrite dec_mult_inv_0 in E.
     apply dec_mult_inv_zero...
    apply (right_cancellation_ne_0 (.*.) (/y)).
     apply dec_mult_inv_nonzero...
    rewrite dec_mult_inverse...
    rewrite <-E. apply dec_mult_inverse...
    apply dec_mult_inv_nonzero_iff. rewrite E. now apply dec_mult_inv_nonzero.
  Qed.

  Lemma dec_mult_inv_involutive x : / / x = x.
  Proof with auto.
    destruct (decide (x = 0)) as [E|E].
     rewrite E. now rewrite 2!dec_mult_inv_0.
    apply (right_cancellation_ne_0 (.*.) (/x)).
     apply dec_mult_inv_nonzero...
    rewrite dec_mult_inverse...
    rewrite commutativity, dec_mult_inverse. reflexivity.
    apply dec_mult_inv_nonzero...
  Qed.

  Lemma equal_dec_quotients (a b c d : F) : b ≠ 0 → d ≠ 0 → (a * d = c * b ↔ a / b = c / d).
  Proof with trivial; try ring.
   split; intro E.
    apply (right_cancellation_ne_0 (.*.) b)...
    apply (right_cancellation_ne_0 (.*.) d)...
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

  Lemma dec_quotients (a c b d : F) : b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + c * b) / (b * d).
  Proof with auto.
    intros A B.
    assert (a / b = (a * d) / (b * d)) as E1.
     apply ->equal_dec_quotients...
      ring.
     intros G. destruct (zero_product b d)...
    assert (c / d = (b * c) / (b * d)) as E2.
     apply ->equal_dec_quotients...
      ring.
     intros G. destruct (zero_product b d)...
    rewrite E1, E2. ring.
  Qed.

  Lemma dec_mult_inv_swap_l x y: x / y = / (/ x * y). 
  Proof. rewrite dec_mult_inv_distr, dec_mult_inv_involutive. ring. Qed.

  Lemma dec_mult_inv_swap_r x y: / x * y = / (x / y). 
  Proof. rewrite dec_mult_inv_distr, dec_mult_inv_involutive. ring. Qed.

  Lemma dec_mult_inv_opp x : -(/ x) = / (-x).
  Proof.
    destruct (decide (x = 0)) as [E|E].
     now rewrite E, opp_0, dec_mult_inv_0, opp_0.
    apply (left_cancellation_ne_0 (.*.) (-x)).
     now apply flip_opp_nonzero.
    rewrite dec_mult_inverse.
     ring_simplify.
     now apply dec_mult_inverse.
    now apply flip_opp_nonzero.
  Qed.
End field_properties.

Definition stdlib_field_theory F `{Field F} `{!DecMultInv F} :
  Field_theory.field_theory 0 1 (+) (.*.) (λ x y, x - y) (-) (λ x y, x / y) (/) (=).
Proof with auto.
  intros.
  constructor.
     apply (theory.rings.stdlib_ring_theory _).
    apply (ne_0 1).
   reflexivity.
  intros.
  rewrite commutativity. apply dec_mult_inverse...
Qed.

Section morphisms.
  Context `{Field F1} `{Field F2} `{!SemiRing_Morphism (f : F1 → F2)} `{∀ z : F2, PropHolds (z ≠ 0) → LeftCancellation (.*.) z}.

  Lemma preserves_mult_inv `{!Injective f} x Px Pfx : f (// x↾Px) = // (f x)↾Pfx.
  Proof.
    apply (left_cancellation_ne_0 (.*.) (f x)).
     now apply injective_ne_0.
    rewrite <-preserves_mult, 2!mult_inverse_alt.
    now apply preserves_1.
  Qed.

  Context  `{!DecMultInv F1} `{!DecMultInv F2} `{∀ x y: F1, Decision (x = y)} `{∀ x y: F2, Decision (x = y)}.

  Lemma preserves_dec_mult_inv `{!Injective f} x : f (/ x) = / f x.
  Proof.
    case (decide (x = 0)) as [E | E].
     now rewrite E, dec_mult_inv_0, preserves_0, dec_mult_inv_0.
    apply (left_cancellation_ne_0 (.*.) (f x)).
     now apply injective_ne_0.
    rewrite <-preserves_mult, 2!dec_mult_inverse.
      apply preserves_1.
     now apply injective_ne_0.
    easy.
  Qed.
End morphisms.

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
   ; unfold equiv, mon_unit, sg_op, ring_plus, ring_mult, mult_inv, group_inv; try field...
   destruct x as [x Ex].
   unfold mult_inv, ring_mult.
   simpl.
   assert (e (mu x (rinv x)) (mu (rinv x) x)) as E by ring.
   rewrite E...
  Qed.
End from_stdlib_field_theory.

Program Instance dec_mult_inv_default `{Field F} `{∀ x y: F, Decision (x = y)} : DecMultInv F | 10
  := λ x, (if decide_rel (=) x 0 then 0 else // x)↾_.
Next Obligation.
  case (decide_rel _); split; try solve [intuition].
  intros E. apply mult_inverse_alt.
Qed.
