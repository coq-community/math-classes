Require Import
  Field Ring
  abstract_algebra theory.fields theory.strong_setoids.
Require Export
  theory.rings.

Section contents.
Context `{DecField F} `{∀ x y: F, Decision (x = y)}.

Add Ring F : (stdlib_ring_theory F).

Global Instance: ZeroProduct F.
Proof with auto.
  intros x y E.
  destruct (decide (x = 0)) as [? | Ex]...
  right.
  rewrite <-(mult_1_r y), <-(dec_recip_inverse x) by assumption.
  rewrite associativity, (commutativity y), E. ring.
Qed.

Global Instance: IntegralDomain F.
Proof. split; try apply _. Qed.

Lemma dec_recip_1: / 1 = 1.
Proof.
  rewrite <-(rings.mult_1_l (/1)).
  apply dec_recip_inverse.
  solve_propholds.
Qed.

Lemma dec_recip_distr (x y: F): / (x * y) = / x * / y.
Proof.
  destruct (decide (x = 0)) as [Ex|Ex].
   rewrite Ex, left_absorb, dec_recip_0. ring.
  destruct (decide (y = 0)) as [Ey|Ey].
   rewrite Ey, right_absorb, dec_recip_0. ring.
  assert (x * y ≠ 0) as Exy by now apply mult_ne_0.
  apply (left_cancellation_ne_0 (.*.) (x * y)); trivial.
  transitivity (x / x * (y / y)).
   rewrite !dec_recip_inverse by assumption. ring.
  ring.
Qed.

Lemma dec_recip_zero x : / x = 0 ↔ x = 0.
Proof.
  split; intros E.
   apply stable. intros Ex.
   destruct (is_ne_0 1).
   rewrite <-(dec_recip_inverse x), E by assumption. ring.
  rewrite E. now apply dec_recip_0.
Qed.

Lemma dec_recip_ne_0_iff x : / x ≠ 0 ↔ x ≠ 0.
Proof. now split; intros E1 E2; destruct E1; apply dec_recip_zero. Qed.

Instance dec_recip_ne_0 x : PropHolds (x ≠ 0) → PropHolds (/x ≠ 0).
Proof. intro. now apply dec_recip_ne_0_iff. Qed.

Lemma equal_by_one_quotient (x y : F) : x / y = 1 → x = y.
Proof.
  intro Exy.
  destruct (decide (y = 0)) as [Ey|Ey].
   exfalso. apply (is_ne_0 1).
   rewrite <- Exy, Ey, dec_recip_0. ring.
  apply (right_cancellation_ne_0 (.*.) (/y)).
   now apply dec_recip_ne_0.
  now rewrite dec_recip_inverse.
Qed.

Global Instance dec_recip_inj: Injective (/).
Proof.
  repeat (split; try apply _).
  intros x y E.
  destruct (decide (y = 0)) as [Ey|Ey].
   rewrite Ey in *. rewrite dec_recip_0 in E.
   now apply dec_recip_zero.
  apply (right_cancellation_ne_0 (.*.) (/y)).
   now apply dec_recip_ne_0.
  rewrite dec_recip_inverse by assumption.
  rewrite <-E, dec_recip_inverse.
   easy.
  apply dec_recip_ne_0_iff. rewrite E.
  now apply dec_recip_ne_0.
Qed.

Global Instance dec_recip_involutive: Involutive (/).
Proof.
  intros x. destruct (decide (x = 0)) as [Ex|Ex].
   now rewrite Ex, !dec_recip_0.
  apply (right_cancellation_ne_0 (.*.) (/x)).
   now apply dec_recip_ne_0.
  rewrite dec_recip_inverse by assumption.
  rewrite commutativity, dec_recip_inverse.
   reflexivity.
  now apply dec_recip_ne_0.
Qed.

Lemma equal_dec_quotients (a b c d : F) : b ≠ 0 → d ≠ 0 → (a * d = c * b ↔ a / b = c / d).
Proof with trivial; try ring.
  split; intro E.
   apply (right_cancellation_ne_0 (.*.) b)...
   apply (right_cancellation_ne_0 (.*.) d)...
   transitivity (a * d * (b * /b))...
   transitivity (c * b * (d * /d))...
   rewrite E, dec_recip_inverse, dec_recip_inverse...
  transitivity (a * d * 1)...
  rewrite <-(dec_recip_inverse b)...
  transitivity (a * / b * d * b)...
  rewrite E.
  transitivity (c * (d * / d) * b)...
  rewrite dec_recip_inverse...
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

Lemma dec_recip_swap_l x y: x / y = / (/ x * y).
Proof. rewrite dec_recip_distr, involutive. ring. Qed.

Lemma dec_recip_swap_r x y: / x * y = / (x / y).
Proof. rewrite dec_recip_distr, involutive. ring. Qed.

Lemma dec_recip_negate x : -(/ x) = / (-x).
Proof.
  destruct (decide (x = 0)) as [Ex|Ex].
   now rewrite Ex, negate_0, dec_recip_0, negate_0.
  apply (left_cancellation_ne_0 (.*.) (-x)).
   now apply flip_negate_ne_0.
  rewrite dec_recip_inverse.
   ring_simplify.
   now apply dec_recip_inverse.
  now apply flip_negate_ne_0.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (/ _ ≠ 0)) => eapply @dec_recip_ne_0 : typeclass_instances.

(* Given a decidable field we can easily construct a constructive field. *)
Section is_field.
  Context `{DecField F} `{Apart F} `{!TrivialApart F} `{∀ x y: F, Decision (x = y)}.

  Global Program Instance recip_dec_field: Recip F := λ x, /`x.

  Instance: StrongSetoid F := dec_strong_setoid.

  Global Instance: Field F.
  Proof.
    split; try apply _.
       now apply (dec_strong_binary_morphism (+)).
      now apply (dec_strong_binary_morphism (.*.)).
     split; try apply _.
     intros ? ? E. unfold recip, recip_dec_field.
     now apply sm_proper.
    intros [x Px]. rapply (dec_recip_inverse x).
    now apply trivial_apart.
  Qed.

  Lemma dec_recip_correct (x : F) Px : / x = // x↾Px.
  Proof with auto.
    apply (left_cancellation_ne_0 (.*.) x).
     now apply trivial_apart.
    now rewrite dec_recip_inverse, reciperse_alt by now apply trivial_apart.
  Qed.
End is_field.

Definition stdlib_field_theory F `{DecField F} :
  Field_theory.field_theory 0 1 (+) (.*.) (λ x y, x - y) (-) (λ x y, x / y) (/) (=).
Proof with auto.
  intros.
  constructor.
     apply (theory.rings.stdlib_ring_theory _).
    apply (is_ne_0 1).
   reflexivity.
  intros.
  rewrite commutativity. now apply dec_recip_inverse.
Qed.

Section from_stdlib_field_theory.
  Context `(ftheory : @field_theory F Fzero Fone Fplus Fmult Fminus Fnegate Fdiv Frecip Fe)
    (rinv_0 : Fe (Frecip Fzero) Fzero)
    `{!@Setoid F Fe}
    `{!Proper (Fe ==> Fe ==> Fe) Fplus}
    `{!Proper (Fe ==> Fe ==> Fe) Fmult}
    `{!Proper (Fe ==> Fe) Fnegate}
    `{!Proper (Fe ==> Fe) Frecip}.

  Add Field F2 : ftheory.

  Definition from_stdlib_field_theory: @DecField F Fe Fplus Fmult Fzero Fone Fnegate Frecip.
  Proof with auto.
   destruct ftheory.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, zero_is_mon_unit, plus_is_sg_op,
     one_is_mon_unit, mult_is_sg_op, plus, mult, recip, negate; try field...
   unfold recip, mult.
   simpl.
   assert (Fe (Fmult x (Frecip x)) (Fmult (Frecip x) x)) as E by ring.
   rewrite E...
  Qed.
End from_stdlib_field_theory.

Section morphisms.
  Context  `{DecField F} `{∀ x y: F, Decision (x = y)}.

  Global Instance dec_field_to_domain_inj `{IntegralDomain R}
    `{!SemiRing_Morphism (f : F → R)} : Injective f.
  Proof.
    apply injective_preserves_0.
    intros x Efx.
    apply stable. intros Ex.
    destruct (is_ne_0 (1:R)).
    rewrite <-(rings.preserves_1 (f:=f)).
    rewrite <-(dec_recip_inverse x) by assumption.
    rewrite rings.preserves_mult, Efx.
    now apply left_absorb.
  Qed.

  Lemma preserves_dec_recip `{DecField F2} `{∀ x y: F2, Decision (x = y)}
    `{!SemiRing_Morphism (f : F → F2)} x : f (/ x) = / f x.
  Proof.
    case (decide (x = 0)) as [E | E].
     now rewrite E, dec_recip_0, preserves_0, dec_recip_0.
    intros.
    apply (left_cancellation_ne_0 (.*.) (f x)).
     now apply injective_ne_0.
    rewrite <-preserves_mult, 2!dec_recip_inverse.
      now apply preserves_1.
     now apply injective_ne_0.
    easy.
  Qed.

  Lemma dec_recip_to_recip `{Field F2} `{!StrongSemiRing_Morphism (f : F → F2)} x Pfx :
    f (/ x) = // (f x)↾Pfx.
  Proof.
    assert (x ≠ 0).
     intros Ex.
     destruct (apart_ne (f x) 0 Pfx).
     now rewrite Ex, preserves_0.
    apply (left_cancellation_ne_0 (.*.) (f x)).
     now apply injective_ne_0.
    rewrite <-preserves_mult, dec_recip_inverse, reciperse_alt by assumption.
    now apply preserves_1.
  Qed.
End morphisms.
