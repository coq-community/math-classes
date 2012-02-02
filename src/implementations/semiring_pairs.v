Require Import
  Ring abstract_algebra interfaces.orders orders.rings.

Inductive SRpair (SR : Type) := C { pos : SR ; neg : SR }.
Arguments C {SR} _ _.
Arguments pos {SR} _.
Arguments neg {SR} _.

Section semiring_pairs.
Context `{SemiRing SR} `{Apart SR}.
Context `{∀ z, LeftCancellation (+) z}.

Add Ring SR : (rings.stdlib_semiring_theory SR).

(* Equivalence *)
Global Instance SRpair_equiv : Equiv (SRpair SR) | 4 := λ x y, pos x + neg y = pos y + neg x.
Global Instance SRpair_apart `{Apart SR} : Apart (SRpair SR) := λ x y, pos x + neg y ≶ pos y + neg x.

Global Instance SRpair_trivial_apart `{!TrivialApart SR} :  TrivialApart (SRpair SR).
Proof. intros x y. now rapply trivial_apart. Qed.

Instance: Setoid (SRpair SR).
Proof.
  split; red; unfold equiv, SRpair_equiv.
    reflexivity.
   intros. now symmetry.
  intros x y z E E'.
  rewrite commutativity.
  rewrite (commutativity (pos z)).
  apply (left_cancellation (+) (pos y)).
  rewrite 2!associativity.
  rewrite <- E, E'. ring.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) C.
Proof.
  intros x1 y1 E1 x2 y2 E2. unfold equiv, SRpair_equiv. simpl.
  now rewrite E1, E2.
Qed.

(* injection from SR *)
Global Instance SRpair_inject: Cast SR (SRpair SR) := λ r, C r 0.

Global Instance: Proper ((=) ==> (=)) SRpair_inject.
Proof. intros x1 x2 E. unfold equiv, SRpair_equiv. simpl. now rewrite E. Qed.

(* Relations, operations and constants *)
Global Instance SRpair_plus: Plus (SRpair SR) := λ x y, C (pos x + pos y) (neg x + neg y).
Global Instance SRpair_negate: Negate (SRpair SR) := λ x, C (neg x) (pos x).
Global Instance SRpair_0: Zero (SRpair SR) := ('0 : SRpair SR).
Global Instance SRpair_mult: Mult (SRpair SR) := λ x y, C (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y).
Global Instance SRpair_1: One (SRpair SR) := ('1 : SRpair SR).

Ltac unfolds := unfold SRpair_negate, SRpair_plus, equiv, SRpair_equiv in *; simpl in *.
Ltac ring_on_sr := repeat intro; unfolds; try ring.

Instance: Proper ((=) ==> (=)) SRpair_negate.
Proof.
  intros x y E. unfolds.
  rewrite commutativity, <- E. ring.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) SRpair_plus.
Proof with try ring.
  intros x1 y1 E1 x2 y2 E2. unfolds.
  transitivity (pos x1 + neg y1 + (pos x2 + neg y2))...
  rewrite E1, E2...
Qed.

Let SRpair_mult_proper_r (x y z : SRpair SR) : x = y → z * x = z * y.
Proof with try ring.
  intros E. unfolds.
  transitivity (pos z * (pos x + neg y) + neg z * (pos y + neg x))...
  transitivity (pos z * (pos y + neg x) + neg z * (pos x + neg y))...
  now rewrite E.
Qed.

Instance: Commutative SRpair_mult.
Proof. repeat intro. ring_on_sr. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) SRpair_mult.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  transitivity (x1 * y2).
   now apply SRpair_mult_proper_r.
  rewrite !(commutativity _ y2).
  now apply SRpair_mult_proper_r.
Qed.

Global Instance: Ring (SRpair SR).
Proof. repeat (split; try apply _); ring_on_sr. Qed.

(* A final word about inject *)
Global Instance: SemiRing_Morphism SRpair_inject.
Proof.
  repeat (constructor; try apply _); try reflexivity.
   intros x y. change (x + y + (0 + 0) = x + y + 0). ring.
  intros x y. change (x * y + (x * 0 + 0 * y) = x * y + 0 * 0 + 0). ring.
Qed.

Global Instance: Injective SRpair_inject.
Proof.
  repeat (constructor; try apply _).
  intros x y. unfolds. now rewrite 2!rings.plus_0_r.
Qed.

Lemma SRpair_splits n m : C n m = 'n + -'m.
Proof. ring_on_sr. Qed.

Global Instance SRpair_le `{Le SR} : Le (SRpair SR) := λ x y, pos x + neg y ≤ pos y + neg x.
Global Instance SRpair_lt `{Lt SR} : Lt (SRpair SR) := λ x y, pos x + neg y < pos y + neg x.
Ltac unfold_le := unfold le, SRpair_le, equiv, SRpair_equiv; simpl.
Ltac unfold_lt := unfold lt, SRpair_lt, equiv, SRpair_equiv; simpl.

Section with_semiring_order.
  Context `{!SemiRingOrder SRle}.

  Instance: Proper ((=) ==> (=) ==> iff) SRpair_le.
  Proof.
    assert (∀ x1 y1 : SRpair SR, x1 = y1 → ∀ x2 y2, x2 = y2 → x1 ≤ x2 → y1 ≤ y2) as E.
     unfold_le. intros [xp1 xn1] [yp1 yn1] E1 [xp2 xn2] [yp2 yn2] E2 F. simpl in *.
     apply (order_reflecting (+ (xp2 + xn1))).
     setoid_replace (yp1 + yn2 + (xp2 + xn1)) with ((yp1 + xn1) + (xp2 + yn2)) by ring.
     rewrite <-E1, E2.
     setoid_replace (xp1 + yn1 + (yp2 + xn2)) with ((yp2 + yn1) + (xp1 + xn2)) by ring.
     now apply (order_preserving _).
    split; repeat intro; eapply E; eauto; symmetry; eauto.
  Qed.

  Instance: Reflexive SRpair_le.
  Proof. intros [? ?]. unfold_le. reflexivity. Qed.

  Instance: Transitive SRpair_le.
  Proof.
    intros [xp xn] [yp yn] [zp zn] E1 E2.
    unfold SRpair_le in *. simpl in *.
    apply (order_reflecting (+ (yn + yp))).
    setoid_replace (xp + zn + (yn + yp)) with ((xp + yn) + (yp + zn)) by ring.
    setoid_replace (zp + xn + (yn + yp)) with ((yp + xn) + (zp + yn)) by ring.
    now apply plus_le_compat.
  Qed.

  Instance: AntiSymmetric SRpair_le.
  Proof.
    intros [xp xn] [yp yn] E1 E2. unfold_le.
    now apply (antisymmetry (≤)).
  Qed.

  Instance: PartialOrder SRpair_le.
  Proof. repeat (split; try apply _). Qed.

  Global Instance: OrderEmbedding SRpair_inject.
  Proof.
    repeat (split; try apply _).
     intros x y E. unfold_le. simpl. now rewrite 2!rings.plus_0_r.
    intros x y E. unfold le, SRpair_le in E. simpl in E. now rewrite 2!rings.plus_0_r in E.
  Qed.

  Instance: ∀ z : SRpair SR, OrderPreserving ((+) z).
  Proof.
    repeat (split; try apply _). unfold_le.
    destruct z as [zp zn]. intros [xp xn] [yp yn] E. simpl in *.
    setoid_replace (zp + xp + (zn + yn)) with ((zp + zn) + (xp + yn)) by ring.
    setoid_replace (zp + yp + (zn + xn)) with ((zp + zn) + (yp + xn)) by ring.
    now apply (order_preserving _).
  Qed.

  Instance: ∀ x y : SRpair SR, PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y).
  Proof.
    intros [xp xn] [yp yn].
    unfold PropHolds. unfold_le. intros E1 E2.
    ring_simplify in E1. ring_simplify in E2.
    destruct (decompose_le E1) as [a [Ea1 Ea2]], (decompose_le E2) as [b [Eb1 Eb2]].
    rewrite Ea2, Eb2. ring_simplify.
    apply compose_le with (a * b).
     now apply nonneg_mult_compat.
    ring.
  Qed.

  Global Instance: SemiRingOrder SRpair_le.
  Proof. apply rings.from_ring_order; apply _. Qed.
End with_semiring_order.

Section with_strict_semiring_order.
  Context `{!StrictSemiRingOrder SRle}.

  Instance: Proper ((=) ==> (=) ==> iff) SRpair_lt.
  Proof.
    assert (∀ x1 y1 : SRpair SR, x1 = y1 → ∀ x2 y2, x2 = y2 → x1 < x2 → y1 < y2) as E.
     unfold_lt. intros [xp1 xn1] [yp1 yn1] E1 [xp2 xn2] [yp2 yn2] E2 F. simpl in *.
     apply (strictly_order_reflecting (+ (xp2 + xn1))).
     setoid_replace (yp1 + yn2 + (xp2 + xn1)) with ((yp1 + xn1) + (xp2 + yn2)) by ring.
     rewrite <-E1, E2.
     setoid_replace (xp1 + yn1 + (yp2 + xn2)) with ((yp2 + yn1) + (xp1 + xn2)) by ring.
     now apply (strictly_order_preserving _).
    split; repeat intro; eapply E; eauto; symmetry; eauto.
  Qed.

  Instance: Irreflexive SRpair_lt.
  Proof. intros [? ?] E. edestruct (irreflexivity (<)); eauto. Qed.

  Instance: Transitive SRpair_lt.
  Proof.
    intros [xp xn] [yp yn] [zp zn] E1 E2.
    unfold SRpair_lt in *. simpl in *.
    apply (strictly_order_reflecting (+ (yn + yp))).
    setoid_replace (xp + zn + (yn + yp)) with ((xp + yn) + (yp + zn)) by ring.
    setoid_replace (zp + xn + (yn + yp)) with ((yp + xn) + (zp + yn)) by ring.
    now apply plus_lt_compat.
  Qed.

  Instance: ∀ z : SRpair SR, StrictlyOrderPreserving ((+) z).
  Proof.
    repeat (split; try apply _). unfold_lt.
    destruct z as [zp zn]. intros [xp xn] [yp yn] E. simpl in *.
    setoid_replace (zp + xp + (zn + yn)) with ((zp + zn) + (xp + yn)) by ring.
    setoid_replace (zp + yp + (zn + xn)) with ((zp + zn) + (yp + xn)) by ring.
    now apply (strictly_order_preserving _).
  Qed.

  Instance: StrictSetoidOrder SRpair_lt.
  Proof. repeat (split; try apply _). Qed.

  Instance: ∀ x y : SRpair SR, PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y).
  Proof.
    intros [xp xn] [yp yn].
    unfold PropHolds. unfold_lt. intros E1 E2.
    ring_simplify in E1. ring_simplify in E2.
    destruct (decompose_lt E1) as [a [Ea1 Ea2]], (decompose_lt E2) as [b [Eb1 Eb2]].
    rewrite Ea2, Eb2. ring_simplify.
    apply compose_lt with (a * b).
     now apply pos_mult_compat.
    ring.
  Qed.

  Global Instance: StrictSemiRingOrder SRpair_lt.
  Proof. apply from_strict_ring_order; apply _. Qed.
End with_strict_semiring_order.

Section with_full_pseudo_semiring_order.
  Context `{!FullPseudoSemiRingOrder SRle SRlt}.

  Instance: StrongSetoid SR := pseudo_order_setoid.

  Instance: StrongSetoid (SRpair SR).
  Proof.
    split.
       intros [??] E. now eapply (irreflexivity (≶)); eauto.
      intros [??] [??] E. unfold apart, SRpair_apart. now symmetry.
     intros [xp xn] [yp yn] E [zp zn]. unfold apart, SRpair_apart in *. simpl in *.
     apply (strong_left_cancellation (+) zn) in E.
     edestruct (cotransitive E).
      left. apply (strong_extensionality (+ yn)).
      setoid_replace (xp + zn + yn) with (zn + (xp + yn)) by ring. eassumption.
     right. apply (strong_extensionality (+ xn)).
     setoid_replace (zp + yn + xn) with (zp + xn + yn) by ring.
     setoid_replace (yp + zn + xn) with (zn + (yp + xn)) by ring.
     eassumption.
    intros [??] [??]. now rapply tight_apart.
  Qed.

  Instance: FullPseudoOrder SRpair_le SRpair_lt.
  Proof.
    split.
     split; try apply _.
       intros [??] [??]. unfold_lt. now apply pseudo_order_antisym.
      intros [xp xn] [yp yn] E [zp zn]. unfold lt, SRpair_lt in *. simpl in *.
      apply (strictly_order_preserving (zn +)) in E.
      edestruct (cotransitive E).
       left. apply (strictly_order_reflecting (+ yn)).
       setoid_replace (xp + zn + yn) with (zn + (xp + yn)) by ring. eassumption.
      right. apply (strictly_order_reflecting (+ xn)).
      setoid_replace (zp + yn + xn) with (zp + xn + yn) by ring.
      setoid_replace (yp + zn + xn) with (zn + (yp + xn)) by ring.
      eassumption.
     intros [??] [??]. now rapply apart_iff_total_lt.
    intros [??] [??]. now rapply le_iff_not_lt_flip.
  Qed.

  Instance: ∀ z : SRpair SR, StrongSetoid_Morphism (z *.).
  Proof.
    intros [zp zn]. split; try apply _. intros [xp xn] [yp yn] E1.
    unfold apart, SRpair_apart in *. simpl in *.
    destruct (strong_binary_extensionality (+)
       (zp * (xp + yn)) (zn * (yp + xn)) (zp * (yp + xn)) (zn * (xp + yn))).
      eapply strong_setoids.apart_proper; eauto; ring.
     now apply (strong_extensionality (zp *.)).
    symmetry. now apply (strong_extensionality (zn *.)).
  Qed.

  Global Instance: FullPseudoSemiRingOrder SRpair_le SRpair_lt.
  Proof.
    apply from_full_pseudo_ring_order; try apply _.
    now apply strong_setoids.strong_binary_setoid_morphism_commutative.
  Qed.
End with_full_pseudo_semiring_order.

Global Instance SRpair_dec `{∀ x y : SR, Decision (x = y)} : ∀ x y : SRpair SR, Decision (x = y)
  := λ x y, decide_rel (=) (pos x + neg y) (pos y + neg x).

Global Program Instance SRpair_le_dec `{Le SR} `{∀ x y: SR, Decision (x ≤ y)} : ∀ x y : SRpair SR, Decision (x ≤ y) := λ x y,
  match decide_rel (≤) (pos x + neg y) (pos y + neg x) with
  | left E => left _
  | right E => right _
  end.

End semiring_pairs.

Typeclasses Opaque SRpair_equiv.
Typeclasses Opaque SRpair_le.
