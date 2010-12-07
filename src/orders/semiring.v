Set Automatic Introduction.

Require
 theory.naturals.
Require Import
 Relation_Definitions Morphisms Ring Program Setoid
 abstract_algebra interfaces.naturals theory.rings workaround_tactics.

Section comm_monoid_order.
  Context `{CommutativeMonoid R} `{!Order R}.

  (* These instances should be created manually to avoid loops *)
  Lemma order_preserving_flip `{!OrderPreserving (sg_op z) } : OrderPreserving (flip sg_op z).
  Proof with auto.
    repeat (split; try apply _).
    intros x y E. unfold flip.
    rewrite (commutativity x z), (commutativity y z).
    apply order_preserving...
  Qed.

  Lemma order_preserving_back_flip `{!OrderPreservingBack (sg_op z) } : OrderPreservingBack (flip sg_op z).
  Proof with auto.
    repeat (split; try apply _).
    intros x y E. unfold flip in E.
    apply (order_preserving_back (sg_op z)).
    rewrite (commutativity z x), (commutativity z y)...
  Qed.
End comm_monoid_order.

Section order_preserving.
  Context `{Equiv A} `{oA : Order A} `{Equiv B} `{oB : Order B} (op : A → B → A) `{!RingZero A} `{!RingOne A}.

  Lemma order_preserving_ge_zero `{∀ z, GeZero z → OrderPreserving (op z)} z : 0 ≤ z → OrderPreserving (op z).
  Proof. auto. Qed.

  Lemma order_preserving_back_ge_one `{∀ z, GeOne z → OrderPreservingBack (op z)} z : 1 ≤ z → OrderPreservingBack (op z).
  Proof. auto. Qed.
End order_preserving.

Section contents. 
  Context `{SemiRing R}.
  Add Ring SR: (stdlib_semiring_theory R).

  Global Instance sr_precedes_proper: Proper ((=) ==> (=) ==> iff) sr_precedes.
  Proof with assumption.
   intros x x' E y y' E'. 
   split; intros [z p]; exists z.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Instance: Transitive sr_precedes.
  Proof.
   intros x y z [d p] [d' p'].
   exists (d + d'). rewrite <- p', <- p. 
   rewrite preserves_sg_op.
   apply associativity.
  Qed.

  Instance: Reflexive sr_precedes.
  Proof.
   exists (0:nat). rewrite preserves_0.
   ring.
  Qed.

  Global Instance: PreOrder sr_precedes.

  Global Instance sr_precedes_plus_compat : Proper ((≤) ==> (≤) ==> (≤)) (+).
  Proof.
    intros x1 y1 [v1 Ev1] x2 y2 [v2 Ev2].
    exists (v1 + v2). rewrite preserves_plus, <-Ev1, <-Ev2. ring.
  Qed.

  Global Instance: ∀ (z : R), OrderPreserving ((+) z).
  Proof. repeat (split; try apply _). apply sr_precedes_plus_compat. reflexivity. Qed.

  Global Instance: ∀ (z : R), OrderPreserving (flip (+) z).
  Proof. intros. apply order_preserving_flip. Qed.

  Lemma sr_precedes_nonneg_plus_compat (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
  Proof.
    intros. rewrite <-(plus_0_r 0). apply sr_precedes_plus_compat; assumption.
  Qed.

  Global Instance: ∀ (z : R), GeZero z → OrderPreserving (ring_mult z).
  Proof.
   intros z [v E]. 
   repeat (split; try apply _).
   intros x y [w F].
   rewrite <-E, <-F. 
   exists (v * w). rewrite preserves_mult. ring.
  Qed.

  Global Instance: ∀ (z : R), GeZero z → OrderPreserving (flip ring_mult z).
  Proof. intros. apply order_preserving_flip. Qed.

  Lemma sr_precedes_nonneg_mult_compat (x y : R) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
  Proof.
    repeat intro. rewrite <-(mult_0_r x).
    apply (order_preserving_ge_zero ring_mult x); assumption.
  Qed.

  Global Instance sr_precedes_0_1: GeZero (1:R).
  Proof.
    exists (1:nat).
    rewrite preserves_1. ring. 
  Qed.

  Lemma not_sr_precedes_0_1 `{!AntiSymmetric (≤)} `{!NeZero (1:R)} : ¬ (1:R) ≤ (0:R).
  Proof with auto.
    intros E.
    destruct (ne_zero 1).
    apply (antisymmetry (≤))...
    apply sr_precedes_0_1.
  Qed.
  
  Context `{∀ z, LeftCancellation (+) z}.

  Global Instance: ∀ (z : R), OrderPreservingBack ((+) z).
  Proof with auto. 
    intros z.
    repeat (split; try apply _). 
    intros x y [v Ev]. 
    exists v. apply (left_cancellation (+) z)...
    rewrite <-Ev. ring.
  Qed.

  Global Instance: ∀ (z : R), OrderPreservingBack (flip (+) z).
  Proof. intros. apply order_preserving_back_flip. Qed.

  Context `{!TotalOrder (≤)} `{!Injective (naturals_to_semiring nat R)}.

  Global Instance: ∀ (z : R), GeOne z → OrderPreservingBack (ring_mult z).
  Proof with auto.
    intros z [w Ew].
    repeat (split; try apply _). 
    intros x y [v Ev].
    destruct (total_order x y) as [| [u Eu]]...
    exists (0:nat). 
    rewrite <-Eu in *. clear Eu x.
    ring_simplify in Ev.  rewrite <-(rings.plus_0_r (z * y)) in Ev at 2. rewrite <-associativity in Ev.
    apply (left_cancellation (+) (z * y)) in Ev...
    destruct (naturals.zero_sum u (u * w + v)) as [E _].
      apply (injective (naturals_to_semiring nat R)).
      rewrite preserves_plus, preserves_plus, preserves_mult, preserves_0.
      rewrite <-Ev, <-Ew. ring.
    rewrite E, preserves_0. ring.
  Qed.

  Global Instance: ∀ (z : R), GeOne z → OrderPreservingBack (flip ring_mult z).
  Proof. intros. apply order_preserving_back_flip. Qed.
End contents.

Section with_naturals.
  Context `{SemiRing R}.
  Add Ring SR2: (stdlib_semiring_theory R).

  Lemma sr_precedes_with N `{Naturals N} {x y: R}: x ≤ y → ∃ z: N, x + naturals_to_semiring N R z = y.
  Proof.
   intros [z E].
   exists (naturals_to_semiring nat N z).
   posed_rewrite (naturals.to_semiring_unique (naturals_to_semiring N R ∘ naturals_to_semiring nat N) z).
   assumption.
  Qed.

  Lemma sr_precedes_from N `{Naturals N} {x y: R} (z: N): x + naturals_to_semiring N R z = y → x ≤ y.
  Proof.
   intros.
   exists (naturals_to_semiring N nat z).
   posed_rewrite (naturals.to_semiring_unique (naturals_to_semiring nat R ∘ naturals_to_semiring N nat) z).
   assumption.
  Qed.

  Lemma sr_preserves_nonneg `{SemiRing B} `{Naturals N} (f: R → B) `{!SemiRing_Morphism f}: 
   ∀ n: N, 0 ≤ f (naturals_to_semiring N R n).
  Proof.
   intros n. pattern n.
   apply theory.naturals.induction.
     intros x y E. rewrite <-E. intuition.
   do 2 rewrite preserves_0. reflexivity.
   intros m [x E].
   do 2 rewrite preserves_plus.
   rewrite <- E.
   rewrite plus_0_l.
   do 2 rewrite preserves_1.
   exists (1 + x).
   rewrite preserves_plus, preserves_1.
   apply plus_0_l.
  Qed. 

  Global Instance nats_preserve_sr_order `{SemiRing A} `{Naturals B} (f: A → B) `{!SemiGroup_Morphism f} :
    OrderPreserving f.
  Proof.
   repeat (split; try apply _).
   intros x y [z p].
   exists (naturals_to_semiring B nat (f (naturals_to_semiring nat A z))).
   rewrite <- p, preserves_sg_op.
   rewrite (naturals.to_semiring_involutive B nat).
   reflexivity.
  Qed.

  Lemma zero_sr_precedes_nat `{Naturals N} (n: N): 
    0 ≤ naturals_to_semiring N R n.
  Proof.
   exists (naturals_to_semiring N nat n).
   posed_rewrite (naturals.to_semiring_unique (naturals_to_semiring nat R ∘ naturals_to_semiring N nat) n).
   ring.
  Qed.
End with_naturals.

(* * Extra [sr_precedes] properties that hold in rings: *)
Section ring. 
  Context `{Ring R}.
  Add Ring R: (stdlib_ring_theory R).

  Lemma sr_precedes_flip (x y: R): x ≤ y ↔ -y ≤ -x.
  Proof.
   split; intros [z p]; exists z.
    rewrite <- p. ring.
   rewrite <- (inv_involutive x), <- p. ring.
  Qed.

  Lemma sr_precedes_0_flip (z: R): 0 ≤ z ↔ -z ≤ 0. 
  Proof with auto.
   split; intros E.
   rewrite <- opp_0. apply (proj1 (sr_precedes_flip _ _))...
   apply sr_precedes_flip. rewrite opp_0...
  Qed.

  Lemma neg_sr_precedes_pos `{Naturals N} (n m: N): 
    - naturals_to_semiring N R n ≤ naturals_to_semiring N R m.
  Proof. transitivity (0:R); [apply -> sr_precedes_0_flip |]; apply zero_sr_precedes_nat. Qed.

  Context  `{!RingMinus R}.
  Lemma sr_precedes_0_minus (x y : R) : 0 ≤ y - x ↔ x ≤ y.
  Proof.
    rewrite ring_minus_correct. 
    split; intros E.
    apply (order_preserving_back (flip (+) (-x))).
      unfold flip. rewrite plus_opp_r. assumption.
    apply (order_preserving_back (flip (+) x)).
      unfold flip. rewrite left_identity, <-associativity, plus_opp_l, right_identity. assumption.
  Qed.
End ring.
