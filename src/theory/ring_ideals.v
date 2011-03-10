 (* We define what a ring ideal is, show that they yield congruences,
 define what a kernel is, and show that kernels are ideal. *)

Require Import
  Ring Morphisms Program
  ua_congruence abstract_algebra theory.rings.
Require varieties.ring.

Section ideal_congruence. 
  Context `{Ring R}.

  Add Ring R: (rings.stdlib_ring_theory R).

  Context (P: R → Prop) `{!Proper ((=) ==> iff) P}.

  (* P is an ideal if: *)

  Class Ideal: Prop :=
    { Ideal_NonEmpty:> NonEmpty P
    ; Ideal_closed_plus_opp: `(P x → P y → P (x + - y))
    ; Ideal_closed_mult_r: `(P x → P (x * y))
    ; Ideal_closed_mult_l: `(P y → P (x * y)) }.

  (* If P is an ideal, we can easily derive some further closedness properties: *)

  Hypothesis ideal: Ideal.

  Hint Resolve Ideal_closed_plus_opp Ideal_closed_mult_l Ideal_closed_mult_r.

  Lemma P0: P 0.
  Proof. destruct Ideal_NonEmpty. destruct non_empty. rewrite <- (plus_opp_r x). intuition. Qed.

  Hint Resolve P0.

  Lemma Pinv: `(P x → P (- x)).
  Proof. intros. rewrite <- rings.plus_0_l. intuition. Qed.

  Hint Resolve Pinv.

  Lemma Pplus: `(P x → P y → P (x + y)).
  Proof. intros. assert (x + y = -(-x + -y)) as E by ring. rewrite E. intuition. Qed.

  Hint Resolve Pplus.

  (* Next, we make a congruence: *)

  Program Instance congruence: Equiv R := λ x y, P (x + - y).

  Instance: Equivalence congruence.
  Proof with intuition.
   unfold congruence.
   constructor; repeat intro.
     rewrite plus_opp_r...
    rewrite opp_swap_r...
   assert (x + - z = (x + -y) + (y + - z)) as E by ring. rewrite E...
  Qed.

  Instance cong_proper: Proper ((=) ==> (=) ==> iff) congruence.
  Proof. intros ? ? E ? ? E'. unfold congruence. rewrite E, E'. intuition. Qed.

  Instance: Proper (congruence ==> congruence ==> congruence) (+).
  Proof.
   unfold congruence. repeat intro. 
   assert (x + x0 + - (y + y0) = (x + - y) + (x0 + - y0)) as E by ring.
   rewrite E. intuition.
  Qed.

  Instance: Proper (congruence ==> congruence ==> congruence) (.*.).
  Proof.
   unfold congruence. repeat intro. 
   assert (x * x0 + - (y * y0) = ((x + -y) * x0) + (y * (x0 + - y0))) as E by ring.
   rewrite E. intuition.
  Qed.

  Instance: Proper (congruence ==> congruence) (-).
  Proof.
   unfold congruence. repeat intro.
   assert (- x + - - y = -(x + -y)) as E by ring.
   rewrite E. intuition.
  Qed.

  Let hint := ring.encode_operations R.

  Instance: Congruence ring.sig (λ _, congruence).
  Proof.
   constructor. intro. apply _. apply ring.encode_algebra_and_ops.
   assert (∀ x y, @equiv _ e x y → congruence x y) as e_cong.
     unfold congruence. intros ? ? E. rewrite E, plus_opp_r. intuition.
   repeat (constructor; try apply _); repeat intro; apply e_cong; try firstorder.
  Qed.

  Instance: Ring R (e:=congruence).
  Proof.
   apply (@ring.decode_variety_and_ops (λ _, R) (λ _, congruence) hint).
   pose proof (ring.encode_variety_and_ops R).
   apply (quotient_variety ring.theory); try apply _.
   intros ? []; intuition.
  Qed.

End ideal_congruence.

Section kernel_is_ideal. 
  Context `{Ring A} `{Ring B} `{f : A → B} `{!SemiRing_Morphism f}.

  Add Ring A: (rings.stdlib_ring_theory A).
  Add Ring B: (rings.stdlib_ring_theory B).

  Definition kernel: A → Prop := (= 0) ∘ f.

  Global Instance: Ideal kernel.
  Proof with ring.
   unfold kernel, compose, flip.
   repeat split.
      exists 0. apply preserves_0.
     intros ?? E E'. rewrite preserves_plus, preserves_opp, E, E'...
    intros ?? E. rewrite preserves_mult, E...
   intros ?? E. rewrite preserves_mult, E...
  Qed.
End kernel_is_ideal.
