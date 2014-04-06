 (* We define what a ring ideal is, show that they yield congruences,
 define what a kernel is, and show that kernels are ideal. *)
Require Import
  Ring abstract_algebra theory.rings.
Require Export
   theory.ring_congruence.

(* Require ua_congruence varieties.rings. *)

Class RingIdeal A (P : A → Prop) `{Ring A} : Prop :=
  { ideal_proper :> Proper ((=) ==> iff) P
  ; ideal_NonEmpty :> NonEmpty (sig P)
  ; ideal_closed_plus_negate : ∀ x y, P x → P y → P (x - y)
  ; ideal_closed_mult_r : ∀ x y, P x → P (x * y)
  ; ideal_closed_mult_l: ∀ x y, P y → P (x * y) }.

Notation Factor A P := (Quotient A (λ x y, P (x - y))).

Section ideal_congruence.
  Context `{ideal : RingIdeal A P}.
  Add Ring A2 : (rings.stdlib_ring_theory A).

  (* If P is an ideal, we can easily derive some further closedness properties: *)
  Hint Resolve (ideal_closed_plus_negate) (ideal_closed_mult_l) (ideal_closed_mult_r).

  Lemma ideal_closed_0 : P 0.
  Proof. destruct ideal_NonEmpty as [[x Px]]. rewrite <-(plus_negate_r x). intuition. Qed.
  Hint Resolve ideal_closed_0.

  Lemma ideal_closed_negate x : P x → P (-x).
  Proof. intros. rewrite <- rings.plus_0_l. intuition. Qed.
  Hint Resolve ideal_closed_negate.

  Lemma ideal_closed_plus x y : P x → P y → P (x + y).
  Proof. intros. assert (x + y = -(-x + -y)) as E by ring. rewrite E. intuition. Qed.
  Hint Resolve ideal_closed_plus.

  Global Instance: RingCongruence A (λ x y, P (x - y)).
  Proof.
    split.
        constructor.
          intros x. now rewrite plus_negate_r.
         intros x y E. rewrite negate_swap_r. intuition.
        intros x y z E1 E2. mc_setoid_replace (x - z) with ((x - y) + (y - z)) by ring. intuition.
       intros ?? E. now rewrite E, plus_negate_r.
      intros x1 x2 E1 y1 y2 E2.
      mc_setoid_replace (x1 + y1 - (x2 + y2)) with ((x1 - x2) + (y1 - y2)) by ring. intuition.
     intros x1 x2 E1 y1 y2 E2.
     mc_setoid_replace (x1 * y1 - (x2 * y2)) with ((x1 - x2) * y1 + x2 * (y1 - y2)) by ring. intuition.
    intros x1 x2 E.
    mc_setoid_replace (-x1 - - x2) with (-(x1 - x2)) by ring. intuition.
  Qed.

  Lemma factor_ring_eq (x y : Factor A P) : x = y ↔ P ('x - 'y).
  Proof. intuition. Qed.

  Lemma factor_ring_eq_0 (x y : Factor A P) : x = 0 ↔ P ('x).
  Proof.
    transitivity (P ('x - cast (Factor A P) A 0)).
     intuition.
    apply ideal_proper. unfold cast. simpl. ring.
  Qed.

(*
  Let hint := rings.encode_operations R.

  Instance: Congruence rings.sig (λ _, congr_equiv).
  Proof. constructor; intros; apply _. Qed.
*)
End ideal_congruence.

Section kernel_is_ideal.
  Context `{Ring A} `{Ring B} `{f : A → B} `{!SemiRing_Morphism f}.

  Add Ring A3 : (rings.stdlib_ring_theory A).
  Add Ring B3 : (rings.stdlib_ring_theory B).

  Definition kernel : A → Prop := (= 0) ∘ f.

  Global Instance: RingIdeal A kernel.
  Proof with ring.
   unfold kernel, compose, flip.
   split.
       intros ? ? E. now rewrite E.
      split. exists (0:A). apply preserves_0.
     intros ?? E E'. rewrite preserves_plus, preserves_negate, E, E'...
    intros ?? E. rewrite preserves_mult, E...
   intros ?? E. rewrite preserves_mult, E...
  Qed.
End kernel_is_ideal.
