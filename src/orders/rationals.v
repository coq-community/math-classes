Require
  theory.naturals.
Require Import
  Morphisms Ring Field Program Setoid
  abstract_algebra interfaces.naturals interfaces.rationals interfaces.integers
  natpair_integers theory.rationals theory.fields theory.rings orders.integers.

Section rationals_order.
  Context `{Rationals Q} {o : Order Q} `{!RingOrder o} `{!TotalOrder o}.
  Add Field Q : (stdlib_field_theory Q).

  Section another_integers.
  Context  Z `{Integers Z} {oZ : Order Z} `{!RingOrder oZ} `{!TotalOrder oZ}.

  Lemma rationals_decompose_pos_den x : ∃ num, ∃ den, 
    0 < den ∧ x = integers_to_ring Z Q num * / integers_to_ring Z Q den.
  Proof with trivial.
    destruct (rationals_decompose Z x) as [num [den [E1 E2]]].
    destruct (total_order den 0).
     exists (-num). exists (-den). split.
      split.
       apply rings.flip_nonpos_inv...
      intros G. apply E1. apply (injective group_inv). rewrite <-G. symmetry. apply opp_0.
     do 2 rewrite preserves_inv. rewrite E2. field.
     split.
      intros G. apply E1.
      apply (injective (integers_to_ring Z Q)). apply (injective group_inv).
      rewrite G. rewrite preserves_0. symmetry. apply opp_0.
     apply injective_not_0...
    exists num. exists den. split...
    split... apply not_symmetry...
  Qed.
  End another_integers.

  Section another_rationals.
  Context `{Rationals Q2} {oQ : Order Q2} `{!RingOrder oQ} `{!TotalOrder oQ}
     {f : Q → Q2} `{!Ring_Morphism f} `{!Injective f}.

  Notation i_to_r := (integers.integers_to_ring (SRpair nat) Q).

  Let f_preserves_0 x : 0 ≤ x → 0 ≤ f x.
  Proof with trivial.
    intros E.
    destruct (rationals_decompose_pos_den (SRpair nat) x) as [num [den [[E1a E1b] E2]]].
    rewrite E2 in E |- *. clear E2.
    rewrite preserves_mult, preserves_dec_mult_inv.
    apply (maps.order_preserving_back_gt_0 ring_mult (f (i_to_r den))).
     change (0 < (f ∘ i_to_r) den).
     rewrite (integers.to_ring_unique _).
     split.
      apply (order_preserving (integers_to_ring (SRpair nat) Q2)) in E1a.
      rewrite preserves_0 in E1a...
     apply not_symmetry. apply (injective_not_0). apply not_symmetry...
    apply (maps.order_preserving_ge_0 ring_mult (i_to_r den)) in E.
     rewrite right_absorb. rewrite right_absorb in E.
     rewrite (commutativity (f (i_to_r num))), associativity, dec_mult_inverse, left_identity.
      rewrite (commutativity (i_to_r num)), associativity, dec_mult_inverse, left_identity in E. 
       change (0 ≤ (f ∘ i_to_r) num).
       rewrite (integers.to_ring_unique _).
       rewrite <-(preserves_0 (f:=integers_to_ring (SRpair nat) Q2)).
       apply (order_preserving _).
       apply (order_preserving_back i_to_r).
       rewrite preserves_0...
      apply (injective_not_0). apply not_symmetry...
     change ((f ∘ i_to_r) den ≠ 0).
     apply (injective_not_0). apply not_symmetry...
    apply (order_preserving i_to_r) in E1a.
    rewrite preserves_0 in E1a...
  Qed.

  Instance morphism_order_preserving: OrderPreserving f.
  Proof with trivial.
    apply semirings.preserving_preserves_0. apply f_preserves_0.
  Qed.
  End another_rationals.
End rationals_order.

Section default_order. 
  Context `{Rationals Q}.

  Add Field F: (stdlib_field_theory Q).
  Notation n_to_sr := (naturals_to_semiring nat Q).

  Global Instance rationals_precedes: Order Q | 9 := λ x y,
    ∃ num, ∃ den, y = x + n_to_sr num * / n_to_sr den.

  Instance field_precedes_proper: Proper ((=) ==> (=) ==> iff) rationals_precedes.
  Proof with assumption.
    intros x x' E y y' E'. unfold rationals_precedes.
    split; intros [n [d U]]; exists n d.
     rewrite <-E, <-E'...
    rewrite E, E'...
  Qed.

  Instance: Reflexive rationals_precedes.
  Proof. intro. exists (0:nat) (0:nat). rewrite preserves_0. ring. Qed.

  (* rationals_precedes can actually only happen if the denominator is nonzero: *)
  Lemma rationals_precedes_decompose (x y: Q) : 
    x ≤ y → ∃ num, ∃ den, den ≠ 0 ∧ y = x + n_to_sr num * / n_to_sr den.
  Proof with eauto.
    intros [n [d E]].
    destruct (decide (d = 0)) as [A|A]...
    exists (0:nat) (1:nat).
    split. discriminate.
    rewrite E, A, preserves_0, preserves_1, dec_mult_inv_0.
    ring.
  Qed.

  Instance: Transitive rationals_precedes.
  Proof with auto.
    intros x y z E1 E2.
    destruct (rationals_precedes_decompose x y) as [n1 [d1 [A1 B1]]]...
    destruct (rationals_precedes_decompose y z) as [n2 [d2 [A2 B2]]]...
    exists (n1 * d2 + n2 * d1) (d1 * d2).
    rewrite B2, B1.
    rewrite preserves_plus.
    repeat rewrite preserves_mult.
    field. split; apply injective_not_0...
  Qed.

  Instance: AntiSymmetric rationals_precedes.
  Proof with auto.
    intros x y E1 E2. 
    destruct (rationals_precedes_decompose x y) as [n1 [d1 [A1 B1]]]...
    destruct (rationals_precedes_decompose y x) as [n2 [d2 [A2 B2]]]...
    rewrite B1 in B2 |- *.
    clear E1 E2 B1 y.
    rewrite <-associativity in B2. rewrite <-(plus_0_r x) in B2 at 1.
    apply (left_cancellation (+) x) in B2.
    destruct (zero_product n1 d2) as [F|F]...
      apply naturals.zero_sum with (d1 * n2).
      apply (injective n_to_sr).
      rewrite preserves_plus, preserves_mult, preserves_mult, preserves_0.
      apply (left_cancellation_ne_0 ring_mult (/n_to_sr d1)).
       apply dec_mult_inv_nonzero. apply injective_not_0...
      apply (left_cancellation_ne_0 ring_mult (/n_to_sr d2)).
       apply dec_mult_inv_nonzero. apply injective_not_0...
      ring_simplify. replace (zero) with (0 : Q) by reflexivity. 
      rewrite B2. field.
      split; apply injective_not_0...
     rewrite F. rewrite preserves_0. ring.
    contradiction.
  Qed.

  Global Instance: RingOrder rationals_precedes.
  Proof.
    repeat (split; try apply _).
     intros x y [n [d E]]. exists n d. rewrite E. ring.
    intros x [n1 [d1 E1]] y [n2 [d2 E2]].
    exists (n1 * n2) (d1 * d2).
    do 2 rewrite preserves_mult. 
    rewrite E1, E2, dec_mult_inv_distr. ring.
  Qed.

  (* Todo: prove that rationals_precedes is total *)
End default_order.
