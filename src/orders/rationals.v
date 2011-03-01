Require Import
  Morphisms Ring Field Program Setoid
  abstract_algebra interfaces.naturals interfaces.rationals interfaces.integers
  natpair_integers theory.rationals theory.fields theory.rings orders.integers orders.fields.

Section rationals_order.
  Context `{Rationals Q} {o : Order Q} `{!RingOrder o} `{!TotalOrder o}.
  Add Field Q : (stdlib_field_theory Q).

  Section another_integers.
  Context  Z `{Integers Z} {oZ : Order Z} `{!RingOrder oZ} `{!TotalOrder oZ}.

  Lemma rationals_decompose_pos_den x : ∃ num, ∃ den, 
    0 < den ∧ x = integers_to_ring Z Q num / integers_to_ring Z Q den.
  Proof.
    destruct (rationals_decompose x) as [num [den [E1 E2]]].
    destruct (total_order den 0).
     exists (-num). exists (-den). split.
      split.
       now apply rings.flip_nonpos_opp.
      intros G. apply E1. apply (injective (-)). rewrite <-G. symmetry. now apply opp_0.
     rewrite 2!preserves_opp. rewrite E2. field.
     split.
      intros G. apply E1.
      apply (injective (integers_to_ring Z Q)). apply (injective (-)).
      rewrite G. rewrite preserves_0. symmetry. now apply opp_0.
     now apply injective_ne_0.
    exists num. exists den. split; try assumption.
    split; try assumption. now apply not_symmetry.
  Qed.
  End another_integers.

  Section another_rationals.
  Context `{Rationals Q2} {o2 : Order Q2} `{!RingOrder o2} `{!TotalOrder o2}
     {f : Q → Q2} `{!SemiRing_Morphism f} `{!Injective f}.

  Notation i_to_r := (integers.integers_to_ring (SRpair nat) Q).

  Let f_preserves_nonneg x : 0 ≤ x → 0 ≤ f x.
  Proof.
    intros E.
    destruct (rationals_decompose_pos_den (SRpair nat) x) as [num [den [[E1a E1b] E2]]].
    rewrite E2 in E |- *. clear E2.
    rewrite preserves_mult, preserves_dec_mult_inv.
    apply (order_preserving_back_gt_0 (.*.) (f (i_to_r den))).
     change (0 < (f ∘ i_to_r) den).
     rewrite (integers.to_ring_unique _).
     split.
      apply (order_preserving (integers_to_ring (SRpair nat) Q2)) in E1a.
      now rewrite preserves_0 in E1a.
     apply not_symmetry. apply injective_ne_0. now apply not_symmetry.
    apply (order_preserving_ge_0 (.*.) (i_to_r den)) in E.
     rewrite right_absorb. rewrite right_absorb in E.
     rewrite (commutativity (f (i_to_r num))), associativity, dec_mult_inverse, left_identity.
      rewrite (commutativity (i_to_r num)), associativity, dec_mult_inverse, left_identity in E. 
       change (0 ≤ (f ∘ i_to_r) num).
       rewrite (integers.to_ring_unique _).
       rewrite <-(preserves_0 (f:=integers_to_ring (SRpair nat) Q2)).
       apply (order_preserving _).
       apply (order_preserving_back i_to_r).
       now rewrite preserves_0.
      apply injective_ne_0. now apply not_symmetry.
     change ((f ∘ i_to_r) den ≠ 0).
     apply injective_ne_0. now apply not_symmetry.
    apply (order_preserving i_to_r) in E1a.
    now rewrite preserves_0 in E1a.
  Qed.

  Instance morphism_order_preserving: OrderPreserving f.
  Proof. apply semirings.preserving_preserves_nonneg. apply f_preserves_nonneg. Qed.
  End another_rationals.
End rationals_order.

Section rationals_order_isomorphic.
  Context `{Rationals Q1} {o1 : Order Q1} `{!RingOrder o1} `{!TotalOrder o1}
    `{Rationals Q2} {o2 : Order Q2} `{!RingOrder o2} `{!TotalOrder o2}
     {f : Q1 → Q2} `{!SemiRing_Morphism f} `{!Injective f}.

  Global Instance: OrderEmbedding f.
  Proof.
    split.
     apply morphism_order_preserving.
    repeat (split; try apply _).
    intros x y E.
    rewrite <-(to_rationals_involutive x (Q2:=Q2)), <-(to_rationals_involutive y (Q2:=Q2)).
    rewrite <-2!(to_rationals_unique f).
    now apply (morphism_order_preserving (f:=rationals_to_rationals Q2 Q1)).
  Qed.
End rationals_order_isomorphic.

Global Instance rationals_precedes `{Rationals Q} : Order Q | 10 := λ x y,
    ∃ num, ∃ den, y = x + naturals_to_semiring nat Q num / naturals_to_semiring nat Q den.

Section default_order. 
  Context `{Rationals Q}.

  Add Field F: (stdlib_field_theory Q).
  Notation n_to_sr := (naturals_to_semiring nat Q).

  Instance: Proper ((=) ==> (=) ==> iff) rationals_precedes.
  Proof.
    intros x x' E y y' E'. unfold rationals_precedes.
    split; intros [n [d d_nonzero]]; exists n d.
     now rewrite <-E, <-E'.
    now rewrite E, E'.
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
    rewrite ?preserves_mult.
    field. split; now apply injective_ne_0.
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
      apply (left_cancellation_ne_0 (.*.) (/n_to_sr d1)).
       apply dec_mult_inv_nonzero. apply injective_ne_0...
      apply (left_cancellation_ne_0 (.*.) (/n_to_sr d2)).
       apply dec_mult_inv_nonzero. apply injective_ne_0...
      ring_simplify. replace (zero) with (0 : Q) by reflexivity. 
      rewrite B2. field.
      split; apply injective_ne_0...
     rewrite F. rewrite preserves_0. ring.
    contradiction.
  Qed.

  Global Instance: RingOrder rationals_precedes.
  Proof.
    repeat (split; try apply _).
     intros x y [n [d E]]. exists n d. rewrite E. ring.
    intros x [n1 [d1 E1]] y [n2 [d2 E2]].
    exists (n1 * n2) (d1 * d2).
    rewrite 2!preserves_mult. 
    rewrite E1, E2, dec_mult_inv_distr. ring.
  Qed.

  Notation i_to_r := (integers_to_ring (SRpair nat) Q).
  Global Instance: TotalOrder rationals_precedes.
  Proof with auto.
    assert (∀ xn xd yn yd, 0 < xd → 0 < yd → xn * yd ≤ yn * xd → i_to_r xn / i_to_r xd ≤ i_to_r yn / i_to_r yd).
     intros xn xd yn yd [xd_ge0 xd_ne0] [yd_ge0 yd_ne0] E.
     apply srorder_plus in E. destruct E as [z [Ez1 Ex2]].
     apply integers_precedes_plus in xd_ge0. apply integers_precedes_plus in yd_ge0. apply integers_precedes_plus in Ez1.
     destruct xd_ge0 as [xd' xd_ge0], yd_ge0 as [yd' yd_ge0], Ez1 as [z' Ez1].
     rewrite left_identity in xd_ge0, yd_ge0, Ez1.
     exists z'. exists (xd' * yd').
     assert (∀ a, (i_to_r ∘ naturals_to_semiring nat (SRpair nat)) a = n_to_sr a) as F.
      intros a. apply (naturals.to_semiring_unique _).
     rewrite preserves_mult, <-F, <-F, <-F.
     unfold compose. rewrite <-xd_ge0, <-yd_ge0, <-Ez1.
     transitivity ((i_to_r yn * i_to_r xd) / (i_to_r yd * i_to_r xd)).
      field. split; apply injective_ne_0; apply not_symmetry...
     rewrite <-preserves_mult, Ex2, preserves_plus, preserves_mult.
     field. split; apply injective_ne_0; apply not_symmetry...
    intros x y.
    destruct (rationals_decompose_pos_den (SRpair nat) x) as [xn [xd [E1x E2x]]].
    destruct (rationals_decompose_pos_den (SRpair nat) y) as [yn [yd [E1y E2y]]].
    rewrite E2x, E2y.
    destruct (total_order (xn * yd) (yn * xd)); [left | right]; auto.
  Qed.
End default_order.
