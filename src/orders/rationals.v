Require
  theory.naturals.
Require Import
  Relation_Definitions Morphisms Ring Field
  abstract_algebra interfaces.naturals interfaces.rationals 
  theory.rationals theory.fields theory.rings.

(* Todo: prove that a total ring order uniquely specifices the order on the rationals *)

Section default_order. 
  Context `{Rationals Q}.

  Add Field F: (stdlib_field_theory Q).
  Notation n_to_sr := (naturals_to_semiring nat Q).

  Global Instance rationals_precedes: Order Q | 9 := λ x y,
    ∃ num, ∃ den, y = x + n_to_sr num * / n_to_sr den.

  Instance field_precedes_proper: Proper ((=) ==> (=) ==> iff) rationals_precedes.
  Proof with assumption.
    intros x x' E y y' E'. unfold rationals_precedes.
    split; intros [n [d U]]; exists n, d.
     rewrite <-E, <-E'...
    rewrite E, E'...
  Qed.

  Instance: Reflexive rationals_precedes.
  Proof. intro. exists (0:nat), (0:nat). rewrite preserves_0. ring. Qed.

  (* rationals_precedes can actually only happen if the denominator is nonzero: *)
  Lemma rationals_precedes_with_nonzero_denominator (x y: Q) : 
    x ≤ y → ∃ num, ∃ den, den ≠ 0 ∧ y = x + n_to_sr num * / n_to_sr den.
  Proof with eauto.
    intros [n [d E]].
    destruct (decide (d = 0)) as [A|A]...
    exists (0:nat), (1:nat).
    split. discriminate.
    rewrite E, A, preserves_0, preserves_1, dec_mult_inv_0.
    ring.
  Qed.

  Instance: Transitive rationals_precedes.
  Proof with auto.
    intros x y z E1 E2.
    destruct (rationals_precedes_with_nonzero_denominator x y) as [n1 [d1 [A1 B1]]]...
    destruct (rationals_precedes_with_nonzero_denominator y z) as [n2 [d2 [A2 B2]]]...
    exists (n1 * d2 + n2 * d1), (d1 * d2).
    rewrite B2, B1.
    rewrite preserves_plus.
    repeat rewrite preserves_mult.
    field. split; apply injective_not_0...
  Qed.

  Instance: AntiSymmetric rationals_precedes.
  Proof with auto.
    intros x y E1 E2. 
    destruct (rationals_precedes_with_nonzero_denominator x y) as [n1 [d1 [A1 B1]]]...
    destruct (rationals_precedes_with_nonzero_denominator y x) as [n2 [d2 [A2 B2]]]...
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
     intros x y [n [d E]]. exists n, d. rewrite E. ring.
    intros x [n1 [d1 E1]] y [n2 [d2 E2]].
    exists (n1 * n2), (d1 * d2).
    do 2 rewrite preserves_mult. 
    rewrite E1, E2, dec_mult_inv_distr. ring.
  Qed.

  (* Todo: prove that rationals_precedes is total *)
End default_order.
