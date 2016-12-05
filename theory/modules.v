From MathClasses
Require Import interfaces.vectorspace interfaces.canonical_names theory.groups theory.rings.
Require Import Coq.setoid_ring.Ring. (* `ring` tactic *)

(*
  A proof of the uniqueness of inverses is omitted, because it follows
  from the proof Injective (-) in groups.v
*)

Section Module_Lemmas.
  Context `{Module R M}.

  (* So we can use the `ring` tactic when we need to *)
  Add Ring my_ring : (stdlib_ring_theory R). 

  Lemma mult_rzero : forall x : M, 0 · x = mon_unit.
    intros.
    apply (mon_unit_unique (0 · x) (0 · x)).
    rewrite <- distribute_r.
    apply scalar_mult_proper.
     - ring. (* 0 + 0 = 0 *)
     - reflexivity. (* x = x *)
  Qed.

  Lemma mult_munit : forall c : R, c · mon_unit = mon_unit.
    intro c.
    rewrite <- right_identity.
    assert (intermediate : mon_unit = c · mon_unit & - (c · mon_unit)) by
      now rewrite right_inverse.
    rewrite intermediate at 2.
    rewrite associativity.
    rewrite <- distribute_l.
    now rewrite left_identity, right_inverse.
  Qed.

  Lemma multiplication_by_negative_1_is_negation : forall x : M, (-1) · x = - x.
    intros.
    assert (x & ((-1) · x) = mon_unit).
    {
      assert (Hone : 1 · x = x) by (apply lm_identity).
      rewrite <- Hone at 1.
      rewrite <- distribute_r.
      setoid_replace (1 - 1) with 0 by (apply right_inverse).
      apply mult_rzero.
    }
    setoid_replace (- x) with (- x & mon_unit) by (now rewrite right_identity).
    rewrite <- H0.
    rewrite associativity, left_inverse, left_identity.
    reflexivity.
  Qed.

  Lemma double_negation : forall x, - (- x) = x.
    intros.
    do 2 rewrite <- multiplication_by_negative_1_is_negation.
    rewrite associativity.
    setoid_replace (-1 * -1) with 1 by ring.
    apply lm_identity.
  Qed.

End Module_Lemmas.
