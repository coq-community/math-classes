Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.integers
  MathClasses.theory.integers MathClasses.theory.ring_ideals.

Definition is_multiple `{Equiv Z} `{Mult Z} (b x : Z) := ∃ k, x = b * k.
Notation Mod b := (Factor _ (is_multiple b)).

Section modular_ring.
  Context `{Ring Z} {b : Z}.
  Add Ring R : (rings.stdlib_ring_theory Z).

  Global Instance: RingIdeal Z (is_multiple b).
  Proof.
    unfold is_multiple. split.
        solve_proper.
       split. exists 0, 0. ring.
      intros x y [k1 E1] [k2 E2]. exists (k1 - k2). rewrite E1, E2. ring.
     intros x y [k E]. exists (y * k). rewrite E. ring.
    intros x y [k E]. exists (x * k). rewrite E. ring.
  Qed.

  Lemma modular_ring_eq (x y : Mod b) : x = y ↔ ∃ k, 'x = 'y + b * k.
  Proof. split; intros [k E]; exists k. rewrite <-E. ring. rewrite E. ring. Qed.
End modular_ring.
