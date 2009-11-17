Require Import Morphisms Structures RingOps.
Require Field_theory.

Lemma mult_inverse' `{Field F}: forall x p, x * // exist _ x p == 1.
Proof. intros. apply (mult_inverse (exist _ _ _)). Qed.

Section dec_mult_inv.

  Context `{e: Equiv A} `{RingZero A} `{!MultInv A} `{forall x y: A, Decision (x == y)}.
  Program Definition dec_mult_inv (x: A): A := if decide (x == 0) then 0 else // x.

  Context `{!Equivalence e} `{!Proper (sig_relation equiv _ ==> equiv) mult_inv}.
  Global Instance: Proper (e ==> e) dec_mult_inv.
  Proof.
   unfold dec_mult_inv. intros x y E.
   destruct (decide (x == 0)); destruct (decide (y == 0)).
      reflexivity.
     elimtype False. apply f. rewrite <- E. assumption.
    elimtype False. apply f. rewrite E. assumption.
   apply Proper0. assumption.
  Qed.

End dec_mult_inv.

Global Notation "/ x" := (dec_mult_inv x).

Definition Field_field_theory `{Field F} `{forall x y: F, Decision (x == y)}:
  Field_theory.field_theory 0 1 ring_plus ring_mult (fun x y => x + - y)
    group_inv (fun x y => x * / y) dec_mult_inv equiv.
Proof.
 intros.
 constructor.
    apply (Ring_ring_theory _).
   intro.
   apply field_0neq1.
   symmetry.
   assumption.
  reflexivity.
 intros.
 rewrite commutativity.
 unfold dec_mult_inv.
 destruct (decide (p == 0)). intuition.
 apply mult_inverse'.
Qed.
