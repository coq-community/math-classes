From MathClasses.interfaces Require Import vectorspace canonical_names.
From MathClasses.theory Require Import groups.

(*
  A proof of the uniqueness of inverses is omitted, because it follows
  from the proof Injective (-) in groups.v
*)

Section Module_Lemmas.
  Context `{Module R M}.

  Lemma mult_rzero : forall x : M, 0 · x = mon_unit.
    intros.
    apply (mon_unit_unique (0 · x) (0 · x)).
    rewrite <- distribute_r.
    apply scalar_mult_proper; [apply right_identity | reflexivity].
  Qed.

End Module_Lemmas.
