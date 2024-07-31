From Coq Require Export RelationClasses Relation_Definitions Lia.

Module FastDoneTactic.

Lemma not_symmetry {A} `{R : relation A, !Symmetric R} x y : ~ R x y -> ~ R y x.
Proof. intuition. Qed.

Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | apply not_symmetry; eassumption
    | reflexivity ].
Tactic Notation "fast_by" tactic(tac) :=
  tac; fast_done.

End FastDoneTactic.

Import FastDoneTactic.

Ltac done :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    (* All the tactics below will introduce themselves anyway, or make no sense
       for goals of product type. So this is a good place for us to do it. *)
    | progress intros
    | solve [symmetry; trivial]
    | solve [apply not_symmetry; trivial]
    | discriminate
    | contradiction
    | split
    | match goal with H : ~ _ |- _ => case H; clear H; fast_done end ]
  ].

