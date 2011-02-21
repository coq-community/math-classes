Require
  theory.rings categories.variety.
Require Import
  Program Morphisms
  abstract_algebra universal_algebra.

Definition op := False.

Definition sig: Signature := Build_Signature False False (False_rect _).

Definition Laws (_: EqEntailment sig): Prop := False.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.

Let carriers := False_rect _: sorts sig → Type.

Instance: Equiv (carriers a).
Proof. intros []. Qed.

Instance implementation: AlgebraOps sig carriers := λ o, False_rect _ o.

Global Instance: Algebra sig _.
Proof. constructor; intuition. Qed.

Instance variety: InVariety theory carriers.
Proof. constructor; intuition. Qed.

Definition Object := variety.Object theory.
Definition object: Object := variety.object theory carriers.
