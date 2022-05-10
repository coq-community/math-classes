Require Import
  Coq.Classes.RelationClasses Coq.Classes.Equivalence
  MathClasses.categories.categories MathClasses.interfaces.abstract_algebra MathClasses.categories.functors.

#[global]
Instance: Arrows unit := λ _ _, unit.
#[global]
Instance: CatId unit := λ _, tt.
#[global]
Instance: CatComp unit := λ _ _ _ _ _, tt.
#[global]
Instance: ∀ x y : unit, Equiv (x ⟶ y) := λ _ _, eq.
#[global]
Instance: ∀ x y : unit, Setoid (x ⟶ y) := {}.

#[global]
Instance: Category unit.
Proof.
 constructor; try constructor; compute; repeat intro;
   repeat match goal with [ x : unit |- _ ] => destruct x end; reflexivity.
Qed.
