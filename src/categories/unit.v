Require Import
  Morphisms RelationClasses Equivalence Setoid
  categories abstract_algebra functors.

Instance: Arrows unit := λ _ _, unit.
Instance: CatId unit := λ _, tt.
Instance: CatComp unit := λ _ _ _ _ _, tt.
Instance: ∀ x y : unit, Equiv (x ⟶ y) := λ _ _, eq.
Instance: ∀ x y : unit, Setoid (x ⟶ y).

Instance: Category unit.
Proof.
 constructor; try constructor; compute; repeat intro; 
   repeat match goal with [ x : unit |- _ ] => destruct x end; reflexivity.
Qed.
