Require Import
    Morphisms RelationClasses Equivalence Setoid
    categories abstract_algebra functors.

Global Instance: Arrows unit := fun _ _ => unit.
Global Instance: CatId unit := fun _ => tt.
Global Instance: CatComp unit := fun _ _ _ _ _ => tt.
Section e.
Context (x y: unit).
Global Instance: Equiv (x⟶y) := eq.
Global Instance: Setoid (x⟶y).
End e.
Global Instance: Category unit.
Proof.
 constructor; try constructor; compute; repeat intro; repeat match goal with [ x : unit |- _ ] => destruct x end; reflexivity.
Qed.
