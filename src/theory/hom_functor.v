Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra setoids interfaces.functors categories.
Require categories.setoid.

Section contents.

  Context `{Category C} (x: C).

  Definition homFrom (y: C): setoid.Object := @setoid.object (x ⟶ y) _ _.

  Global Program Instance: Fmap homFrom := λ v w X, (X ◎): (x ⟶ v) → (x ⟶ w).
  Next Obligation. constructor; apply _. Qed.

  Global Instance: Functor homFrom _.
  Proof.
   constructor; try apply _.
     constructor; try apply _.
     repeat intro. simpl in *.
     apply comp_proper; auto.
    repeat intro.
    simpl.
    rewrite H1.
    apply left_identity.
   repeat intro.
   simpl.
   unfold compose.
   rewrite H1.
   symmetry.
   apply comp_assoc.
  Qed.

End contents.
