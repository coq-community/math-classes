Require Import
  abstract_algebra theory.setoids interfaces.functors theory.categories.
Require categories.setoids.

Section contents.
  Context `{Category C} (x: C).

  Definition homFrom (y: C): setoids.Object := setoids.object (x ⟶ y).

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
