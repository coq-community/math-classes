(* "Forgetting" a variety's laws (but keeping the algebraic operations) is a trivial functor. *)

Require Import
  MathClasses.interfaces.canonical_names MathClasses.interfaces.universal_algebra MathClasses.interfaces.functors
  MathClasses.theory.categories MathClasses.categories.varieties MathClasses.categories.algebras.

Section contents.

  Variable et: EquationalTheory.

  Definition forget (v: varieties.Object et) := algebras.object et v.

  Global Instance: Fmap forget := λ _ _, id.

  Global Instance: Functor forget _.
  Proof. constructor; intros; try apply _; repeat intro; try reflexivity. 
  Qed.

End contents.
