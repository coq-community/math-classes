(* "Forgetting" a variety's laws (but keeping the algebraic operations) is a trivial functor. *)

Require Import universal_algebra interfaces.functors theory.categories.
Require categories.variety categories.algebra.

Section contents.

  Variable et: EquationalTheory.

  Definition forget (v: variety.Object et) := algebra.object et v.

  Global Instance: Fmap forget := λ _ _ => id.

  Global Instance: Functor forget _.
  Proof. constructor. intros. apply _. reflexivity. repeat intro. reflexivity. Qed.

End contents.
