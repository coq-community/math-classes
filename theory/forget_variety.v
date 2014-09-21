(* "Forgetting" a variety's laws (but keeping the algebraic operations) is a trivial functor. *)

Require Import
  canonical_names universal_algebra interfaces.functors
  theory.categories categories.varieties categories.algebras.

Section contents.

  Variable et: EquationalTheory.

  Definition forget (v: varieties.Object et) := algebras.object et v.

  Global Instance: Fmap forget := λ _ _, id.

  Global Instance: Functor forget _.
  Proof. constructor; intros; try apply _; repeat intro; reflexivity. Qed.

End contents.
