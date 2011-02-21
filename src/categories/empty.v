Require Import abstract_algebra interfaces.functors.

Section contents.

Definition Empty_map {A:Empty_set → Type} : ∀ x:Empty_set, A x := fun x => match x with end.
Implicit Arguments Empty_map [[A]].
Local Notation E := Empty_map.
Global Instance: Arrows Empty_set := E.
Global Instance: CatComp Empty_set := E.
Global Instance: CatId Empty_set := E.
Global Instance: ∀ x y, Equiv (x⟶y) := E.
Global Instance: ∀ x y, Setoid (x⟶y) := E.
Global Instance: Category Empty_set.
Proof. constructor; exact E. Qed.

Context `{Category C}.
Global Instance: Fmap (E:_->C) := E.
Global Instance: Functor (E:_→C) E.
Proof. constructor; exact E || typeclasses eauto. Qed.

End contents.
