Require Import
  abstract_algebra interfaces.functors.

Definition Empty_map {A: Empty_set → Type} : ∀ x : Empty_set, A x := λ x, match x with end.
Local Notation E := Empty_map.

Instance: Arrows Empty_set := E.
Instance: CatComp Empty_set := E.
Instance: CatId Empty_set := E.
Instance: ∀ x y, Equiv (x ⟶ y) := E.
Instance: ∀ x y, Setoid (x ⟶ y) := E.
Instance: Category Empty_set.
Proof. constructor; exact E. Qed.

Section another_category.
  Context `{Category C}.

  Global Instance: Fmap (E: _ → C) := E.

  Global Instance: Functor (E: _ → C) E.
  Proof. constructor; exact E || typeclasses eauto. Qed.
End another_category.
