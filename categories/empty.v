Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.functors.

Definition Empty_map {A: Empty_set → Type} : ∀ x : Empty_set, A x := λ x, match x with end.
Local Notation E := Empty_map.

#[global]
Instance: Arrows Empty_set := E.
#[global]
Instance: CatComp Empty_set := E.
#[global]
Instance: CatId Empty_set := E.
#[global]
Instance: ∀ x y, Equiv (x ⟶ y) := E.
#[global]
Instance: ∀ x y, Setoid (x ⟶ y) := E.
#[global]
Instance: Category Empty_set.
Proof. constructor; exact E. Qed.

Section another_category.
  Context `{Category C}.

  Global Instance: Fmap (E: _ → C) := E.

  Global Instance: Functor (E: _ → C) E.
  Proof. constructor; exact E || typeclasses eauto. Qed.
End another_category.
