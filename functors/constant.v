Require Import
  MathClasses.theory.categories MathClasses.interfaces.abstract_algebra MathClasses.interfaces.functors.

Section constant_functor.
  Context `{Category A} `{Category B}.
  Context (b:B).

  Notation F := (const b: A → B).
  Global Instance: Fmap F := λ _ _ _, cat_id.

  Global Instance: ∀ a a' : A, Setoid_Morphism (fmap F : (a ⟶ a') → (F a ⟶ F a')).
  Proof.
    intros; constructor; try apply _.
    now intros ? ? ?.
  Qed.

  Global Instance ConstantFunctor : Functor F (λ _ _ _, cat_id).
  Proof.
    split; try apply _.
     reflexivity.
    intros; symmetry; compute; apply left_identity.
  Qed.
End constant_functor.

Set Warnings "-unsupported-attributes". (* FIXME: remove when minimal Coq version is enough *)

#[global]
Typeclasses Transparent const.

Set Warnings "+unsupported-attributes".

Section constant_transformation.
  Context `{Category A} `{Category J}.
  Context {a a' : A}.

  Global Instance constant_transformation {f : a⟶a'} : NaturalTransformation (const f : J → _).
  Proof. intros ? ? ?. now rewrite left_identity, right_identity. Qed.
End constant_transformation.
