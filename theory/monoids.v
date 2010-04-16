Set Automatic Introduction.

Require Import
  Program abstract_algebra canonical_names.

Section morphisms.

  Context (A B C: Type)
    `{!MonoidUnit A} `{!SemiGroupOp A} `{!Equiv A}
    `{!MonoidUnit B} `{!SemiGroupOp B} `{!Equiv B}
    `{!MonoidUnit C} `{!SemiGroupOp C} `{!Equiv C}
    (f: A → B) (g: B → C).

  Global Instance id_monoid_morphism `{!Monoid A}: Monoid_Morphism id.
  Proof. repeat (constructor; try apply _); reflexivity. Qed.

  Global Instance compose_monoid_morphisms
    `{!Monoid_Morphism f} `{!Monoid_Morphism g}: Monoid_Morphism (g ∘ f).
  Proof with try reflexivity.
   pose proof (monmor_b: Monoid C).
   pose proof monmor_b. pose proof monmor_a.
   repeat (constructor; try apply _); intros; unfold compose.
    do 2 rewrite preserves_sg_op...
   do 2 rewrite preserves_mon_unit...
  Qed.

End morphisms.
