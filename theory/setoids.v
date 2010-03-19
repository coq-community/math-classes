Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program.

Section simple_product.

  Context `{Setoid A} `{Setoid B}.

  Global Instance: Equiv (A * B) := λ p q => fst p = fst q ∧ snd p = snd q.

  Global Instance: Setoid (A * B).
  Proof. firstorder. Qed.

  Global Instance: Setoid_Morphism (@fst A B).
  Proof. constructor; try apply _. firstorder. Qed.

  Global Instance: Setoid_Morphism (@snd A B).
  Proof. constructor; try apply _. firstorder. Qed.

End simple_product.

Section product.

  Context (I: Type) (c: I → Type) `{Π i, Equiv (c i)} `{Π i, Setoid (c i)}.

  Let product: Type := Π i, c i.

  Global Instance: Equiv product := `(Π i, x i = y i).

  Global Instance: Setoid product.
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ?. symmetry. apply E.
   intros ? y ? ? ? i. transitivity (y i); firstorder.
  Qed.

  Global Instance projection_morphism i: Setoid_Morphism (λ c: product => c i).
  Proof. firstorder. Qed.

End product.

Instance id_setoid_morphism `{Setoid T}: @Setoid_Morphism T T _ _ id.

Instance compose_setoid_morphisms (A B C: Type)
  `{!Equiv A} `{!Equiv B} `{!Equiv C} (f: A → B) (g: B → C)
  {P: Setoid_Morphism f} {Q: Setoid_Morphism g}: Setoid_Morphism (g ∘ f).
Proof. destruct P, Q. constructor; apply _. Qed.

Global Instance sig_Setoid `{Setoid A} (P: A → Prop): Setoid (sig P).
Global Instance sigT_Setoid `{Setoid A} (P: A → Type): Setoid (sigT P).
