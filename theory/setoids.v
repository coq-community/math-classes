Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program.

Section product.

  Context (I: Type) (c: I -> Type) `{forall i, Equiv (c i)} `{forall i, Setoid (c i)}.

  Let product: Type := forall i, c i.

  Global Instance: Equiv product := fun x y => forall i, x i == y i.

  Global Instance: Setoid product.
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ?. symmetry. apply E.
   intros ? y ? ? ? i. transitivity (y i); firstorder.
  Qed.

  Global Instance projection_morphism: forall i: I, Setoid_Morphism (fun c: product => c i).
  Proof. firstorder. Qed.

End product.

Instance id_setoid_morphism `{Setoid T}: @Setoid_Morphism T e T e id.

Instance compose_setoid_morphisms (A B C: Type)
  `{!Equiv A} `{!Equiv B} `{!Equiv C} (f: A -> B) (g: B -> C)
  {P: Setoid_Morphism f} {Q: Setoid_Morphism g}: Setoid_Morphism (g ∘ f).
Proof. destruct P, Q. constructor; apply _. Qed.

Global Instance sig_Setoid `{e: Equiv A} (P: A -> Prop) `{!Setoid A}: Setoid (sig P).

Global Instance sigT_Setoid `{e: Equiv A} (P: A -> Type) `{!Setoid A}: Setoid (sigT P).
