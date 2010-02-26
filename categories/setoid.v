Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Inductive Object := object { T:> Type; e: T → T → Prop; setoid_proof: @Setoid T e }.
  (* We don't use the type [Equiv T] for e because it leads to universe consistency
   problems in theory/ua_forget. Hopefully when Coq gets universe polymorphism for
   definitions (like Equiv), we can use the proper type again. *)

Hint Extern 4 (Equiv (T ?x)) => exact (e x): typeclass_instances.
  (* Matthieu is adding [Existing Instance (c: T).], which is nicer. *)

Existing Instance setoid_proof.

Section contents.

  Global Instance: Arrows Object := λ A B => sig (@Setoid_Morphism A B _ _).

  Global Program Instance: Π x y: Object, Equiv (x ⟶ y)
    := λ _ _ => respectful equiv equiv.

  Global Instance: Π x y: Object, Setoid (x ⟶ y).
  Proof with intuition.
   intros x y.
   constructor.
     intros [? ?] ? ? E. rewrite E...
    intros ? ? E ? ? ?. symmetry...
   intros [? ?] [? ?] [? ?] ? ? ? ? ?.
   apply transitivity with (x1 x3)...
  Qed.

  Global Program Instance: CatId Object := λ _ => id.
  Global Program Instance: CatComp Object := λ _ _ _ => compose.
  Next Obligation. destruct x, x0. apply _. Qed.

  Global Instance: Π x y z: Object, Proper (equiv ==> equiv ==> equiv) (comp: (y ⟶ z) → (x ⟶ y) → (x ⟶ z)).
  Proof. repeat intro. simpl. firstorder. Qed.

  Global Instance: Category Object.
  Proof.
   constructor; try apply _; intros; intros ? ? E; simpl; unfold compose;
    destruct a; try destruct b; try destruct c; simpl; rewrite E; reflexivity.
  Qed.

  Global Instance: Producer Object := λ _ c => object (Π i, c i) (λ x y => Π i, x i = y i) _.
    (* todo: use pointwise_relation or something like that *)

  Section product. Context {Index: Type} (c: Index → Object).

    Global Program Instance: ElimProduct c (product c) := λ i x => x i.
    Next Obligation. constructor; try apply _. firstorder. Qed.

    Global Program Instance: IntroProduct c (product c) := λ d df x y => df y x.
    Next Obligation. constructor; try apply _. repeat intro. destruct df. simpl. firstorder. Qed.

    Global Instance: Product c (product c).
    Proof.
     split.
      intros ? ? ? E. simpl. unfold compose. destruct ccomp. rewrite E. reflexivity.
     intros ? E' ? x E. intro. simpl in *.
     symmetry in E |- *.
     apply (E' i _ _ E).
    Qed.

  End product.

  Global Instance: HasProducts Object.

  Global Instance mono: Π (X Y: Object) (a: X ⟶ Y), @Injective X _ Y _ (@proj1_sig _ (@Setoid_Morphism _ _ _ _) a) → Mono a.
  Proof. (* todo: why so ugly? *)
   intros ? ? ? ? ? ? ? E ? ? U.
   pose proof (E _ _ U).
   firstorder.
  Qed.

End contents.
