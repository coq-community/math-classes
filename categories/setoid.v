Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Inductive Object := object { T:> Type; e: T -> T -> Prop; setoid_proof: @Setoid T e }.
  (* We don't use the type [Equiv T] for e because it leads to universe consistency
   problems in theory/ua_forget. Hopefully when Coq gets universe polymorphism for
   definitions (like Equiv), we can use the proper type again. *)

Hint Extern 4 (Equiv (T ?x)) => exact (e x): typeclass_instances.
  (* Matthieu is adding [Existing Instance (c: T).], which is nicer. *)

Existing Instance setoid_proof.

Section contents.

  Global Instance: Arrows Object := fun A B => sig (@Setoid_Morphism A _ B _).

  Global Program Instance: forall x y: Object, Equiv (x --> y)
    := fun _ _ => respectful equiv equiv.

  Global Instance: forall x y: Object, Setoid (x --> y).
  Proof with intuition.
   intros x y.
   constructor.
     intros [? ?] ? ? E. rewrite E...
    intros ? ? E ? ? ?. symmetry...
   intros [? ?] [? ?] [? ?] ? ? ? ? ?.
   apply transitivity with (x1 x3)...
  Qed.

  Global Program Instance: CatId Object := fun _ => id.
  Global Program Instance: CatComp Object := fun _ _ _ => compose.
  Next Obligation. destruct x, x0. apply _. Qed.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv) (comp: (y --> z) -> (x --> y) -> (x --> z)).
  Proof. repeat intro. simpl. firstorder. Qed.

  Global Instance: Category Object.
  Proof.
   constructor; try apply _; intros; intros ? ? E; simpl; unfold compose;
    destruct a; try destruct b; try destruct c; simpl; rewrite E; reflexivity.
  Qed.

  Section product. Context {Index: Type} (c: Index -> Object).

    Definition product_obj: Object := object (forall i, c i) (fun x y => forall i, x i == y i) _.

    Program Definition project i: product_obj --> c i := (fun x => x i).
    Next Obligation. constructor; try apply _. firstorder. Qed.

    Program Definition factor (d: Object) (df: forall i, d --> c i): d --> product_obj := fun x y => df y x.
    Next Obligation. constructor; try apply _. intros ?? E ?. destruct df. rewrite E. reflexivity. Qed.

  End product.

  Instance: Producer Object Arrow := fun I c => mkProduct c (product_obj c) (project c) (factor c).

  Instance: Produces Object.
  Proof.
   split.
    intros ? ? ? E. simpl. unfold compose. destruct ccomp. rewrite E. reflexivity.
   intros ? E' ? x E. intro. simpl in *.
   symmetry in E |- *.
   apply (E' i _ _ E).
  Qed.

  Global Instance mono: forall (X Y: Object) (a: X --> Y), @Injective X _ Y _ (@proj1_sig _ (@Setoid_Morphism _ _ _ _) a) -> Mono a.
  Proof. (* todo: why so ugly? *)
   intros ? ? ? ? ? ? ? E ? ? U.
   pose proof (E _ _ U).
   firstorder.
  Qed.

End contents.