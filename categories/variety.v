(* Show that Varieties with homomorphisms between them form a category.

Hm, this file is almost identical to categories/algebra because the morphism are the same. There must be some way to
factor out the commonality.

 *)

Set Automatic Introduction.

Require Import Morphisms abstract_algebra Program universal_algebra.
Require categories.cat.

Section contents.

  Variable et: EquationalTheory.

  Record Object: Type := object
    { variety_carriers:> sorts et -> Type
    ; variety_equiv: forall a, Equiv (variety_carriers a)
    ; variety_op: AlgebraOps et variety_carriers
    ; variety_proof: Variety et variety_carriers
    }.

  Global Implicit Arguments object [[variety_equiv] [variety_op] [variety_proof]].

  Global Existing Instance variety_equiv.
  Global Existing Instance variety_op.
  Global Existing Instance variety_proof.

  Definition Arrow (X Y: Object): Type := sig (HomoMorphism et X Y).

  Program Definition arrow `{Variety et A} `{Variety et B}
    f `{!HomoMorphism et A B f}: Arrow (object A) (object B) := f.


  Program Definition arrow' {A B: Object} f `{!HomoMorphism et A B f}: Arrow A B := f.


  Global Program Instance: CatId Object Arrow := fun _ _ => id.

  Global Program Instance comp: CatComp Object Arrow := fun _ _ _ f g v => (`f) v ∘ (`g) v.
  Next Obligation. destruct f, g. apply _. Qed.

  Global Program Instance e x y: Equiv (Arrow x y)
    := fun x y => forall b, pointwise_relation _ equiv (x b) (y b).

  Global Instance: forall x y, Equivalence (e x y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: Proper (equiv ==> equiv ==> equiv) (comp x y z).
  Proof.
   intros ? ? ? x0 ? E ? ? F ? ?.
   simpl. unfold compose. unfold equiv, e, pointwise_relation in E, F.
   destruct (proj2_sig x0). unfold equiv. rewrite F, E. reflexivity.
  Qed.

  Global Instance cat: Category Object Arrow.
  Proof. constructor; try apply _; repeat intro; unfold equiv; reflexivity. Qed.

  (* Definition obj: cat.Object := cat.object Object Arrow e _ _ _.
    Defining this causes a universe inconsistency when this module
    is imported in theory/ua_forget.. *)

End contents.
