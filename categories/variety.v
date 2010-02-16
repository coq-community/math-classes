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

  Global Instance: Arrows Object := fun X Y: Object => sig (HomoMorphism et X Y).

  Program Definition arrow `{Variety et A} `{Variety et B}
    f `{!HomoMorphism et A B f}: object A --> object B := f.

  Global Program Instance: CatId Object := fun _ _ => id.

  Global Program Instance: CatComp Object := fun _ _ _ f g v => f v ∘ g v.
  Next Obligation. destruct f, g. apply _. Qed.

  Global Program Instance: forall (x y: Object), Equiv (x --> y)
    := fun _ _ x y => forall b, pointwise_relation _ equiv (x b) (y b).

  Global Instance: forall (x y: Object), Setoid (x --> y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: forall (x y z: Object), Proper (equiv ==> equiv ==> equiv) (comp: y --> z -> x --> y -> x --> z).
  Proof.
   intros ??? [? [??]] ? E ?? F ??. simpl.
   unfold compose. rewrite (F _ _), (E _ _). reflexivity.
  Qed.

  Global Instance: Category Object.
  Proof. constructor; try apply _; repeat intro; unfold equiv; reflexivity. Qed.

  (* Definition obj: cat.Object := cat.object Object Arrow e _ _ _.
    Defining this causes a universe inconsistency when this module
    is imported in theory/ua_forget.. *)

End contents.
