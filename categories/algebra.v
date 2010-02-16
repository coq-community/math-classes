(* Show that algebras with homomorphisms between them form a category. *)

Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program universal_algebra theory.categories.
Require
  categories.cat categories.setoid categories.product.

Section contents.

  Variable sign: Signature.

  Record Object: Type := object
    { algebra_carriers:> sorts sign -> Type
    ; algebra_equiv: forall a, Equiv (algebra_carriers a)
    ; algebra_ops: AlgebraOps sign algebra_carriers
    ; algebra_proof: Algebra sign algebra_carriers
    }.

  Global Implicit Arguments object [[algebra_equiv] [algebra_ops] [algebra_proof]].

  Global Existing Instance algebra_equiv.
  Global Existing Instance algebra_ops.
  Global Existing Instance algebra_proof.

  Global Instance: Arrows Object := fun (X Y: Object) => sig (HomoMorphism sign X Y).

  Program Definition arrow `{Algebra sign A} `{Algebra sign B}
    f `{!HomoMorphism sign A B f}: object A --> object B := f.

  Global Program Instance: CatId Object := fun _ _ => id.

  Global Program Instance comp: CatComp Object := fun _ _ _ f g v => f v ∘ g v.
  Next Obligation. destruct f, g. apply _. Qed.

  Global Program Instance: forall x y: Object, Equiv (x --> y)
    := fun _ _ x y => forall b, pointwise_relation _ equiv (x b) (y b).

  Global Instance: forall x y: Object, Setoid (x --> y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: Proper (equiv ==> equiv ==> equiv) (comp x y z).
  Proof.
   intros ? ? ? x0 ? E ? ? F ? ?.
   simpl. unfold compose. do 3 red in E, F.
   destruct (proj2_sig x0). rewrite F, E. reflexivity.
  Qed.

  Global Instance: Category Object.
  Proof. constructor; try apply _; repeat intro; unfold equiv; reflexivity. Qed.

  (* Definition obj: cat.Object := cat.Build_Object Object Arrow e _ _ _.
    Risks universe inconsistencies.. *)

End contents.
