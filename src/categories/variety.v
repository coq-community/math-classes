(* Show that Varieties with homomorphisms between them form a category.

Hm, this file is almost identical to categories/algebra because the morphism are the same. There must be some way to
factor out the commonality.

 *)
Require Import Morphisms abstract_algebra Program universal_algebra ua_homomorphisms.

Section contents.

  Variable et: EquationalTheory.

  Record Object: Type := object
    { variety_carriers:> sorts et → Type
    ; variety_equiv: ∀ a, Equiv (variety_carriers a)
    ; variety_op: AlgebraOps et variety_carriers
    ; variety_proof: InVariety et variety_carriers
    }.

  Global Implicit Arguments object [[variety_equiv] [variety_op] [variety_proof]].

  Global Existing Instance variety_equiv.
  Global Existing Instance variety_op.
  Global Existing Instance variety_proof.

  Global Instance: Arrows Object := λ X Y: Object, sig (HomoMorphism et X Y).

  Program Definition arrow `{InVariety et A} `{InVariety et B}
    f `{!HomoMorphism et A B f}: object A ⟶ object B := f.

  Global Program Instance: CatId Object := λ _ _, id.

  Global Program Instance: CatComp Object := λ _ _ _ f g v, f v ∘ g v.
  Next Obligation. destruct f, g. apply _. Qed.

  Global Program Instance: ∀ (x y: Object), Equiv (x ⟶ y)
    := λ _ _ x y, ∀ b, pointwise_relation _ (=) (x b) (y b).

  Global Instance: ∀ (x y: Object), Setoid (x ⟶ y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: ∀ (x y z: Object), Proper ((=) ==> (=) ==> (=)) (comp x y z).
  Proof.
   intros ??? [? [??]] ? E ?? F ??. simpl.
   unfold compose. rewrite (F _ _), (E _ _). reflexivity.
  Qed.

  Global Instance: Category Object.
  Proof. constructor; try apply _; repeat intro; reflexivity. Qed.

End contents.
