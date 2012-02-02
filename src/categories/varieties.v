(* Show that Varieties with homomorphisms between them form a category.

Hm, this file is almost identical to categories/algebra because the morphism are the same. There must be some way to
factor out the commonality.

 *)
Require Import
  abstract_algebra universal_algebra ua_homomorphisms.

Record Object (et: EquationalTheory) : Type := object
  { variety_carriers:> sorts et → Type
  ; variety_equiv: ∀ a, Equiv (variety_carriers a)
  ; variety_ops: AlgebraOps et variety_carriers
  ; variety_proof: InVariety et variety_carriers }.
Arguments object _ _ {variety_equiv variety_ops variety_proof}.

(* Avoid Coq trying to apply variety_equiv to find arbitrary Equiv instances *)
Hint Extern 0 (Equiv (variety_carriers _ _ _)) => eapply @variety_equiv : typeclass_instances.
Existing Instance variety_ops.
Existing Instance variety_proof.

Section contents.
  Variable et: EquationalTheory.

  Global Instance: Arrows (Object et) := λ X Y, sig (HomoMorphism et X Y).

  Program Definition arrow `{InVariety et A} `{InVariety et B}
    f `{!HomoMorphism et A B f}: object et A ⟶ object et B := f.

  Global Program Instance: CatId (Object et) := λ _ _, id.

  Global Program Instance: CatComp (Object et) := λ _ _ _ f g v, f v ∘ g v.

  Global Program Instance: ∀ (x y: Object et), Equiv (x ⟶ y)
    := λ _ _ x y, ∀ b, pointwise_relation _ (=) (x b) (y b).

  Global Instance: ∀ (x y: Object et), Setoid (x ⟶ y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: ∀ (x y z: Object et), Proper ((=) ==> (=) ==> (=)) (comp x y z).
  Proof.
   intros ??? [? [??]] ? E ?? F ??. simpl.
   unfold compose. rewrite (F _ _), (E _ _). reflexivity.
  Qed.

  Global Instance: Category (Object et).
  Proof. constructor; try apply _; repeat intro; reflexivity. Qed.
End contents.
