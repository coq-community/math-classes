(* Show that algebras with homomorphisms between them form a category. *)
Require Import
  abstract_algebra universal_algebra ua_homomorphisms theory.categories.
Require
  categories.setoids categories.product.

Record Object (sign: Signature) : Type := object
  { algebra_carriers:> sorts sign → Type
  ; algebra_equiv: ∀ a, Equiv (algebra_carriers a)
  ; algebra_ops: AlgebraOps sign algebra_carriers
  ; algebra_proof: Algebra sign algebra_carriers }.

Implicit Arguments object [[algebra_equiv] [algebra_ops] [algebra_proof]].

(* Avoid Coq trying to apply algebra_equiv to find arbitrary Equiv instances *)
Hint Extern 0 (Equiv (algebra_carriers _ _ _)) => eapply @algebra_equiv : typeclass_instances.
Existing Instance algebra_ops.
Existing Instance algebra_proof.

Section contents.
  Variable sign: Signature.

  Global Instance: Arrows (Object sign) := λ X Y, sig (HomoMorphism sign X Y).

  Program Definition arrow `{Algebra sign A} `{Algebra sign B}
    f `{!HomoMorphism sign A B f}: object sign A ⟶ object sign B := f.

  Global Program Instance: CatId (Object sign) := λ _ _, id.

  Global Program Instance comp: CatComp (Object sign) := λ _ _ _ f g v, f v ∘ g v.
  Next Obligation. destruct f, g. apply _. Qed.

  Global Program Instance: ∀ x y: Object sign, Equiv (x ⟶ y)
    := λ _ _ x y, ∀ b, pointwise_relation _ (=) (x b) (y b).

  Global Instance: ∀ x y: Object sign, Setoid (x ⟶ y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) (comp x y z).
  Proof.
   intros ? ? ? x0 ? E ? ? F ? ?.
   simpl. unfold compose. do 3 red in E, F.
   destruct (proj2_sig x0). rewrite F, E. reflexivity.
  Qed.

  Global Instance: Category (Object sign).
  Proof. constructor; try apply _; repeat intro; reflexivity. Qed.
End contents.
