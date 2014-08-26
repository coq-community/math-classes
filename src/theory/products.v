Require Import
  abstract_algebra.

Definition prod_equiv `{Equiv A} `{Equiv B} : Equiv (A * B) := λ p q, fst p = fst q ∧ snd p = snd q.
(* Avoid eager application *)
Hint Extern 0 (Equiv (_ * _)) => eapply @prod_equiv : typeclass_instances.

Section product.
  Context `{Setoid A} `{Setoid B}.

  Global Instance: Setoid (A * B) := {}.
  Proof. firstorder auto. Qed.

  Global Instance pair_proper: Proper ((=) ==> (=) ==> (=)) (@pair A B).
  Proof. firstorder. Qed.

  Global Instance: Setoid_Morphism (@fst A B).
  Proof. constructor; try apply _. firstorder. Qed.

  Global Instance: Setoid_Morphism (@snd A B).
  Proof. constructor; try apply _. firstorder. Qed.

  Context `(A_dec : ∀ x y : A, Decision (x = y)) `(B_dec : ∀ x y : B, Decision (x = y)).
  Global Program Instance prod_dec: ∀ x y : A * B, Decision (x = y) := λ x y,
    match A_dec (fst x) (fst y) with
    | left _ => match B_dec (snd x) (snd y) with left _ => left _ | right _ => right _ end
    | right _ => right _
    end.
  Solve Obligations with (program_simpl; firstorder).
End product.

Definition prod_fst_equiv X A `{Equiv X} : relation (X * A) := λ x y, fst x = fst y.

Section product_fst.
  Context `{Setoid X}.

  Global Instance: Equivalence (prod_fst_equiv X A).
  Proof. unfold prod_fst_equiv. firstorder auto. Qed.
End product_fst.

Section dep_product.
  Context (I : Type) (c : I → Type) `{∀ i, Equiv (c i)} `{∀ i, Setoid (c i)}.

  Let dep_prod: Type := ∀ i, c i.

  Instance dep_prod_equiv: Equiv dep_prod := λ x y, ∀ i, x i = y i.

  Global Instance: Setoid dep_prod.
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ?? E ?. symmetry. apply E.
   intros ? y ??? i. transitivity (y i); firstorder.
  Qed.

  Global Instance dep_prod_morphism i : Setoid_Morphism (λ c: dep_prod, c i).
  Proof. firstorder auto. Qed.
End dep_product.
