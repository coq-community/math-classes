(* To be imported qualified. *)
Require Import
  abstract_algebra.

Instance ext_equiv_trans `{Setoid A} `{Setoid B}: Transitive (_ : Equiv (A → B)).
Proof. intros ? y ???? w ?. transitivity (y w); firstorder. Qed.

Instance ext_equiv_sym `{Setoid A} `{Setoid B}: Symmetric (_ : Equiv (A → B)).
Proof. firstorder. Qed.

Instance: Equiv Prop := iff.
Instance: Setoid Prop := {}.

Lemma projected_setoid `{Setoid B} `{Equiv A} (f: A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y) : Setoid A.
Proof.
 constructor; repeat intro; apply eq_correct.
   reflexivity.
  symmetry; now apply eq_correct.
 transitivity (f y); now apply eq_correct.
Qed.

Instance sig_Setoid `{Setoid A} (P: A → Prop): Setoid (sig P).
Proof. now apply (projected_setoid (@proj1_sig _ P)). Qed.

Instance sigT_Setoid `{Setoid A} (P: A → Type): Setoid (sigT P).
Proof. now apply (projected_setoid (@projT1 _ P)). Qed.

Definition prod_equiv `{Equiv A} `{Equiv B} : Equiv (A * B) := λ p q, fst p = fst q ∧ snd p = snd q.
(* Avoid eager application *)
Hint Extern 0 (Equiv (_ * _)) => eapply @prod_equiv : typeclass_instances.

Section simple_product.
  Context `{Setoid A} `{Setoid B}.

  Global Instance: Setoid (A * B) := {}.
  Proof. firstorder auto. Qed.

  Global Instance pair_proper : Proper ((=) ==> (=) ==> (=)) (@pair A B).
  Proof. firstorder. Qed.

  Global Instance: Setoid_Morphism (@fst A B).
  Proof. constructor; try apply _. firstorder. Qed.

  Global Instance: Setoid_Morphism (@snd A B).
  Proof. constructor; try apply _. firstorder. Qed.
End simple_product.

Section product.
  Context (I: Type) (c: I → Type) `{∀ i, Equiv (c i)} `{∀ i, Setoid (c i)}.

  Let product: Type := ∀ i, c i.

  Instance product_equiv: Equiv product := `(∀ i, x i = y i).

  Global Instance: Setoid product.
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ?? E ?. symmetry. apply E.
   intros ? y ??? i. transitivity (y i); firstorder.
  Qed.

  Global Instance projection_morphism i: Setoid_Morphism (λ c: product, c i).
  Proof. firstorder. Qed.
End product.

Instance id_morphism `{Setoid T}: Setoid_Morphism (@id T) := {}.

Instance compose_morphisms (A B C: Type)
  `{!Equiv A} `{!Equiv B} `{!Equiv C} (f: A → B) (g: B → C)
  {P: Setoid_Morphism f} {Q: Setoid_Morphism g}: Setoid_Morphism (g ∘ f).
Proof. destruct P, Q. constructor; apply _. Qed.

Instance: ∀ `{Setoid_Morphism A B f} `{!Inverse f}, Bijective f → Setoid_Morphism (f⁻¹).
Proof.
 intros.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 constructor; try apply _.
 repeat intro. apply (injective f).
 pose proof (surjective f) as E.
 unfold compose in E.
 rewrite (E x x), (E y y); intuition.
Qed.

Instance morphism_proper `{ea: Equiv A} `{eb: Equiv B}: Proper ((=) ==> (=)) (@Setoid_Morphism A B _ _).
Proof.
 cut (∀ (x y: A → B), x = y → Setoid_Morphism x → Setoid_Morphism y).
  firstorder.
 intros x y E [AS BS P].
 constructor; try apply _. intros v w E'.
 rewrite <- (E v), <- (E w), E'; reflexivity.
Qed.
