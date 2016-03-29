Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.theory.products.

Lemma ext_equiv_refl `{Setoid_Morphism A B f} : f = f.
Proof. intros ?? E. pose proof (setoidmor_b f). now rewrite E. Qed.

Instance ext_equiv_trans `{Equiv A} `{Equiv B} `{Reflexive (A:=A) (=)} `{Transitive (A:=B) (=)} : Transitive (_ : Equiv (A → B)).
Proof. intros ? y ???? w ?. transitivity (y w); firstorder. Qed.

Instance ext_equiv_sym `{Equiv A} `{Equiv B} `{Symmetric (A:=A) (=)} `{Symmetric (A:=B) (=)}: Symmetric (A:=A→B) (=).
Proof. firstorder. Qed.

Lemma ext_equiv_applied `{Setoid A} `{Equiv B} {f g : A → B} :
  f = g → ∀ x, f x = g x.
Proof. intros E x. now apply E. Qed.

Lemma ext_equiv_applied_iff `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)}
  `{!Setoid_Morphism (g : A → B)} : f = g ↔ ∀ x, f x = g x.
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; intros E1.
   now apply ext_equiv_applied.
  intros x y E2. now rewrite E2.
Qed.

Lemma morphism_ne `{Equiv A} `{Equiv B} (f : A → B) `{!Setoid_Morphism f} x y :
  f x ≠ f y → x ≠ y.
Proof. intros E1 E2. apply E1. now apply sm_proper. Qed.

Instance: Equiv Prop := iff.
Instance: Setoid Prop := {}.

Lemma projected_setoid `{Setoid B} `{Equiv A} (f : A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y) : Setoid A.
Proof.
 constructor; repeat intro; apply eq_correct.
   reflexivity.
  symmetry; now apply eq_correct.
 transitivity (f y); now apply eq_correct.
Qed.

Instance sig_setoid `{Setoid A} (P : A → Prop) : Setoid (sig P).
Proof. now apply (projected_setoid (@proj1_sig _ P)). Qed.

Instance sigT_setoid `{Setoid A} (P : A → Type) : Setoid (sigT P).
Proof. now apply (projected_setoid (@projT1 _ P)). Qed.

Instance id_morphism `{Setoid A} : Setoid_Morphism (@id A) := {}.
Proof. repeat red; intros x y Heq. apply Heq. Qed.

Lemma compose_setoid_morphism `{Equiv A} `{Equiv B} `{Equiv C} (f : A → B) (g : B → C) :
  Setoid_Morphism f → Setoid_Morphism g → Setoid_Morphism (g ∘ f).
Proof. firstorder. Qed.
Hint Extern 4 (Setoid_Morphism (_ ∘ _)) => class_apply @compose_setoid_morphism : typeclass_instances.

Instance morphism_proper `{Equiv A} `{Equiv B}: Proper ((=) ==> iff) (@Setoid_Morphism A B _ _).
Proof.
  assert (∀ f g : A → B, f = g → Setoid_Morphism f → Setoid_Morphism g) as aux.
   intros f g E1 ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
   split; try apply _. intros x y E2.
   now rewrite <-!(ext_equiv_applied E1 _), E2.
  intros f g; split; intros ?; eapply aux; eauto.
  pose proof (setoidmor_a g). pose proof (setoidmor_b g). now symmetry.
Qed.

