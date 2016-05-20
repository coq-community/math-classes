Require Import
  MathClasses.theory.setoids MathClasses.interfaces.abstract_algebra.

Local Existing Instance injective_mor.
Local Existing Instance surjective_mor.

Lemma injective_compose_cancel `{Equiv A} `{Equiv B} `{Equiv C} (f : B → C)
    `{!Injective f} `{!Setoid_Morphism (g : A → B)} `{!Setoid_Morphism (h : A → B)} :
  f ∘ g = f ∘ h → g = h.
Proof.
  pose proof (setoidmor_a g).
  intros E. apply setoids.ext_equiv_applied_iff. intros x.
  apply (injective f). now apply E.
Qed.

Lemma surjective_applied `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} `{!Surjective f} x : f (f⁻¹ x) = x.
Proof. firstorder. Qed.

Instance inverse_mor `{Bijective A B f} : Setoid_Morphism (f⁻¹).
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; try apply _.
  intros x y E. apply (injective f). now rewrite !(surjective_applied f).
Qed.

Lemma bijective_cancel_left `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} `{!Bijective f} x y :
  f x = y → x = f⁻¹ y.
Proof.
  pose proof (setoidmor_b f).
  intros E. apply (injective f). now rewrite (surjective_applied f).
Qed.

Lemma bijective_cancel_inverse_left `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} `{!Bijective f} x y :
  f⁻¹ x = y → x = f y.
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  intros E. now rewrite <-E, (surjective_applied f).
Qed.

Lemma bijective_applied `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} `{!Bijective f} x: f⁻¹ (f x) = x.
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  symmetry. now apply (bijective_cancel_left f).
Qed.

Lemma bijective `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} `{!Bijective f} : f⁻¹ ∘ f = id. (* a.k.a. "split-mono" *)
Proof.
  pose proof (setoidmor_a f).
  apply ext_equiv_applied_iff, (bijective_applied f).
Qed.

Lemma injective_ne `{Equiv A} `{Equiv B} `(f : A → B) `{!Injective f} x y :
  x ≠ y → f x ≠ f y.
Proof. intros E1 E2. apply E1. now apply (injective f). Qed.

Instance id_inverse {A} : Inverse (@id A) := (@id A).

Global Existing Instance id_morphism.

Instance id_injective `{Setoid A} : Injective (@id A).
Proof. split; try apply _. easy. Qed.
Instance id_surjective `{Setoid A} : Surjective (@id A).
Proof. split; try apply _. now repeat intro. Qed.
Instance id_bijective `{Setoid A} : Bijective (@id A).
Proof. split; try apply _. Qed.

Section compositions.
  Context `{Equiv A} `{Equiv B} `{Equiv C} (g: A → B) (f: B → C) `{!Inverse f} `{!Inverse g}.

  Instance compose_inverse: Inverse (f ∘ g) := g⁻¹ ∘ f⁻¹.

  Instance compose_injective: Injective f → Injective g → Injective (f ∘ g).
  Proof. firstorder. Qed.
  Instance compose_surjective: Surjective f → Surjective g → Surjective (f ∘ g).
  Proof.
    split; try apply _.
    pose proof (setoidmor_b f).
    intros x y E. rewrite <-E.
    change (f (g (g⁻¹ (f⁻¹ x))) = x).
    now rewrite !surjective_applied.
  Qed.
  Instance compose_bijective: Bijective f → Bijective g → Bijective (f ∘ g) := {}.
End compositions.

Hint Extern 4 (Inverse (_ ∘ _)) => class_apply @compose_inverse : typeclass_instances.
Hint Extern 4 (Injective (_ ∘ _)) => class_apply @compose_injective : typeclass_instances.
Hint Extern 4 (Surjective (_ ∘ _)) => class_apply @compose_surjective : typeclass_instances.
Hint Extern 4 (Bijective (_ ∘ _)) => class_apply @compose_bijective : typeclass_instances.

Lemma alt_Build_Injective `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} :
  Setoid_Morphism f → Setoid_Morphism (f⁻¹) → f⁻¹ ∘ f = id → Injective f.
Proof.
  intros ?? E.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; try apply _.
  intros x y F.
  rewrite <-(ext_equiv_applied E x), <-(ext_equiv_applied E y).
  unfold compose. now rewrite F.
Qed.

Lemma alt_Build_Bijective `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} :
  Setoid_Morphism f → Setoid_Morphism (f⁻¹) → f⁻¹ ∘ f = id → f ∘ f⁻¹ = id → Bijective f.
Proof.
  intros. split.
   now apply (alt_Build_Injective f).
  split; auto.
Qed.

Definition inverse_inverse `{Inverse A B f} : Inverse (f⁻¹) := f.
Hint Extern 4 (Inverse (_ ⁻¹)) => class_apply @inverse_inverse : typeclass_instances.

Lemma flip_bijection `{Bijective A B f} : Bijective (f⁻¹).
Proof. apply alt_Build_Bijective; try apply _. apply (surjective f). apply (bijective f). Qed.

(* We use this instead of making flip_bijection a real instance, because
   otherwise it gets applied too eagerly, resulting in cycles. *)
Hint Extern 4 (Bijective (_ ⁻¹)) => apply flip_bijection : typeclass_instances.

Lemma inverse_involutive `(f : A → B) `{!Inverse f} : (f⁻¹)⁻¹ ≡ f.
Proof. reflexivity. Qed.

(* This second version is strictly for manual application. *)
Lemma flip_bijection_back `{Equiv A} `{Equiv B} (f: A → B) `{!Inverse f} : Bijective (f⁻¹) → Bijective f.
Proof. intro. apply (_: Bijective (f⁻¹⁻¹)). Qed.

Instance injective_proper `{Equiv A} `{Equiv B} : Proper ((=) ==> (=)) (@Injective A B _ _).
Proof.
  assert (∀ f g : A → B, f = g → Injective f → Injective g) as aux.
   intros f g E ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f). split.
    intros x y ?. apply (injective f).
    now rewrite (ext_equiv_applied E x), (ext_equiv_applied E y).
   rewrite <-E; apply _.
  intros f g; split; intros; eapply aux; eauto.
  pose proof (setoidmor_a g). pose proof (setoidmor_b g). now symmetry.
Qed.

Lemma surjective_proper `{Equiv A} `{Equiv B} (f g : A → B) `{!Inverse f} `{!Inverse g} `{!Surjective g} :
  f = g → f⁻¹ = g⁻¹  → Surjective f.
Proof.
  intros E1 E2.
  pose proof (setoidmor_a g). pose proof (setoidmor_b g).
  split.
   intros ? ? E3. change (f  (f⁻¹ x) = y).
   rewrite <-E3, (ext_equiv_applied E1 _), (ext_equiv_applied E2 _).
   now apply surjective_applied.
  rewrite E1; apply _.
Qed.

Ltac setoid_inject :=
  match goal with
  | E : _ = ?f _ |- _ => apply (injective f) in E
  | E : ?f _ = _ |- _ => apply (injective f) in E
  | E : _ ≡ _ |-  ?G => change (id G); injection E; clear E; intros; unfold id at 1 
  end.
