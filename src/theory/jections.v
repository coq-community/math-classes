Require Import
  Relation_Definitions Morphisms Setoid Program Basics
  abstract_algebra canonical_names workaround_tactics.
Require setoids.

Instance id_injective `{Setoid A} : Injective (@id A).
Proof. split; try apply _. easy. Qed.

Section compositions.
  Context `{Equiv A} `{Equiv B} `{Equiv C} (g: A → B) (f: B → C) `{!Inverse f} `{!Inverse g}.

  Global Instance: Inverse (f ∘ g) := g⁻¹ ∘ f⁻¹.

  Global Instance: Injective f → Injective g → Injective (f ∘ g).
  Proof. firstorder. Qed.

  Global Instance: Surjective f → Surjective g → Surjective (f ∘ g).
  Proof with try apply _; intuition.
   constructor...
   pose proof (setoidmor_b f).
   pose proof (setoidmor_a f).
   intros x y E. unfold compose.
   posed_rewrite (surjective g (f⁻¹ x) (f⁻¹ x))...
   posed_rewrite (surjective f x x)...
  Qed.

  Global Instance: Bijective f → Bijective g → Bijective (f ∘ g) := {}.

End compositions.

Lemma back `{Bijective A B f}: f ⁻¹ ∘ f = id. (* a.k.a. "split-mono" *)
Proof.
 intros x y E.
 unfold compose.
 destruct H.
 unfold id, inverse.
 apply bijective_injective.
 destruct (bijective_surjective).
 apply surjective.
 destruct surjective_mor.
 now apply sm_proper.
Qed.
  (* recall that "f ∘ f ⁻¹ = id" is just surjective. *)

Lemma surjective_applied `{Surjective A B f} x : f (f⁻¹ x) = x.
Proof. firstorder. Qed.

(* Without explicit argument f. This one is more convenient for rewriting *)
Lemma surjective_applied' `{Equiv A} `{Equiv B} (f : A → B) `{!Inverse f} `{!Surjective f} x : f (f⁻¹ x) = x.
Proof. firstorder. Qed.

Lemma bijective_applied `{Bijective A B f} x: f⁻¹ (f x) = x.
Proof. firstorder. Qed.

Lemma alt_injective `{Equiv A} `{Equiv B} `{f: A → B} `{!Inverse f}:
  Setoid_Morphism f →
  Setoid_Morphism (f ⁻¹: B → A) →
  f ⁻¹ ∘ f = id → Injective f.
Proof with try tauto; intuition.
 intros ?? E.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 constructor.
  intros ?? F.
  rewrite <- (E x x), <- (E y y)...
  unfold compose.
  rewrite F...
 tauto.
Qed.

Instance: ∀ `{Bijective A B f}, Setoid_Morphism (f⁻¹).
Proof with try tauto; intuition.
 intros.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 constructor...
 repeat intro.
 apply (injective f).
 change ((f ∘ f ⁻¹) x = (f ∘ f ⁻¹) y).
 rewrite (surjective f x x)...
 rewrite (surjective f y y)...
Qed.

Instance: ∀ `{Inverse A B f}, Inverse (f ⁻¹) := λ _ _ f _, f.

Lemma flip_bijection_pseudoinstance: ∀ `{Bijective A B f}, Bijective (f ⁻¹).
Proof with intuition.
 intros.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 repeat (constructor; try apply _).
  intros x y E.
  rewrite <- (surjective f x x), <- (surjective f y y)...
  unfold compose. (* f_equal ?*)
  rewrite E...
 intros x y E. rewrite <- E.
 apply bijective_applied.
Qed.

Hint Extern 4 (Bijective (_ ⁻¹)) => apply flip_bijection_pseudoinstance: typeclass_instances.
  (* We use this instead of making flip_bijection_pseudoinstance a real instance, because
   otherwise it gets applied too eagerly, resulting in cycles. *)

Lemma flip_bijection `{Equiv A} `{Equiv B} (f: A → B) `{!Inverse f}: Bijective (f ⁻¹) → Bijective f.
Proof. intro. apply (_: Bijective (f ⁻¹ ⁻¹)). Qed.
  (* This second version is strictly for manual application. *)

(* back' = surjective *)

Lemma cancel_left `{Bijective A B f} x y: f x = y → x = f ⁻¹ y.
Proof.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 intros. apply (injective f).
 now posed_rewrite (surjective f y y).
Qed.

Lemma cancel_left' `{Bijective A B f} x y: f ⁻¹ x = y → x = f y.
Proof. apply (@cancel_left _ _ _ _ (f ⁻¹) f _). Qed.

Instance Injective_proper `{Equiv A} `{Equiv B}: Proper ((=) ==> (=)) (@Injective A _ B _).
Proof with intuition.
 cut (∀ (x y: A → B), x = y → Injective x → Injective y).
  intros P f g ?. split; intros ?.
   apply P with f...
  destruct (injective_mor g).
  apply P with g...
 intros f g P ?.
 destruct (injective_mor f).
 constructor.
  intros x y ?.
  apply (injective f).
  rewrite (P x x), (P y y)...
 rewrite <-P...
Qed.

Instance Surjective_proper `{Equiv A} `{Equiv B} (f g: A → B) {finv: Inverse f}:
  f = g → Surjective g (inv:=finv) → Surjective f.
Proof with try apply _; intuition.
 intros E [P [Q U Z]].
 repeat constructor...
  intros x y F. unfold compose.
  rewrite <- F.
  rewrite (E (f⁻¹ x) (f⁻¹ x))... apply P...
 repeat intro. rewrite (E x x), (E y y)...
Qed. 
