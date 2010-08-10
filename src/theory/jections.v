Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program Basics
  abstract_algebra canonical_names workaround_tactics.
Require setoids.

Local Notation "f ⁻¹" := (inverse f) (at level 30).
  (* Seems to work well, but conflicts with identical notation for multiplicative inverses. Todo: Find solution. *)

Section compositions.

  Context `{Equiv A} `{Equiv B} `{Equiv C} (g: A → B) (f: B → C) {fi: Inverse f} {gi: Inverse g}.

  Global Instance: Inverse (f ∘ g) := gi ∘ fi.

  Global Instance: Injective f → Injective g → Injective (f ∘ g).
  Proof. firstorder. Qed.

  Global Instance: Surjective f → Surjective g → Surjective (f ∘ g).
  Proof with try apply _.
   constructor...
   change (f ∘ (g ∘ gi ∘ fi) = id).
   intro. unfold compose.
   pose proof (setoidmor_b f).
   posed_rewrite (surjective g (fi x)).
   apply surjective...
  Qed.

  Global Instance: Bijective f → Bijective g → Bijective (f ∘ g).
  Proof. intros []. constructor; apply _. Qed.

End compositions.

Lemma back `{Bijective A B f}: f ⁻¹ ∘ f = id. (* a.k.a. "split-mono" *)
Proof. repeat intro. apply (injective f). exact (surjective f (f x)). Qed.
  (* recall that "f ∘ f ⁻¹ = id" is just surjective. *)

Lemma alt_injective `{Equiv A} `{Equiv B} `{f: A → B} `{!Inverse f}:
  Setoid_Morphism f →
  Setoid_Morphism (f ⁻¹: B → A) →
  f ⁻¹ ∘ f = id → Injective f.
Proof with try tauto.
 intros ?? E.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 constructor...
 intros ?? E'.
 rewrite <- (E x), <- (E y).
 unfold compose.
 rewrite E'...
 intuition.
Qed.

Instance: ∀ `{Bijective A B f}, Setoid_Morphism (f⁻¹).
Proof with try tauto.
 intros.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 constructor...
 repeat intro.
 apply (injective f).
 change ((f ∘ f ⁻¹) x = (f ∘ f ⁻¹) y).
 do 2 rewrite (surjective f _)...
Qed.

Instance: ∀ `{Inverse A B f}, Inverse (f ⁻¹) := λ _ _ f _, f.

Lemma flip_bijection_pseudoinstance: ∀ `{Bijective A B f}, Bijective (f ⁻¹).
Proof with intuition.
 intros.
 pose proof (setoidmor_a f).
 pose proof (setoidmor_b f).
 repeat (constructor; try apply _).
  intros x y E.
  rewrite <- (surjective f x), <- (surjective f y).
  unfold compose. (* f_equal ?*)
  rewrite E...
 intro. apply (injective f), (surjective f).
Qed.

Hint Extern 4 (Bijective (inverse _)) => apply flip_bijection_pseudoinstance: typeclass_instances.
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
 posed_rewrite (surjective f y).
 assumption.
Qed.

Lemma cancel_left' `{Bijective A B f} x y: f ⁻¹ x = y → x = f y.
Proof. apply (@cancel_left _ _ _ _ (f ⁻¹) f _). Qed.

Instance Injective_proper `{Equiv A} `{Equiv B}: Proper ((=) ==> (=)) (@Injective A _ B _).
Proof with intuition.
 cut (∀ (x y: A → B), x = y → Injective x → Injective y).
  split; repeat intro.
   apply H1 with x...
  destruct (injective_mor y).
  apply H1 with y...
 repeat intro.
 destruct (injective_mor x).
 constructor.
  repeat intro.
  apply (injective x).
  rewrite (H1 x0), (H1 y0)...
 rewrite <- H1...
Qed.

Instance Surjective_proper `{Equiv A} `{Equiv B} (f g: A → B) {finv: Inverse f}:
  f = g → Surjective g (inv:=finv) → Surjective f.
Proof with try apply _; try assumption.
 intros E [P [Q U Z]].
 repeat constructor...
  intro. unfold compose. rewrite (E (inverse f x)). apply P.
 repeat intro. rewrite (E x), (E y). apply Z...
Qed. 
