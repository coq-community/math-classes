Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.theory.jections.

Section contents.
Context `{StrongSetoid A}.

Global Instance: Setoid A.
Proof.
  split.
    intros x. rewrite <-tight_apart. now apply (irreflexivity (≶)).
   intros x y. rewrite <-?tight_apart. now apply not_symmetry.
  intros x y z. rewrite <-?tight_apart. intros E1 E2 E3.
  destruct (cotransitive E3 y); contradiction.
Qed.

Global Instance apart_proper: Proper ((=) ==> (=) ==> iff) (≶).
Proof.
  assert (∀ x₁ y x₂, x₁ ≶ y → x₁ = x₂ → x₂ ≶ y) as P1.
   intros ? ? ? E Ex.
   destruct (cotransitive E x₂); trivial.
   apply tight_apart in Ex. destruct Ex.
   now symmetry.
  assert (∀ x₁ y₁ x₂ y₂, x₁ ≶ y₁ → x₁ = x₂ → y₁ = y₂ → x₂ ≶ y₂) as P2.
   intros ? ? ? ? E Ex Ey.
   apply P1 with x₁; trivial.
   symmetry. apply P1 with y₁; trivial. now symmetry.
  intros ? ? E1 ? ? E2.
  split; intro; eapply P2; eauto; now symmetry.
Qed.

Instance apart_ne x y : PropHolds (x ≶ y) → PropHolds (x ≠ y).
Proof. firstorder. Qed.

Global Instance: ∀ x y, Stable (x = y).
Proof.
  intros x y. unfold Stable, DN.
  rewrite <-tight_apart. tauto.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 3 (PropHolds (_ ≠ _)) => eapply @apart_ne : typeclass_instances.

Lemma projected_strong_setoid `{StrongSetoid B} `{Equiv A} `{Apart A} (f: A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y) (apart_correct : ∀ x y, x ≶ y ↔ f x ≶ f y) : StrongSetoid A.
Proof.
  split.
     intros x. red. rewrite apart_correct. apply (irreflexivity (≶)).
    intros x y. rewrite !apart_correct. now symmetry.
   intros x y E z. rewrite !apart_correct. apply cotransitive. now apply apart_correct.
  intros x y. rewrite apart_correct, eq_correct. now apply tight_apart.
Qed.

Instance sig_strong_setoid `{StrongSetoid A} (P: A → Prop): StrongSetoid (sig P).
Proof. now apply (projected_strong_setoid (@proj1_sig _ P)). Qed.

Section morphisms.
  Context `{Equiv A} `{Apart A} `{Equiv B} `{Apart B} `{Equiv C} `{Apart C}.

  Existing Instance strong_setoidmor_a.
  Existing Instance strong_setoidmor_b.

  Global Instance strong_morphism_proper `{!StrongSetoid_Morphism (f : A → B)} :
    Setoid_Morphism f | 10.
  Proof.
    split; try apply _.
    intros ? ?. rewrite <-!tight_apart. intros E1 E2.
    destruct E1. now apply (strong_extensionality f).
  Qed.

  Global Instance strong_injective_injective `{!StrongInjective (f : A → B)} :
    Injective f.
  Proof.
    pose proof (strong_injective_mor f).
    split; try apply _.
    intros ? ?. rewrite <-!tight_apart. intros E1 E2.
    destruct E1. now apply (strong_injective f).
  Qed.

  (* If a morphism satisfies the binary strong extensionality property, it is
    strongly extensional in both coordinates. *)
  Global Instance strong_setoid_morphism_1 `{!StrongSetoid_BinaryMorphism (f : A → B → C)} :
    ∀ z, StrongSetoid_Morphism (f z).
  Proof.
    pose proof (strong_binary_setoidmor_a f).
    pose proof (strong_binary_setoidmor_b f).
    pose proof (strong_binary_setoidmor_c f).
    intros z.
    split; try apply _.
    intros x y E.
    destruct (strong_binary_extensionality f z x z y); trivial.
    now destruct (irreflexivity (≶) z).
  Qed.

  Global Instance strong_setoid_morphism_unary_2 `{!StrongSetoid_BinaryMorphism (f : A → B → C)} :
    ∀ z, StrongSetoid_Morphism (λ x, f x z).
  Proof.
    pose proof (strong_binary_setoidmor_a f).
    pose proof (strong_binary_setoidmor_b f).
    pose proof (strong_binary_setoidmor_c f).
    intros z.
    split; try apply _.
    intros x y E.
    destruct (strong_binary_extensionality f x z y z); trivial.
    now destruct (irreflexivity (≶) z).
  Qed.

  (* Conversely, if a morphism is strongly extensional in both coordinates, it
    satisfies the binary strong extensionality property. We don't make this an
    instance in order to avoid loops. *)
  Lemma strong_binary_setoid_morphism_both_coordinates
    `{!StrongSetoid A} `{!StrongSetoid B} `{!StrongSetoid C} {f : A → B → C}
    `{∀ z, StrongSetoid_Morphism (f z)} `{∀ z, StrongSetoid_Morphism (λ x, f x z)} : StrongSetoid_BinaryMorphism f.
  Proof.
    split; try apply _.
    intros x₁ y₁ x₂ y₂ E.
    destruct (cotransitive E (f x₂ y₁)).
     left. now apply (strong_extensionality (λ x, f x y₁)).
    right. now apply (strong_extensionality (f x₂)).
  Qed.

  Global Instance binary_strong_morphism_proper `{!StrongSetoid_BinaryMorphism (f : A → B → C)} :
    Proper ((=) ==> (=) ==> (=)) f.
  Proof.
    pose proof (strong_binary_setoidmor_a f).
    pose proof (strong_binary_setoidmor_b f).
    pose proof (strong_binary_setoidmor_c f).
    intros x₁ y₁ E1 x₂ y₂ E2.
    rewrite <-tight_apart in E1. rewrite <-tight_apart in E2.
    apply tight_apart. intros E3.
    edestruct (cotransitive E3 (f y₁ x₂)).
     destruct E1. now apply (strong_extensionality (λ x, f x x₂)).
    destruct E2. now apply (strong_extensionality (f y₁)).
  Qed.
End morphisms.

Section more_morphisms.
  Context `{StrongSetoid A} `{StrongSetoid B}.

  Lemma strong_binary_setoid_morphism_commutative {f : A → A → B} `{!Commutative f}
    `{∀ z, StrongSetoid_Morphism (f z)} : StrongSetoid_BinaryMorphism f.
  Proof.
    assert (∀ z, StrongSetoid_Morphism (λ x, f x z)).
     split; try apply _. intros x y. rewrite !(commutativity _ z). now apply (strong_extensionality (f z)).
    apply strong_binary_setoid_morphism_both_coordinates.
  Qed.
End more_morphisms.

Instance default_apart `{Equiv A} : Apart A | 20 := (≠).
Typeclasses Opaque default_apart.

Instance default_apart_trivial `{Equiv A} : TrivialApart A (Aap:=default_apart).
Proof. red. reflexivity. Qed.

(* In case we have a decidable setoid, we can construct a strong setoid. Again
  we do not make this an instance as it will cause loops *)
Section dec_setoid.
  Context `{Setoid A} `{Apart A} `{!TrivialApart A} `{∀ x y, Decision (x = y)}.

  (* Not Global in order to avoid loops *)
  Instance ne_apart x y : PropHolds (x ≠ y) → PropHolds (x ≶ y).
  Proof. rewrite trivial_apart. easy. Qed.

  Instance dec_strong_setoid: StrongSetoid A.
  Proof.
    split; try apply _.
       firstorder.
      intros x y. rewrite !trivial_apart. firstorder.
     intros x y E1 z. rewrite !trivial_apart.
     destruct (decide (x = z)) as [E2|E2]; [|tauto].
     right. intros E3. rewrite trivial_apart in E1. apply E1. now rewrite E2.
    intros x y. rewrite trivial_apart. split.
     intros E. now apply stable.
    firstorder.
  Qed.
End dec_setoid.

(* And a similar result for morphisms *)
Section dec_setoid_morphisms.
  Context `{StrongSetoid A} `{!TrivialApart A} `{StrongSetoid B}.

  Instance dec_strong_morphism (f : A → B) `{!Setoid_Morphism f} :
    StrongSetoid_Morphism f.
  Proof.
    split; try apply _.
    intros x y E. apply trivial_apart, (setoids.morphism_ne f). now apply apart_ne.
  Qed.

  Context `{!TrivialApart B}.

  Instance dec_strong_injective (f : A → B) `{!Injective f} :
    StrongInjective f.
  Proof.
    pose proof (injective_mor f).
    split; try apply _.
    intros x y. rewrite !trivial_apart. now apply (injective_ne f).
  Qed.

  Context `{StrongSetoid C}.

  Instance dec_strong_binary_morphism (f : A → B → C) `{!Proper ((=) ==> (=) ==> (=)) f} :
    StrongSetoid_BinaryMorphism f.
  Proof.
    split; try apply _.
    intros x₁ y₁ x₂ y₂ E1.
    case (cotransitive E1 (f x₂ y₁)); rewrite !trivial_apart; intros E2.
     left. intros E3. destruct (apart_ne _ _ E2). now rewrite E3.
    right. intros E3. destruct (apart_ne _ _ E2). now rewrite E3.
  Qed.
End dec_setoid_morphisms.
