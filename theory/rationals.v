Require Import
  Coq.setoid_ring.Ring
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.integers MathClasses.interfaces.naturals MathClasses.interfaces.rationals
  MathClasses.implementations.field_of_fractions MathClasses.implementations.natpair_integers
  MathClasses.theory.rings MathClasses.theory.integers MathClasses.theory.dec_fields.

Program Instance slow_rat_dec `{Rationals Q} : ∀ x y: Q, Decision (x = y) | 10 := λ x y,
  match decide (rationals_to_frac Q (SRpair nat) x = rationals_to_frac Q (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (injective (rationals_to_frac Q (SRpair nat))). Qed.

Section another_integers.
  Context `{Rationals Q} `{Integers Z}.
  Add Ring Z : (stdlib_ring_theory Z).

  Notation ZtoQ := (integers_to_ring Z Q).
  Notation QtoFrac := (rationals_to_frac Q Z).

  Lemma rationals_decompose `{!SemiRing_Morphism (f : Z → Q)} (x : Q) :
    ∃ num, ∃ den, den ≠ 0 ∧ x = f num / f den.
  Proof.
    exists (num (QtoFrac x)) (den (QtoFrac x)). split.
     now apply den_ne_0.
    apply (injective QtoFrac).
    rewrite preserves_mult.
    rewrite preserves_dec_recip.
    change (QtoFrac x = (QtoFrac ∘ f) (num (QtoFrac x)) / (QtoFrac ∘ f) (den (QtoFrac x))).
    rewrite 2!(to_ring_unique_alt (QtoFrac ∘ f) Frac_inject).
    assert (Frac_inject (den (QtoFrac x)) ≠ 0) as P.
     apply injective_ne_0. apply den_ne_0.
    apply Frac_dec_mult_num_den.
  Qed.

  Global Instance integers_to_rationals_injective `{!SemiRing_Morphism (f: Z → Q)} : Injective f.
  Proof.
    split; try apply _.
    intros x y E.
    apply (injective (integers_to_ring Z Q)).
    now rewrite <-2!(to_ring_unique f).
  Qed.

  Context `{f : Q → Frac Z} `{!SemiRing_Morphism f}.

  Global Instance to_frac_inverse: Inverse f := λ x, ZtoQ (num x) / ZtoQ (den x).

  Global Instance: Surjective f.
  Proof.
    split; try apply _.
    intros x y E.
    unfold compose, inverse, to_frac_inverse, id.
    rewrite <-E. clear E.
    rewrite commutativity.
    apply (left_cancellation_ne_0 (.*.) (f (ZtoQ (den x)))).
     do 2 apply injective_ne_0. apply den_ne_0.
    rewrite <-preserves_mult, associativity.
    rewrite dec_recip_inverse, left_identity.
     change ((f ∘ ZtoQ) (num x) = (f ∘ ZtoQ) (den x) * x).
     rewrite 2!(to_ring_unique_alt (f ∘ ZtoQ) Frac_inject).
     unfold equiv, Frac_equiv. simpl. ring.
    apply injective_ne_0.
    now apply den_ne_0.
  Qed.

  (* Making this instance global results in loops *)
  Instance to_frac_bijective: Bijective f := {}.
  Global Instance to_frac_inverse_bijective: Bijective (f⁻¹) := _.
  Global Instance: SemiRing_Morphism (f⁻¹) := {}.
End another_integers.

Lemma to_frac_unique `{Rationals Q} `{Integers Z} (f g : Q → Frac Z) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} :
  ∀ x, f x = g x.
Proof.
  intros x.
  apply (injective (g⁻¹)).
  change (f⁻¹ (f ⁻¹ ⁻¹ x) = g⁻¹ (g⁻¹ ⁻¹ x)).
  now rewrite 2!(jections.surjective_applied _).
Qed.

Definition rationals_to_rationals Q1 Q2 `{Rationals Q1} `{Rationals Q2} : Q1 → Q2
  := (rationals_to_frac Q2 (SRpair nat))⁻¹ ∘ rationals_to_frac Q1 (SRpair nat).
Hint Unfold rationals_to_rationals : typeclass_instances.

Section another_rationals.
  Context `{Rationals Q1} `{Rationals Q2}.

  Local Existing Instance to_frac_bijective.
  Global Instance: SemiRing_Morphism (rationals_to_rationals Q1 Q2) := _.
  Global Instance: Bijective (rationals_to_rationals Q1 Q2) := _.
  Global Instance: Bijective (rationals_to_rationals Q2 Q1) := _.

  Instance: Bijective (rationals_to_frac Q1 (SRpair nat)) := {}.

  Lemma to_rationals_involutive:
    ∀ x, rationals_to_rationals Q2 Q1 (rationals_to_rationals Q1 Q2 x) = x.
  Proof.
    intros x.
    unfold rationals_to_rationals, compose.
    rewrite (jections.surjective_applied _).
    apply (jections.bijective_applied _).
  Qed.

  Lemma to_rationals_unique (f : Q1 → Q2) `{!SemiRing_Morphism f} :
    ∀ x, f x = rationals_to_rationals Q1 Q2 x.
  Proof.
    intros x.
    apply (injective (rationals_to_rationals Q2 Q1)).
    rewrite to_rationals_involutive.
    change ((rationals_to_frac Q1 (SRpair nat)⁻¹) ((rationals_to_frac Q2 (SRpair nat) ∘ f) x) = x).
    rewrite (to_frac_unique (rationals_to_frac Q2 (SRpair nat) ∘ f) (rationals_to_frac Q1 (SRpair nat))).
    apply (jections.bijective_applied _).
  Qed.
End another_rationals.

Lemma to_rationals_unique_alt `{Rationals Q1} `{Rationals Q2} (f g : Q1 → Q2) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} :
  ∀ x, f x = g x.
Proof.
  intros x.
  now rewrite (to_rationals_unique f), (to_rationals_unique g).
Qed.

Lemma morphisms_involutive `{Rationals Q1} `{Rationals Q2} (f : Q1 → Q2) (g : Q2 → Q1) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} :
  ∀ x, f (g x) = x.
Proof.
  intros x.
  rewrite (to_rationals_unique f), (to_rationals_unique g).
  apply to_rationals_involutive.
Qed.

Global Instance injective_nats `{Rationals Q} `{Naturals N} `{!SemiRing_Morphism (f : N → Q)} : Injective f.
Proof.
  split; try apply _.
  intros x y E.
  apply (injective (naturals_to_semiring N (SRpair nat))).
  apply rationals_embed_ints.
  now rewrite 2!(naturals.to_semiring_unique_alt f (integers_to_ring (SRpair nat) Q ∘ naturals_to_semiring N (SRpair nat))) in E.
Qed.

Section isomorphic_image_is_rationals.
  Context `{Rationals Q} `{DecField F}.
  Context (f : Q → F) `{!Inverse f} `{!Bijective f} `{!SemiRing_Morphism f}.

  Instance iso_to_frac: RationalsToFrac F := λ Z _ _ _ _ _ _ _ _, rationals_to_frac Q Z ∘ f⁻¹.
  Hint Unfold iso_to_frac: typeclass_instances.

  Instance: Bijective (f⁻¹) := _.
  Instance: SemiRing_Morphism (f⁻¹) := {}.

  Lemma iso_is_rationals: Rationals F.
  Proof.
    repeat (split; unfold rationals_to_frac; try apply _).
    intros x y E.
    apply (injective (f ∘ integers_to_ring Z Q)).
    now rewrite 2!(to_ring_unique (f ∘ integers_to_ring Z Q)).
  Qed.
End isomorphic_image_is_rationals.

Section alt_Build_Rationals.
  Context `{DecField F} `{Integers Z} (F_to_fracZ : F → Frac Z) `{!SemiRing_Morphism F_to_fracZ} `{!Injective F_to_fracZ}.
  Context (Z_to_F : Z → F) `{!SemiRing_Morphism Z_to_F} `{!Injective Z_to_F}.

  Program Instance alt_to_frac: RationalsToFrac F := λ B _ _ _ _ _ _ _ _ x,
    frac (integers_to_ring Z B (num (F_to_fracZ x))) (integers_to_ring Z B (den (F_to_fracZ x))) _.
  Next Obligation.
    apply injective_ne_0.
    apply den_ne_0.
  Qed.

  Instance: ∀ `{Integers B}, Proper ((=) ==> (=)) (rationals_to_frac F B).
  Proof.
    intros. intros ? ? E.
    unfold equiv, Frac_equiv. simpl.
    rewrite <-2!preserves_mult.
    apply sm_proper.
    change (F_to_fracZ x = F_to_fracZ y).
    now apply sm_proper.
  Qed.

  Instance: ∀ `{Integers B}, SemiRing_Morphism (rationals_to_frac F B).
  Proof.
    intros.
    repeat (split; try apply _); unfold equiv, Frac_equiv; simpl.
       intros x y.
       rewrite <-?preserves_mult, <-preserves_plus, <-preserves_mult.
       apply sm_proper.
       change (F_to_fracZ (x + y) = F_to_fracZ x + F_to_fracZ y).
       apply preserves_plus.
      rewrite <-(preserves_0 (f:=integers_to_ring Z B)), <-(preserves_1 (f:=integers_to_ring Z B)),
         <-2!preserves_mult.
      apply sm_proper.
      change (F_to_fracZ 0 = 0).
      apply preserves_0.
     intros x y.
     rewrite <-?preserves_mult.
     apply sm_proper.
     change (F_to_fracZ (x * y) = F_to_fracZ x * F_to_fracZ y).
     apply preserves_mult.
    rewrite <-(preserves_1 (f:=integers_to_ring Z B)), <-2!preserves_mult.
    apply sm_proper.
    change (F_to_fracZ 1 = 1).
    apply preserves_1.
  Qed.

  Instance: ∀ `{Integers B}, Injective (rationals_to_frac F B).
  Proof.
    intros.
    split; try apply _.
    intros x y E. unfold equiv, Frac_equiv in E. simpl in E.
    rewrite <-2!preserves_mult in E.
    apply (injective F_to_fracZ).
    now apply (injective (integers_to_ring Z B)).
  Qed.

  Instance: ∀ `{Integers B}, Injective (integers_to_ring B F).
  Proof.
    intros.
    split; try apply _.
    intros x y E.
    apply (injective (Z_to_F ∘ integers_to_ring B Z)).
    now rewrite 2!(to_ring_unique (Z_to_F ∘ integers_to_ring B Z)).
  Qed.

  Lemma alt_Build_Rationals: Rationals F.
  Proof. split; intros; apply _. Qed.
End alt_Build_Rationals.
