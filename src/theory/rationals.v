Require Import
  Morphisms Program
  abstract_algebra interfaces.rationals
  theory.naturals theory.integers theory.fields theory.jections
  natpair_integers.

Section alt_Build_Rationals.
Context A Int (inject: Int → A) `{Field A} {d: ∀ x y: A, Decision (x = y)}
  `{Integers Int} `{!SemiRing_Morphism inject} `{i : !Inverse (λ p, inject (fst p) * / inject (snd p))}.

Global Instance: Inverse (λ p, integers_to_ring (SRpair nat) A (fst p) * / integers_to_ring (SRpair nat) A (snd p)) :=
  λ x, (integers_to_ring Int (SRpair nat) (fst (inverse _ x)), integers_to_ring Int (SRpair nat) (snd (inverse _ x))).

Lemma alt_Build_Rationals: Surjective (λ p, inject (fst p) * / inject (snd p)) → Injective inject → Rationals A.
Proof with auto.
  intros sur ?.
  repeat (split; try apply _).
    intros x y E.
    unfold Basics.compose, id. simpl.
    change ((integers_to_ring (SRpair nat) A ∘ integers_to_ring Int (SRpair nat)) (fst (i x)) *
      / (integers_to_ring (SRpair nat) A ∘ integers_to_ring Int (SRpair nat)) (snd (i x)) = y).
    do 2 rewrite (integers.to_ring_unique_alt (integers_to_ring (SRpair nat) A ∘ integers_to_ring Int (SRpair nat)) inject).
    apply sur...
   intros x y E. rewrite E. reflexivity.
  intros x y ?.
  apply (injective (inject ∘ integers_to_ring (SRpair nat) Int)).
  do 2 rewrite (integers.to_ring_unique (inject ∘ integers_to_ring (SRpair nat) Int))...
Qed.
End alt_Build_Rationals.

Section contents. 
Context `{Rationals Q}.

Notation i_to_r := (integers_to_ring (SRpair nat) Q).

Lemma rationals_decompose_nat (x : Q) : ∃ num, ∃ den, 
  x = integers_to_ring (SRpair nat) Q num * / integers_to_ring (SRpair nat) Q den.
Proof.
  set (i := inverse (λ p, i_to_r (fst p) * / i_to_r (snd p))).
  exists (fst (i x)) (snd (i x)).
  symmetry.
  apply (rationals_frac _). reflexivity.
Qed.

Lemma rationals_decompose Z `{Integers Z} (x : Q) : ∃ num, ∃ den, 
  den ≠ 0 ∧ x = integers_to_ring Z Q num * / integers_to_ring Z Q den.
Proof with trivial.
  destruct (rationals_decompose_nat x) as [num [den E]].
  destruct (decide (den = 0)) as [F|F].
   exists (0:Z) (1:Z). split.
    apply (ne_zero _).
   rewrite rings.preserves_0, left_absorb.
   rewrite E, F, rings.preserves_0. 
   rewrite dec_mult_inv_0, right_absorb. reflexivity.
  exists (integers_to_ring _ Z num) (integers_to_ring _ Z den).
  split.
   apply rings.injective_not_0...
  do 2 rewrite <-(integers.to_ring_unique (integers_to_ring Z Q ∘ integers_to_ring (SRpair nat) Z)) in E...
Qed.

Global Instance injective_ints `{Integers Int} `{!SemiRing_Morphism (f: Int → Q)}: Injective f.
Proof.
  split; try apply _.
  intros x y E.
  apply (injective (integers_to_ring Int (SRpair nat))).
  eapply (rationals_embed_ints _).
  do 2 rewrite (integers.to_ring_unique_alt f (i_to_r ∘ integers_to_ring Int (SRpair nat))) in E. 
  assumption.
Qed.

Global Instance injective_nats `{Naturals N} `{!SemiRing_Morphism (f: N → Q)}: Injective f.
Proof with auto.
  split; try apply _.
  intros x y E.
  apply (injective (naturals_to_semiring N (SRpair nat))).
  eapply (rationals_embed_ints _).
  do 2 rewrite (naturals.to_semiring_unique_alt f (i_to_r ∘ naturals_to_semiring N (SRpair nat))) in E. 
  assumption.
Qed.
End contents.

Section isomorphism_is_rationals.
  Context `{Rationals Q} `{Field F} `{∀ x y: F, Decision (x = y)}.
  Context (f : Q → F) `{!Inverse f} `{!Bijective f} `{!SemiRing_Morphism f}.

  Definition isomorphism_is_inj_inv : Inverse (λ p, integers_to_ring (SRpair nat) F (fst p) * / integers_to_ring (SRpair nat) F (snd p)) 
    := inj_inv ∘ inverse f.
  
  Instance: Bijective (inverse f).
  Instance: SemiRing_Morphism (inverse f).

  Lemma isomorphism_is_rationals: Rationals F (inj_inv:=isomorphism_is_inj_inv). 
  Proof.
    repeat (split; try apply _).
      intros x y U. rewrite <- U. 
      unfold id, compose, inverse, isomorphism_is_inj_inv, compose.
      apply (injective (inverse f)).
      rewrite <-(@surjective_applied _ _ _ _ _ inj_inv (rationals_frac Q) (inverse f x)) at 3.
      rewrite rings.preserves_mult. rewrite preserves_dec_mult_inv.
      apply sg_mor. 
      rewrite <-(to_ring_unique (inverse f ∘ integers_to_ring (SRpair nat) F)). reflexivity.
      apply (_ : Proper ((=) ==> (=)) (/)). 
      rewrite <-(to_ring_unique (inverse f ∘ integers_to_ring (SRpair nat) F)). reflexivity. 
     intros x y E. rewrite E. reflexivity.
    intros x y E.
    apply (injective (f ∘ integers_to_ring (SRpair nat) Q)).
    do 2 rewrite (to_ring_unique (f ∘ integers_to_ring (SRpair nat) Q)). 
    assumption.
  Qed.
End isomorphism_is_rationals.
