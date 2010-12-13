Set Automatic Introduction.

Require Import
  Morphisms Program
  abstract_algebra theory.naturals theory.integers theory.fields theory.jections interfaces.rationals
  natpair_integers orders.field.

Section alt_Build_Rationals.

  Context A Int (inject: Int → A) `{Field A} {d: ∀ x y: A, Decision (x = y)}
    `{Integers Int} `{!Ring_Morphism inject} `{!Inverse (λ p, inject (fst p) * / inject (snd p))}.

  Global Instance: Inverse (λ p, integers_to_ring (Z nat) A (fst p) * / integers_to_ring (Z nat) A (snd p)) :=
    λ x, (integers_to_ring Int (Z nat) (fst (inverse _ x)), integers_to_ring Int (Z nat) (snd (inverse _ x))).

  Lemma alt_Build_Rationals: Surjective (λ p, inject (fst p) * / inject (snd p)) → Injective inject → Rationals A.
  Proof with auto.
   intros sur ?.
   split.
      apply _.
     constructor.
     intro x.
     unfold Basics.compose, id in *.
     transitivity (inject (fst (inverse _ x)) * / inject (snd (inverse _ x))).
      2: apply sur...
     pose proof (integers.to_ring_unique' 
       (integers_to_ring (Z nat) A ∘ integers_to_ring Int (Z nat)) inject) as B.
     pose proof (B (fst (inverse _ x)) (fst (inverse _ x)) (reflexivity _)) as P1. simpl in P1. rewrite P1.
     pose proof (B (snd (inverse _ x)) (snd (inverse _ x)) (reflexivity _)) as P2. simpl in P2. rewrite P2.
     reflexivity.
    constructor; try apply _.
    intros x y E.
    rewrite E.
    reflexivity.
   constructor. 2: apply _.
   intros x y ?.
   apply (injective (integers_to_ring (Z nat) Int)), (injective inject).
   pose proof (integers.to_ring_unique (inject ∘ integers_to_ring (Z nat) Int)) as P.
   unfold compose in P. do 2 rewrite P...
  Qed. (* todo: too long *)

End alt_Build_Rationals.

Section embedding. 
  Context `{Rationals Q}.

  Global Instance injective_ints `{Rationals Q} `{Integers Int} `{!Ring_Morphism (f: Int → Q)}: Injective f.
  Proof with try apply _.
    assert (f = integers_to_ring (Z nat) Q ∘ integers_to_ring Int (Z nat)).
     apply (integers.to_ring_unique')...
     unfold compose...
    pose proof rationals_embed_ints.
    apply (Injective_proper f (integers_to_ring (Z nat) Q ∘ integers_to_ring Int (Z nat)))... (* todo: make it so that we can use [rewrite] here *)
    assumption.
  Qed.

  Global Instance injective_nats `{Naturals N} `{!SemiRing_Morphism (f: N → Q)}: Injective f.
  Proof with auto.
   pose proof (naturals.to_semiring_unique' f (naturals_to_semiring N Q)).
   apply (Injective_proper f (naturals_to_semiring N Q)). (* todo: make it so that we can use [rewrite] here *)
    assumption.
   constructor. 2: apply _.
   intros x y ?.
   apply (injective (naturals_to_semiring N (Z nat))).
   apply (injective (integers_to_ring (Z nat) Q)).
   pose proof (naturals.to_semiring_unique
     (integers_to_ring (Z nat) Q ∘ naturals_to_semiring N (Z nat))) as P.
   unfold compose in P. do 2 rewrite P...
  Qed.
End embedding.

Section isomorphism_is_rationals.
  Context `{Rationals Q} `{Field F} `{∀ x y: F, Decision (x = y)}.
  Context (f : Q → F) `{!Inverse f} `{!Bijective f} `{!Ring_Morphism f} `{!Ring_Morphism (inverse f)}.

  Definition isomorphism_is_inj_inv : Inverse (λ p, integers_to_ring (Z nat) F (fst p) * / integers_to_ring (Z nat) F (snd p)) 
    := inj_inv ∘ inverse f.
  
  Instance: Bijective (inverse f).

  Lemma isomorphism_is_rationals: Rationals F (inj_inv:=isomorphism_is_inj_inv). 
  Proof.
    repeat (split; try apply _).
    intros x y U. rewrite <- U. unfold id, compose, inverse, isomorphism_is_inj_inv, compose.
    apply (injective (inverse f)).
    rewrite <-(@surjective_applied _ _ _ _ _ inj_inv (rationals_frac Q) (inverse f x)) at 3.
    rewrite rings.preserves_mult. rewrite preserves_dec_mult_inv.
    apply sg_mor. 
    rewrite <-(to_ring_unique (inverse f ∘ integers_to_ring (Z nat) F)). reflexivity.
    apply (_ : Proper ((=) ==> (=)) dec_mult_inv). 
    rewrite <-(to_ring_unique (inverse f ∘ integers_to_ring (Z nat) F)). reflexivity. 
    intros x y E. rewrite E. reflexivity.
    intros x y E.
    apply (injective (f ∘ integers_to_ring (Z nat) Q)).
    do 2 rewrite (to_ring_unique (f ∘ integers_to_ring (Z nat) Q)). 
    assumption.
  Qed.
End isomorphism_is_rationals.
