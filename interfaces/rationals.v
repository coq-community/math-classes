Set Automatic Introduction.

Require Import
 Morphisms abstract_algebra theory.naturals theory.integers theory.fields
 natpair_integers orders.field.

Class Rationals A {e plus mult opp zero one mult_inv } `{Π x y: A, Decision (x = y)} {inj_inv}: Prop :=
  { rationals_field:> @Field A e plus mult opp zero one mult_inv
  ; rationals_frac: Surjective (λ p => integers_to_ring (Z nat) A (fst p) * / integers_to_ring (Z nat) A (snd p)) (Inv0:=inj_inv)
  ; rationals_embed_ints: Injective (integers_to_ring (Z nat) A) }.

(* rational_embed_ints is not declared as a coercion because we prove a stronger result in a moment *)

(* This definition of Rationals uses maps from plain (Z nat) for simplicity, but maps from
 any model of the integers suffice, as the following "smart" constructor shows: *)

Section alt_Build_Rationals.

  Context A Int (inject: Int → A) `{Field A} {d: Π x y: A, Decision (x = y)}
    `{Integers Int} `{!Ring_Morphism inject} `{!Inv (λ p => inject (fst p) * / inject (snd p))}.

  Global Instance: Inv (λ p => integers_to_ring (Z nat) A (fst p) * / integers_to_ring (Z nat) A (snd p)) :=
    λ x => (integers_to_ring Int (Z nat) (fst (inv x)), integers_to_ring Int (Z nat) (snd (inv x))).

  Lemma alt_Build_Rationals: Surjective (λ p => inject (fst p) * / inject (snd p)) → Injective inject → Rationals A.
  Proof with auto.
   intros sur ?.
   apply (Build_Rationals A _ _ _ _ _ _ _ _ _)...
    constructor.
     intro x.
     unfold Basics.compose, id in *.
     transitivity (inject (fst (inv x)) * / inject (snd (inv x))).
      2: apply sur.
     pose proof (integers_to_ring_unique' _
       (λ x => integers_to_ring (Z nat) A (integers_to_ring Int (Z nat) x)) inject) as B.
     pose proof (B (fst (inv x))). simpl in H3. rewrite H3.
     pose proof (B (snd (inv x))). simpl in H4. rewrite H4.
     reflexivity.
    constructor; try apply _.
    repeat intro.
    rewrite H3.
    reflexivity.
   constructor. 2: apply _.
   intros x y ?.
   apply (injective (integers_to_ring (Z nat) Int)), (injective inject).
   do 2 rewrite (integers_to_ring_unique _ (λ v => inject (integers_to_ring (Z nat) Int v)))...
  Qed. (* todo: too long *)

End alt_Build_Rationals.

Require Import Program.

Section sec. Context `{Rationals Q}.

  Global Instance: Order Q := field_precedes.

  Global Instance injective_ints `{Integers Int} `{!Ring_Morphism (f: Int → Q)}: Injective f.
  Proof with try apply _.
   assert (f = integers_to_ring (Z nat) Q ∘ integers_to_ring Int (Z nat)).
    apply (@integers_to_ring_unique' Int _ _ _ _ _ _ _ _ Q _ _ _ _ _ _)...
    unfold compose...
   pose proof rationals_embed_ints.
   apply (Injective_proper f (integers_to_ring (Z nat) Q ∘ integers_to_ring Int (Z nat)))... (* todo: make it so that we can use [rewrite] here *)
   assumption.
  Qed.

  Global Instance injective_nats `{Naturals N} `{!SemiRing_Morphism (f: N → Q)}: Injective f.
  Proof with auto.
   pose proof (to_semiring_unique' f (naturals_to_semiring N Q) _ _).
   apply (Injective_proper f (naturals_to_semiring N Q)). (* todo: make it so that we can use [rewrite] here *)
    assumption.
   constructor. 2: apply _.
   intros x y ?.
   apply (injective (naturals_to_semiring N (Z nat))).
   apply (injective (integers_to_ring (Z nat) Q)).
   do 2 rewrite (theory.naturals.to_semiring_unique Q
     (λ v => integers_to_ring (Z nat) Q (naturals_to_semiring N (Z nat) v)))...
  Qed.

  Instance: OrdField Q.
   (* making this global (as it should be) indirectly produces an [Add Ring] bug that i've presented to mattam *)

End sec.

Instance: Params (@field_precedes) 8.
