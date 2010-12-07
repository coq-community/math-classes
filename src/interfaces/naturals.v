Set Automatic Coercions Import.

Require Import
 Relation_Definitions Morphisms
 abstract_algebra theory.categories.
Require
 varieties.semiring categories.variety.

Module bad.
  Class Naturals (A: semiring.Object) `{!InitialArrow A}: Prop :=
    { naturals_initial:> Initial A }.
End bad.

Section initial_maps.

  Variable A: Type.

  Class NaturalsToSemiRing :=
    naturals_to_semiring: ∀ B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A → B.

  Context `{NaturalsToSemiRing} `{SemiRing A} `{∀ `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring B)}.

  Program Definition natural_initial_arrow: InitialArrow (semiring.object A) :=
    λ y u, match u return A → y u with tt => naturals_to_semiring (y tt) end.

  Next Obligation.
   apply (@semiring.mor_from_sr_to_alg (λ _, A) _ _ (semiring.variety A)); apply _.
  Qed.

  Global Existing Instance natural_initial_arrow.
   (* For some reason if we try to make it an instance immediately upon
    definition, Program suddenly generates 5 subgoals.. *)

  Lemma natural_initial (same_morphism : ∀ `{SemiRing B} {h :  A → B} `{!SemiRing_Morphism h}, naturals_to_semiring B = h) : 
    Initial (semiring.object A).
  Proof.
    intros y [x h] [] ?. simpl in *.
    apply same_morphism.
      apply semiring.decode_variety_and_ops. 
     apply (@semiring.decode_morphism_and_ops _ _ _ _ _ _ _ _ _ h).
    reflexivity.
  Qed.

End initial_maps.

Instance: Params (@naturals_to_semiring) 7.

Class Naturals A {e plus mult zero one} `{U: NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A e plus mult zero one
  ; naturals_to_semiring_mor:> ∀ `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_initial:> Initial (semiring.object A) }.

Implicit Arguments naturals_to_semiring_mor [[e] [plus] [mult] [zero] [one] [U] [Naturals] [e0] [plus0] [mult0] [zero0] [one0] ].
  (* todo: really necessary? *)

(* Specializable operations: *)

Class NatDistance N `{Equiv N} `{RingPlus N}
  := nat_distance: ∀ (x y: N), { z: N | x + z = y ∨ y + z = x }.

(* Order: *)

(* The following NaturalsToSemiRing instance really belongs in implementations.peano_naturals, but
 having it there would mean that sr_precedes (and things built on it, like interfaces.integers must also
 depend on that implementation, which is undesireable. *)

Instance: NaturalsToSemiRing nat :=
  λ _ _ _ _ _, fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

(* We give this order a low priority because it does not make a lot of sense for 
  semirings in general. Yet, it makes more sense than sg_precedes, so it has priority
  9 instead of 10. *)
Instance sr_precedes `{SemiRing R} : Order R | 9 :=
  λ x y: R, ∃ z: nat, x + naturals_to_semiring nat R z = y.
Instance: Params (@sr_precedes) 7.

(* Notice that it is also possible to use sg_precedes instead of sr_precedes for the naturals.
  However, now we have the same order for the naturals and the integers *)
