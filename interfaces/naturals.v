Require Import
 Relation_Definitions Morphisms
 abstract_algebra theory.categories
 orders.semigroup.
Require
 varieties.semiring categories.variety.

Section initial_maps.

  Variable A: Type.

  Class NaturalsToSemiRing :=
    naturals_to_semiring: Π B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A → B.

  Context `{NaturalsToSemiRing} (B: semiring.Object).

  Definition f u: A → B u :=
    match u return A → B u with tt => H (B tt) _ _ _ _ end.

  Definition initial_arrow `{SemiRing A} {d: SemiRing_Morphism (H (B tt) _ _ _ _)}: semiring.object A ⟶ B.
  Proof.
   exists f.
   simpl.
   apply (@semiring.mor_from_sr_to_alg (λ _ => A) _ (semiring.implementation A) (semiring.variety A) B _ _ _ _).
   assumption.
  Defined. (* todo: clean up *)

End initial_maps.

Instance: Params (@naturals_to_semiring) 7.

Class Naturals A {e plus mult zero one} `{U: NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A e plus mult zero one
  ; naturals_to_semiring_mor:> Π `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_initial: proves_initial (λ B => initial_arrow A B) }.

Implicit Arguments naturals_to_semiring_mor [[e] [plus] [mult] [zero] [one] [U] [Naturals] [e0] [plus0] [mult0] [zero0] [one0] ].

(* Specializable operations: *)

Class NatDistance N `{Equiv N} `{RingPlus N}
  := nat_distance: Π (x y: N), { z: N | x + z = y ∨ y + z = x }.

(* Order: *)

Instance natural_precedes `{Naturals N}: Order N := sg_precedes.

(* The following NaturalsToSemiRing instance really belongs in implementations.peano_naturals, but
 having it there would mean that sr_precedes (and things built on it, like interfaces.integers must also
 depend on that implementation, which is undesireable. *)

Instance nat_to_semiring: NaturalsToSemiRing nat :=
  λ _ _ _ _ _ => fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Definition sr_precedes `{SemiRing R}: Order R :=
  λ x y: R => exists z: nat, x + naturals_to_semiring nat R z = y.

Instance: Params (@sr_precedes) 7.
