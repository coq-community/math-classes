Require Import
 Relation_Definitions Morphisms
 abstract_algebra theory.categories
 orders.semigroup.
Require
 varieties.semiring.

Section initial_maps.
  Variable A: Type.
  Class NaturalsToSemiRing :=
    naturals_to_semiring: forall B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A -> B.
End initial_maps.

Instance: Params (@naturals_to_semiring) 7.

Class Naturals A {e plus mult zero one} `{NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A e plus mult zero one
  ; naturals_to_semiring_mor:> forall `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_to_semiring_arrow := (fun x =>
        @varieties.semiring.arrow_from_morphism_from_instance_to_object A _ _ _ _ _ _ x (naturals_to_semiring A (x tt))
           (@naturals_to_semiring_mor (x tt) _ _ _ _ _ (varieties.semiring.from_object x)) )
  ; naturals_initial: proves_initial naturals_to_semiring_arrow }.

Implicit Arguments naturals_to_semiring_mor [[e] [plus] [mult] [zero] [one] [H] [Naturals] [e0] [plus0] [mult0] [zero0] [one0] [H0]].
Implicit Arguments naturals_to_semiring_arrow [[e] [plus] [mult] [zero] [one] [H] [Naturals]].

(* Specializable operations: *)

Class NatDistance N `{Equiv N} `{RingPlus N}
  := nat_distance: forall (x y: N), { z: N | x + z == y \/ y + z == x }.

(* Order: *)

Instance natural_precedes `{Naturals N}: Order N := sg_precedes.

(* The following NaturalsToSemiRing instance really belongs in implementations.peano_naturals, but
 having it there would mean that sr_precedes (and things built on it, like interfaces.integers must also
 depend on that implementation, which is undesireable. *)

Instance nat_to_semiring: NaturalsToSemiRing nat :=
  fun _ _ _ _ _ => fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Definition sr_precedes `{SemiRing R}: Order R := fun x y: R =>
  exists z: nat, x + naturals_to_semiring nat R z == y.

Instance: Params (@sr_precedes) 7.
