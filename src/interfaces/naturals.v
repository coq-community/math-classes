Require Import
 Relation_Definitions Morphisms
 abstract_algebra theory.categories
 orders.semigroup.
Require
 varieties.semiring categories.variety.

Module bad.
  Class Naturals (A: semiring.Object) `{!InitialArrow A}: Prop :=
    { naturals_initial:> Initial A }.
End bad.

Section initial_maps.

  Variable A: Type.

  Class NaturalsToSemiRing :=
    naturals_to_semiring: Π B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A → B.

  Context `{NaturalsToSemiRing} `{SemiRing A} `{Π `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring B)}.

  Global Instance natural_initial_arrow: InitialArrow (semiring.object A).
   intro.
   exists (λ u => match u return A → y u with tt => naturals_to_semiring (y tt) end).
   abstract (simpl;
    apply (@semiring.mor_from_sr_to_alg (λ _ => A) _ _ (semiring.variety A) _ _ _ _ _);
    apply _).
  Defined. (* for some reason [Program] isn't cooperating here. look into it *)

End initial_maps.

Instance: Params (@naturals_to_semiring) 7.

Class Naturals A {e plus mult zero one} `{U: NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A e plus mult zero one
  ; naturals_to_semiring_mor:> Π `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_initial:> Initial (semiring.object A) }.

Implicit Arguments naturals_to_semiring_mor [[e] [plus] [mult] [zero] [one] [U] [Naturals] [e0] [plus0] [mult0] [zero0] [one0] ].
  (* todo: really necessary? *)

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
