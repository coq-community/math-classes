Require Import
 Relation_Definitions Morphisms
 Structures CatStuff RingOps
 SemiRingAlgebra UniversalAlgebra SemiGroupOrder.

Section initial_maps.
  Variable A: Type.
  Class NaturalsToSemiRing :=
    naturals_to_semiring: forall B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A -> B.
End initial_maps.

Instance: Params (@naturals_to_semiring) 7.

Class Naturals A {e plus mult zero one} `{NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A e plus mult zero one
  ; naturals_to_semiring_mor:> forall `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_to_semiring_arrow := (fun x: semiring.Object =>
        @semiring.arrow_from_morphism_from_instance_to_object A _ _ _ _ _ _ x (naturals_to_semiring A (x tt))
           (@naturals_to_semiring_mor (x tt) _ _ _ _ _ (semiring.from_object x)) )
  ; naturals_initial: proves_initial naturals_to_semiring_arrow }.

Implicit Arguments naturals_to_semiring_mor [[e] [plus] [mult] [zero] [one] [H] [Naturals] [e0] [plus0] [mult0] [zero0] [one0] [H0]].
Implicit Arguments naturals_to_semiring_arrow [[e] [plus] [mult] [zero] [one] [H] [Naturals]].

(* Important operations that specific implementations might wish to specialize: *)

Class NatDistance N `{Equiv N} `{RingPlus N}
  := nat_distance: forall (x y: N), { z: N | x + z == y \/ y + z == x }.

(* Key properties of the canonical semiring maps (to avoid having to refer to categorical/universal algebra stuff all the time): *)

Lemma naturals_to_semiring_unique `{Naturals N} SR `{SemiRing SR} (f: N -> SR) (h: SemiRing_Morphism f):
 forall x, f x == naturals_to_semiring N SR x.
Proof.
 intros.
 set (@semiring.arrow_from_morphism_from_instance_to_object N _ _ _ _ _ _ (semiring.as_object SR) f h).
 symmetry.
 apply (naturals_initial (semiring.as_object SR) a tt x).
Qed.

Lemma naturals_to_semiring_unique' `{Naturals N} `{SemiRing SR} (f g: N -> SR):
 SemiRing_Morphism f -> SemiRing_Morphism g ->
   forall x, f x == g x.
Proof.
 intros.
 rewrite (naturals_to_semiring_unique _ f _ _).
 rewrite (naturals_to_semiring_unique _ g _ _).
 reflexivity.
Qed.

Lemma iso_nats A `{Naturals A} B `{Naturals B}: forall a: A,
 naturals_to_semiring B A (naturals_to_semiring A B a) == a.
Proof.
 intros.
 pose proof (@naturals_initial A _ _ _ _ _ _ _ (semiring.as_object A) cat_id tt a).
 set (comp (naturals_to_semiring_arrow B (semiring.as_object A)) (naturals_to_semiring_arrow A (semiring.as_object B))).
 pose proof (@naturals_initial A _ _ _ _ _ _ _ (semiring.as_object A) a0 tt a).
 simpl in *.
 rewrite <- H4.
 assumption.
Qed.

Lemma iso_nats' `{Naturals A} `{Naturals B} (f: A -> B) (g: B -> A):
 SemiRing_Morphism f -> SemiRing_Morphism g -> forall a, f (g a) == a.
Proof.
 intros.
 rewrite (naturals_to_semiring_unique _ _ _ _).
 rewrite (naturals_to_semiring_unique _ g _ _).
 apply (iso_nats B A).
Qed.

(* Order: *)

Instance natural_precedes `{Naturals N}: Order N := sg_precedes.

Lemma preserves_naturals_order_back `{Naturals A} `{Naturals B} (f: A -> B) `{!SemiRing_Morphism f} (x y: A): f x <= f y -> x <= y.
Proof.
 intros.
 rewrite <- (iso_nats' (naturals_to_semiring _ _) f _ _ y).
 rewrite <- (iso_nats' (naturals_to_semiring _ _) f _ _ x).
 apply (@preserves_sg_order B _ ring_plus _ A _ _ _ _ _).
 assumption.
Qed.

Lemma preserves_naturals_order `{Naturals A} `{Naturals B} (f: A -> B) `{!SemiRing_Morphism f} (x y: A): x <= y <-> f x <= f y.
Proof.
 split.
  apply preserves_sg_order. apply _.
 apply preserves_naturals_order_back. apply _.
Qed.
