Require Import
  Relation_Definitions Morphisms
  Structures CatStuff RingOps FieldOps
  SemiRingAlgebra RingAlgebra UniversalAlgebra.

(*Definition canonical_semiring_map A `{SemiRing.*)

Section initial_maps.

  Variable A: Type.

  Class NaturalsToSemiRing :=
    naturals_to_semiring: forall B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A -> B.
  Class IntegersToRing :=
    integers_to_ring: forall B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B} `{GroupInv B}, A -> B.

End initial_maps.

Class Naturals A {e plus mult zero one} `{NaturalsToSemiRing A} :=
  { naturals_ring:> SemiRing e plus mult zero one
  ; naturals_to_semiring_mor:> forall `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_to_semiring_arrow := (fun x: semiring.Object =>
        @semiring.arrow_from_morphism_from_instance_to_object A _ _ _ _ _ _ x (naturals_to_semiring A (x tt))
           (@naturals_to_semiring_mor (x tt) _ _ _ _ _ (semiring.from_object x)) )
  ; naturals_initial: proves_initial naturals_to_semiring_arrow }.

Implicit Arguments naturals_to_semiring_mor [[e] [plus] [mult] [zero] [one] [H] [Naturals] [e0] [plus0] [mult0] [zero0] [one0] [H0]].
Implicit Arguments naturals_to_semiring_arrow [[e] [plus] [mult] [zero] [one] [H] [Naturals]].

Class Integers A {e plus mult opp zero one} `{IntegersToRing A} :=
  { integers_ring:> Ring e plus mult opp zero one
  ; integers_to_ring_mor: forall `{Ring B}, Ring_Morphism (integers_to_ring A B)
  ; integers_to_ring_arrow := (fun x: ring.Object =>
        @ring.arrow_from_morphism_from_instance_to_object _ _ _ _ _ _ _ _ x (integers_to_ring A (x tt))
           (@integers_to_ring_mor _ _ _ _ _ _ _ (ring.from_object x)) )
  ; integers_initial: proves_initial integers_to_ring_arrow }.

Class Rationals A {e plus mult opp zero one mult_inv leq} :=
  { rationals_ordfield:> OrdField e plus mult opp zero one mult_inv leq
  ; rationals_eqdec:> forall x y: A, Decision (x == y)
  ; rationals_frac: forall `{i: Integers B} (t := integers_to_ring B A) (a: A),
     exists num: B, exists den: B, a == t num * / t den }.
	(* todo: further require that denominator is nonzero *)

(* Above, initiality is stated in categorical/universal algebra terms, which isn't the most
 pleasant form to subsequently reason about. We therefore state its key properties in
 more pleasant terms of canonical SemiRing_Morphisms, below. *)

Lemma naturals_to_semiring_unique `{Naturals N} SR `{SemiRing SR} (f: N -> SR) (h: SemiRing_Morphism f):
 forall x, f x == naturals_to_semiring N SR x.
Proof.
 intros.
 set (@semiring.arrow_from_morphism_from_instance_to_object N _ _ _ _ _ _ (semiring.as_object SR) f h).
 symmetry.
 apply (naturals_initial (semiring.as_object SR) a tt x).
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

Lemma integers_to_ring_unique `{Integers Int} R `{Ring R} (f: Int -> R) (h: Ring_Morphism f):
 forall x, f x == integers_to_ring Int R x.
Proof.
 intros.
 set (@ring.arrow_from_morphism_from_instance_to_object Int _ _ _ _ _ _ _ (ring.as_object R) f h).
 symmetry.
 apply (integers_initial (ring.as_object R) a tt x).
Qed.

Lemma iso_ints `{Integers A} B `{Integers B}: forall a: A,
  integers_to_ring B A (integers_to_ring A B a) == a.
Proof.
 intros.
 pose proof (@integers_initial A _ _ _ _ _ _ _ _ (ring.as_object A) cat_id tt a).
 set (comp (integers_to_ring_arrow (ring.as_object A)) (integers_to_ring_arrow (ring.as_object B))).
 pose proof (@integers_initial A _ _ _ _ _ _ _ _ (ring.as_object A) a0 tt a).
 simpl in *.
 rewrite <- H4.
 assumption.
Qed.

Lemma ints_through_third `{Integers A} B `{Integers B} C `{Ring C}: forall a: A,
  integers_to_ring B C (integers_to_ring A B a) == integers_to_ring A C a.
Proof.
 intros.
 set (comp (integers_to_ring_arrow (ring.as_object C)) (integers_to_ring_arrow (ring.as_object B)): ring.Arrow (ring.as_object A) (ring.as_object C)).
 pose proof (@integers_initial A _ _ _ _ _ _ _ _ (ring.as_object C) a0 tt a).
 subst a0.
 simpl in H4.
 symmetry.
 assumption.
Qed.

Lemma naturals_to_integers_injective `{Naturals N} `{Integers Int} x y:
  naturals_to_semiring N Int x == naturals_to_semiring N Int y -> x == y.
Proof.
 intros.
Admitted.

