Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Ring
  abstract_algebra theory.ring_as_ua interfaces.naturals theory.categories.

Section integers_to_ring.

  Variable Int: Type.

  Class IntegersToRing :=
    integers_to_ring: forall R `{RingMult R} `{RingPlus R} `{RingOne R} `{RingZero R} `{GroupInv R}, Int -> R.

End integers_to_ring.

Instance: Params (@integers_to_ring) 8.

Class Integers A {e plus mult opp zero one} `{IntegersToRing A} :=
  { integers_ring:> @Ring A e plus mult opp zero one
  ; integers_to_ring_mor:> forall B `{Ring B}, Ring_Morphism (integers_to_ring A B)
  ; integers_to_ring_arrow := (fun x =>
        @ring_as_ua.arrow_from_morphism_from_instance_to_object _ _ _ _ _ _ _ _ x (integers_to_ring A (x tt))
          (@integers_to_ring_mor _ _ _ _ _ _ _ (ring_as_ua.from_object x)) )
  ; integers_initial: proves_initial integers_to_ring_arrow }.

Section specializable.

  Context (Int N: Type) `{Equiv Int} `{RingMult Int} `{RingPlus Int} `{RingOne Int} `{GroupInv Int} `{RingZero Int} `{NaturalsToSemiRing N}.

  Class IntAsNat := int_as_nat: forall i: Int, { n: N | i = naturals_to_semiring N Int n } + { n: N | i == - naturals_to_semiring N Int n }.

  Class IntAbs := int_abs: forall i: Int, { n: N | naturals_to_semiring N Int n == i \/ - naturals_to_semiring N Int n == i }.
  Definition int_abs' `{IntAbs}: Int -> N := fun x => proj1_sig (int_abs x).

End specializable.

Instance: Params (@int_abs') 10.

Instance integer_precedes `{Integers Int}: Order Int := sr_precedes.

Instance: Params (@integer_precedes) 9.
