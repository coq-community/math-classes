Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Ring
  abstract_algebra interfaces.naturals theory.categories.
Require
  varieties.ring.

Section initial_maps.

  Variable Int: Type.

  Class IntegersToRing :=
    integers_to_ring: Π R `{RingMult R} `{RingPlus R} `{RingOne R} `{RingZero R} `{GroupInv R}, Int → R.

  Context `{IntegersToRing} (B: ring.Object).

  Definition f u: Int → B u :=
    match u return Int → B u with tt => H (B tt) _ _ _ _ _ end.
      (* todo: use integers_to_ring here? *)

  Definition initial_arrow `{Ring Int} {d: Ring_Morphism (H (B tt) _ _ _ _ _)}: ring.object Int ⟶ B.
  Proof.
   simpl.
   intros.
   exists f.
   simpl.
   apply (@ring.mor_from_sr_to_alg (λ _ => Int) _ (ring.implementation Int) (ring.variety Int) B _ _ _).
   assumption.
  Defined. (* todo: clean up *)

End initial_maps.

Instance: Params (@integers_to_ring) 8.

Class Integers A {e plus mult opp zero one} `{IntegersToRing A} :=
  { integers_ring:> @Ring A e plus mult opp zero one
  ; integers_to_ring_mor:> Π `{Ring B}, Ring_Morphism (integers_to_ring A B)
  ; integers_initial: proves_initial (λ B => initial_arrow A B) }.

Section specializable.

  Context (Int N: Type) `{Equiv Int} `{RingMult Int} `{RingPlus Int} `{RingOne Int} `{GroupInv Int} `{RingZero Int} `{NaturalsToSemiRing N}.

  Class IntAsNat := int_as_nat: Π i: Int, { n: N | i = naturals_to_semiring N Int n } + { n: N | i = - naturals_to_semiring N Int n }.

  Class IntAbs := int_abs: Π i: Int, { n: N | naturals_to_semiring N Int n = i ∨ - naturals_to_semiring N Int n = i }.
  Definition int_abs' `{IntAbs}: Int → N := λ x => proj1_sig (int_abs x).

End specializable.

Instance: Params (@int_abs') 10.

Instance integer_precedes `{Integers Int}: Order Int := sr_precedes.

Instance: Params (@integer_precedes) 9.
