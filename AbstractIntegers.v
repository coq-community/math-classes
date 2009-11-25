(* Integers interface along with properties we can show without needing any model. *)

Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Ring
  Structures CatStuff RingOps
  SemiRingAlgebra RingAlgebra UniversalAlgebra
  AbstractNaturals SemiRingOrder.

Section integers_to_ring.

  Variable Int: Type.

  Class IntegersToRing :=
    integers_to_ring: forall R `{RingMult R} `{RingPlus R} `{RingOne R} `{RingZero R} `{GroupInv R}, Int -> R.

End integers_to_ring.

Instance: Params (@integers_to_ring) 8.

Class Integers A {e plus mult opp zero one} `{IntegersToRing A} :=
  { integers_ring:> @Ring A e plus mult opp zero one
  ; integers_to_ring_mor:> forall B `{Ring B}, Ring_Morphism (integers_to_ring A B)
  ; integers_to_ring_arrow := (fun x: ring.Object =>
        @ring.arrow_from_morphism_from_instance_to_object _ _ _ _ _ _ _ _ x (integers_to_ring A (x tt))
          (@integers_to_ring_mor _ _ _ _ _ _ _ (ring.from_object x)) )
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

Lemma integers_to_ring_unique `{Integers Int} R `{Ring R} (f: Int -> R) (h: Ring_Morphism f):
 forall x, f x == integers_to_ring Int R x.
Proof.
 intros. symmetry.
 set (a := @ring.arrow_from_morphism_from_instance_to_object Int _ _ _ _ _ _ _ (ring.as_object R) f h).
 apply (integers_initial (ring.as_object R) a tt x).
Qed.

Lemma integers_to_ring_unique' `{Integers Int} R `{Ring R}
  (f g: Int -> R) (h: Ring_Morphism f) (u: Ring_Morphism g):
 forall x, f x == g x.
Proof.
 intros.
 rewrite (integers_to_ring_unique R f); [| apply _].
 rewrite (integers_to_ring_unique R g); [| apply _].
 reflexivity.
Qed.

Lemma int_to_ring_injective `{Ring A} `{Integers B} 
 (f: A -> B) (g: B -> A) `{!Ring_Morphism f} `{!Ring_Morphism g}: Injective g.
Proof with auto.
 intros x y E.
 assert (Ring_Morphism (fun v => f (g v))).
  apply _.
 assert (Ring_Morphism (fun v: B => v)).
  repeat (constructor; try apply _; try reflexivity; repeat intro; try assumption).
 rewrite <- (integers_to_ring_unique' B (fun v => f (g v)) (fun v => v) _ _ x).
 rewrite <- (integers_to_ring_unique' B (fun v => f (g v)) (fun v => v) _ _ y).
 rewrite E. reflexivity.
Qed.

Instance int_to_int_injective `{Integers A} `{Integers B} (f: A -> B) `{!Ring_Morphism f}: Injective f.
Proof. apply int_to_ring_injective with (integers_to_ring B A); apply _. Qed.

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
