Require Import
 Morphisms Structures AbstractNaturals IntegerTheory FieldOps simpleZ FieldOrder.

Class Rationals A {e plus mult opp zero one mult_inv} :=
  { rationals_field:> @Field A e plus mult opp zero one mult_inv
  ; rationals_eqdec:> forall x y: A, Decision (x == y)
  ; rationals_frac: Surjective (fun p => integers_to_ring (Z nat) A (fst p) * / integers_to_ring (Z nat) A (snd p))
  ; rationals_embed_ints:> Injective (integers_to_ring (Z nat) A) }.

Lemma alt_Build_Rationals A Int (inject: Int -> A) `{Field A} {d: forall x y : A, Decision (x == y)} `{Integers Int} `{!Ring_Morphism inject}:
  Surjective (fun p => inject (fst p) * / inject (snd p)) -> Injective inject -> Rationals A.
Proof.
 intros.
 apply (@Build_Rationals A _ _ _ _ _ _ _ _ d).
  intro x.
  destruct (H2 x).
  exists (integers_to_ring Int (Z nat) (fst x0), integers_to_ring Int (Z nat) (snd x0)).
  simpl.
  pose proof dec_mult_inv_proper.
  rewrite (@integers_to_ring_unique' Int _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ (fun x => integers_to_ring (Z nat) A (integers_to_ring Int (Z nat) x)) inject ); try apply _.
  rewrite (@integers_to_ring_unique' Int _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ (fun x => integers_to_ring (Z nat) A (integers_to_ring Int (Z nat) x)) inject ); try apply _.
  assumption.
 intros x y E.
 apply (injective (integers_to_ring (Z nat) Int)).
 apply (injective inject).
 rewrite (integers_to_ring_unique _ (fun v => inject (integers_to_ring (Z nat) Int v))); [| apply _].
 rewrite (integers_to_ring_unique _ (fun v => inject (integers_to_ring (Z nat) Int v))); [| apply _].
 assumption.
Qed.

Section sec. Context `{Rationals Q}.

  Global Instance: Order Q := field_precedes.

  Global Instance: Injective (naturals_to_semiring nat Q).
  Proof.
   intros x y.
   intros. 
   apply (naturals_to_integers_injective).
   apply (injective (integers_to_ring (Z nat) Q)).
   do 2 rewrite (naturals_to_semiring_unique Q (fun v => integers_to_ring (Z nat) Q (naturals_to_semiring nat (Z nat) v)) _).
   assumption.
  Qed.

  Instance: OrdField Q. 
   (* making this global (as it should be) indirectly produces an [Add Ring] bug that i've presented to mattam *)

End sec.

Instance: Params (@field_precedes) 8.
