Set Automatic Introduction.

Require Import
 Morphisms abstract_algebra theory.naturals theory.integers theory.fields
 natpair_integers orders.field.

Class Rationals A {e plus mult opp zero one mult_inv} :=
  { rationals_field:> @Field A e plus mult opp zero one mult_inv
  ; rationals_eqdec:> forall x y: A, Decision (x == y)
  ; rationals_frac: Surjective (fun p => integers_to_ring (Z nat) A (fst p) * / integers_to_ring (Z nat) A (snd p))
  ; rationals_embed_ints:> Injective (integers_to_ring (Z nat) A) }.

(* This definition of Rationals uses maps from plain (Z nat) for simplicity, but maps from
 any model of the integers suffice, as the following "smart" constructor shows: *)

Lemma alt_Build_Rationals A Int (inject: Int -> A) `{Field A} {d: forall x y : A, Decision (x == y)} `{Integers Int} `{!Ring_Morphism inject}:
  Surjective (fun p => inject (fst p) * / inject (snd p)) -> Injective inject -> Rationals A.
Proof with auto.
 intros sur ?.
 apply (Build_Rationals A _ _ _ _ _ _ _ _ _).
  intro x.
  destruct (sur x) as [[y z] ?].
  exists (integers_to_ring Int (Z nat) y, integers_to_ring Int (Z nat) z). simpl.
  pose proof dec_mult_inv_proper.
  do 2 rewrite (integers_to_ring_unique' _
    (fun x => integers_to_ring (Z nat) A (integers_to_ring Int (Z nat) x)) inject)...
 intros x y ?.
 apply (injective (integers_to_ring (Z nat) Int)), (injective inject).
 do 2 rewrite (integers_to_ring_unique _ (fun v => inject (integers_to_ring (Z nat) Int v)))...
Qed.

Section sec. Context `{Rationals Q}.

  Global Instance: Order Q := field_precedes.

  Global Instance naturals_to_rationals_injective `{Naturals N}: Injective (naturals_to_semiring N Q).
  Proof with auto.
   intros x y ?.
   apply (injective (naturals_to_semiring N (Z nat))).
   apply (injective (integers_to_ring (Z nat) Q)).
   do 2 rewrite (theory.naturals.to_semiring_unique Q
     (fun v => integers_to_ring (Z nat) Q (naturals_to_semiring N (Z nat) v)))...
  Qed.

  Instance: OrdField Q. 
   (* making this global (as it should be) indirectly produces an [Add Ring] bug that i've presented to mattam *)

End sec.

Instance: Params (@field_precedes) 8.
