Require Import
  abstract_algebra interfaces.integers natpair_integers.

Class Rationals A {e plus mult opp zero one mult_inv } `{∀ x y: A, Decision (x = y)} {inj_inv}: Prop :=
  { rationals_field:> @Field A e plus mult opp zero one mult_inv
  ; rationals_frac: Surjective (λ p, integers_to_ring (Z nat) A (fst p) * / integers_to_ring (Z nat) A (snd p)) (inv:=inj_inv)
  ; rationals_embed_ints: Injective (integers_to_ring (Z nat) A) }.

(* rational_embed_ints is not declared as a coercion because we prove a stronger result in a moment *)

(* This definition of Rationals uses maps from plain (Z nat) for simplicity, but maps from
 any model of the integers suffice, as the following "smart" constructor shows: *)