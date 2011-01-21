Require Import
  abstract_algebra interfaces.integers natpair_integers
  theory.fields.

Section rationals.
  Context A `{field : Field A} `{∀ x y: A, Decision (x = y)}.

  Class Rationals {inj_inv}: Prop :=
  { rationals_field:> Field A
  ; rationals_frac: Surjective (λ p, integers_to_ring (SRpair nat) A (fst p) * / integers_to_ring (SRpair nat) A (snd p)) (inv:=inj_inv)
  ; rationals_embed_ints: Injective (integers_to_ring (SRpair nat) A) }.
End rationals.

(* rational_embed_ints is not declared as a coercion because we prove a stronger result in a moment *)

(* This definition of Rationals uses maps from plain (SRpair nat) for simplicity, but maps from
 any model of the integers suffice, as the "smart" constructor in theory.rationals shows *)