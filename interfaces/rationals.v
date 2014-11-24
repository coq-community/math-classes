Require Import
  abstract_algebra interfaces.integers field_of_fractions theory.integers.

Section rationals_to_frac.
  Context (A : Type).
  Class RationalsToFrac := rationals_to_frac : ∀ B `{Integers B}, A → Frac B.
End rationals_to_frac.

(*
We specify the Rationals as a field that contains the integers and can be embedded
into the field of integers fractions. Since we do not want to fix a specific integer
representation in this interface, we quantify over all integer implementations.
However, when constructing an instance of the rationals it is generally inconvenient
to prove that the required properties hold for all possible integer implementations.
Therefore we provide a way (theory.rationals.alt_Build_Rationals) to construct
a rationals implementation if the required properties hold for some specific
implementation of the integers.
*)

Class Rationals A {e plus mult zero one neg recip} `{U : !RationalsToFrac A} : Prop :=
  { rationals_field:> @DecField A e plus mult zero one neg recip
  ; rationals_frac :> ∀ `{Integers Z}, Injective (rationals_to_frac A Z)
  ; rationals_frac_mor :> ∀ `{Integers Z}, SemiRing_Morphism (rationals_to_frac A Z)
  ; rationals_embed_ints :> ∀ `{Integers Z}, Injective (integers_to_ring Z A) }.
