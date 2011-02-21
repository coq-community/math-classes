Require Import
  abstract_algebra interfaces.integers field_of_fractions theory.integers.

Section rationals_to_frac.
  Context (A : Type).
  Class RationalsToFrac := rationals_to_frac : ∀ B `{Integers B}, A → Frac B.
End rationals_to_frac.

Class Rationals A {e plus mult zero one opp inv} `{U : !RationalsToFrac A} : Prop :=
  { rationals_field:> @Field A e plus mult zero one opp inv
  ; rationals_frac :> ∀ `{Integers Z}, Injective (rationals_to_frac A Z)
  ; rationals_frac_mor :> ∀ `{Integers Z}, SemiRing_Morphism (rationals_to_frac A Z)
  ; rationals_embed_ints :> ∀ `{Integers Z}, Injective (integers_to_ring Z A) }.
