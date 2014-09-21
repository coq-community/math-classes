Require Import
  interfaces.rationals interfaces.integers
  abstract_algebra theory.rationals.
Require Export
  field_of_fractions.

Section intfrac_rationals.
  Context `{Integers Z}.

  Global Instance: RationalsToFrac (Frac Z) := alt_to_frac id.
  Global Instance: Rationals (Frac Z) := alt_Build_Rationals id (cast Z (Frac Z)).
End intfrac_rationals.
