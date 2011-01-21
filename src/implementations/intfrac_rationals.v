Require theory.integers.
Require Import 
  interfaces.rationals interfaces.integers 
  abstract_algebra field_of_fractions theory.rationals.

Instance intfrac_rationals `{Integers Z} `{∀ x y: Z, Decision (x = y)} : Rationals (Frac Z).
Proof. apply (alt_Build_Rationals _ _ _ _ _). Qed.
