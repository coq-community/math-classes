Require theory.integers.
Require Import 
  interfaces.rationals interfaces.integers 
  abstract_algebra field_of_fractions theory.rationals.

Instance intfrac_rationals `{Integers Z} `{∀ x y: Z, Decision (x = y)} : Rationals (Frac Z).
Proof alt_Build_Rationals _.
