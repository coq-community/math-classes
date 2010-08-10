Require theory.integers.
Require Import interfaces.rationals interfaces.integers abstract_algebra field_of_fractions.

Instance intfrac_rationals
  Z `{Zth: Integers Z} `{∀ x y: Z, Decision (x = y)} `{∀ x y: Z, Decision (x <= y)}: Rationals (Frac Z).
Proof. apply (alt_Build_Rationals _ _ _ _ _). Qed.
