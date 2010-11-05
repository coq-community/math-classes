Require Import 
  Program Morphisms
  abstract_algebra interfaces.naturals interfaces.integers.

Class RingMinus R `{r : Ring R} := ring_minus_sig: ∀ x y : R, { z: R |  z = x + -y }.
Definition ring_minus `{RingMinus R} : R → R → R := λ x y, ` (ring_minus_sig x y).
Infix "-" := ring_minus.

Class FieldDiv R `{Field R} := field_div_sig: ∀ (x : R) (y : { x: R | x ≠ zero }), { z: R |  z = x * //y }.
Definition field_div `{FieldDiv R}: R → { x: R | x ≠ zero } → R := λ x y, ` (field_div_sig x y).
Infix "/" := field_div.

Inductive nat_pow_spec `{SemiRing A} `{Naturals B} : A → B → A → Prop := 
| nat_pow_spec_0 : `(nat_pow_spec x 0 1)
| nat_pow_spec_S : `(nat_pow_spec x n y → nat_pow_spec x (1 + n) (x * y))
| nat_pow_spec_proper': `(x1 = x2 → n1 = n2 → y1 = y2 → 
    nat_pow_spec x1 n1 y1 → nat_pow_spec x2 n2 y2). 

Class NatPow A B `{SemiRing A} `{Naturals B} := nat_pow_sig (x : A) (n : B) : { y | nat_pow_spec x n y }.
Definition nat_pow `{NatPow A B}: A → B → A := λ x n, ` (nat_pow_sig x n).
Infix "^" := nat_pow.

Class ShiftLeft A B `{SemiRing A} `{Naturals B} `{!NatPow A B} := shiftl_sig: ∀ (x : A) (y : B), 
  { z: A | z = x * 2 ^ y }.
Definition shiftl `{ShiftLeft A B}: A → B → A := λ x y, ` (shiftl_sig x y).
Infix "≪" := shiftl (at level 33, left associativity).

Class Log `(b : A) B `{SemiRing A} `{Order A} `{Naturals B} `{!NatPow A B} :=
  log_sig: ∀ (x : {z : A | 0 < z }), { z: B | b ^ z ≤ `x < b ^ (z + 1) }.
Definition log  `(b : A) `{Log A b N}: {z | 0 < z } → N := λ x, ` (log_sig x).

Section euclid.
  Context Z `{Integers Z}.
  
  (* Our abs operation is of type Z → N and therefore quite annoying for this definition *)
  Class Euclid a (b : { z : Z | z ≠ 0}) q r := 
    euclid : a = `b * q + r ∧ (0 ≤ r < `b ∨ `b < r ≤ 0).

  Class DivEuclid := div_euclid_sig (a : Z) (b : { z : Z | z ≠ 0}) : 
    { q : Z | ∃ r, Euclid a b q r }.
  Class ModEuclid := mod_euclid_sig (a : Z) (b : { z : Z | z ≠ 0}) : 
    { r : Z | ∃ q, Euclid a b q r }.
End euclid.

Definition div_euclid `{DivEuclid}: Z → { z : Z | z ≠ 0} → Z := λ x y, ` (div_euclid_sig Z x y).
Definition mod_euclid `{ModEuclid}: Z → { z : Z | z ≠ 0} → Z := λ x y, ` (mod_euclid_sig Z x y).