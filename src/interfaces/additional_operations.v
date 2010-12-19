Require Import 
  Program Morphisms abstract_algebra.

Class Pow A B := pow: A → B → A.
Infix "^" := pow.
Notation "(^)" := pow (only parsing).
Instance: Params (@pow) 3.

Inductive nat_pow_spec `{Equiv A} `{Equiv B} `{RingOne A} `{RingMult A} `{RingZero B} 
    `{RingOne B} `{RingPlus B} : A → B → A → Prop := 
| nat_pow_spec_0 : `(nat_pow_spec x 0 1)
| nat_pow_spec_S : `(nat_pow_spec x n y → nat_pow_spec x (1 + n) (x * y))
| nat_pow_spec_proper': `(x1 = x2 → n1 = n2 → y1 = y2 → 
    nat_pow_spec x1 n1 y1 → nat_pow_spec x2 n2 y2). 

Class NatPow A B `{Equiv A} `{Equiv B} `{RingOne A} `{RingMult A} `{RingZero B} 
    `{RingOne B} `{RingPlus B} := nat_pow_sig (x : A) (n : B) : { y | nat_pow_spec x n y }.
Instance nat_pow `{NatPow A B} : `{Pow A B} := λ x n, ` (nat_pow_sig x n).
Instance: Params (@nat_pow_sig) 10.
Instance: Params (@nat_pow) 10.

(*
(* [0 ^ x] for a negative [x] is not defined. However, we take the easy way and let it yield [0]. *)
Class IntPow A B `{OrdField A} `{!DecMultInv A} `{Integers B} := 
  int_pow_sig (x : A) (n : B) : { y | (0 ≤ n → nat_pow_spec x n y) ∧ (n < 0 → nat_pow_spec x (-n) (/ y)) }.
Instance int_pow `{IntPow A B} : `{Pow A B} := λ x n, ` (int_pow_sig x n).
*)

Class ShiftLeft A B `{NatPow A B} `{RingPlus A} := shiftl_sig: ∀ (x : A) (y : B), 
  { z: A | z = x * 2 ^ y }.
Definition shiftl `{ShiftLeft A B}: A → B → A := λ x y, ` (shiftl_sig x y).
Infix "≪" := shiftl (at level 33, left associativity).
Notation "(≪)" := shiftl (only parsing).
Instance: Params (@shiftl_sig) 12.
Instance: Params (@shiftl) 12.

Class Log `(b : A) B  `{NatPow A B} `{RingZero A} `{RingPlus A} `{Order A} :=
  log_sig: ∀ (x : {z : A | 0 < z }), { z: B | b ^ z ≤ `x < b ^ (z + 1) }.
Definition log  `(b : A) `{Log A b N}: {z | 0 < z } → N := λ x, ` (log_sig x).
Instance: Params (@log_sig) 15.
Instance: Params (@log) 15.

(* Our abs operation is of type [Z → N] and therefore quite annoying for this definition *)
Class Euclid `{Equiv A} `{RingZero A} `{RingPlus A} `{RingMult A} `{Order A} a (b : { z : A | z ≠ 0}) q r := 
  euclid : a = `b * q + r ∧ (0 ≤ r < `b ∨ `b < r ≤ 0).

Class DivEuclid A `{Equiv A} `{RingZero A} `{RingPlus A} `{RingMult A} `{Order A} := div_euclid_sig (a : A) (b : { z : A | z ≠ 0}) : 
  { q : A | ∃ r, Euclid a b q r }.
Class ModEuclid A `{Equiv A} `{RingZero A} `{RingPlus A} `{RingMult A} `{Order A} := mod_euclid_sig (a : A) (b : { z : A | z ≠ 0}) : 
  { r : A | ∃ q, Euclid a b q r }.

Definition div_euclid `{DivEuclid A}: A → { z : A | z ≠ 0} → A := λ x y, ` (div_euclid_sig x y).
Instance: Params (@div_euclid_sig) 7.
Instance: Params (@div_euclid) 7.

Definition mod_euclid `{ModEuclid A}: A → { z : A | z ≠ 0} → A := λ x y, ` (mod_euclid_sig x y).
Instance: Params (@mod_euclid_sig) 7.
Instance: Params (@mod_euclid) 7.

Class ShiftRight A B `{NatPow A B} `{RingPlus A} `{Order A}
  := shiftr_sig: ∀ (x : A) (y : B), { z: A | x ≤ z * 2 ^ y < 2 * x }.

Definition shiftr `{ShiftRight A B}: A → B → A := λ x y, proj1_sig (shiftr_sig x y).
Infix "≫" := shiftr (at level 33, left associativity).
Notation "(≫)" := shiftr (only parsing).
Instance: Params (@shiftr_sig) 13.
Instance: Params (@shiftr) 13.

Class CutMinus A `{Equiv A} `{RingZero A} `{RingPlus A} `{Order A} := 
  cut_minus_sig: ∀ (x y : A), { z: A | (y < x → z + y = x) ∧ (x ≤ y → z =0) }.
Definition cut_minus `{m : CutMinus A} : A → A → A := λ x y, ` (cut_minus_sig x y).
Infix "∸" := cut_minus (at level 50, left associativity).
Notation "(∸)" := cut_minus (only parsing).
Instance: Params (@cut_minus_sig) 6.
Instance: Params (@cut_minus) 6.
