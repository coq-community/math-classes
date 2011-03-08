Require Import 
  Morphisms abstract_algebra.

Class Pow A B := pow : A → B → A.
Infix "^" := pow.
Notation "(^)" := pow (only parsing).
Instance: Params (@pow) 3.

(* If we make [nat_pow_proper] a coercion, Coq is unable to find it. However, if we make a global instance in theory.nat_pow, it works? *)
Class NatPowSpec A B (pw : Pow A B) `{eA : Equiv A} `{eB : Equiv B} `{RingOne A} `{RingMult A} `{RingZero B} `{RingOne B} `{RingPlus B} := {
  nat_pow_proper : Proper ((=) ==> (=) ==> (=)) (^) ; 
  nat_pow_0 : ∀ x, x ^ 0 = 1 ;
  nat_pow_S : ∀ x n, x ^ (1 + n) = x * x ^ n
}.

Class IntPowSpec A B (pow : Pow A B) `{Equiv A} `{Equiv B} `{RingZero A} `{RingOne A} `{RingMult A} `{RingZero B} `{RingOne B} `{RingPlus B} := {
  int_pow_proper : Proper ((=) ==> (=) ==> (=)) (^) ;
  int_pow_0 : ∀ x, x ^ 0 = 1 ;
  int_pow_base_0 : ∀ (n : B), n ≠ 0 → 0 ^ n = 0 ;
  int_pow_S : ∀ x n, x ≠ 0 → x ^ (1 + n) = x * x ^ n
}.

Class ShiftL A B := shiftl: A → B → A.
Infix "≪" := shiftl (at level 33, left associativity).
Notation "(≪)" := shiftl (only parsing).
Instance: Params (@shiftl) 3.

Class ShiftLSpec A B (sl : ShiftL A B) `{Equiv A} `{Equiv B} `{RingOne A} `{RingPlus A} `{RingMult A} `{RingZero B} `{RingOne B} `{RingPlus B} := {
  shiftl_proper : Proper ((=) ==> (=) ==> (=)) (≪) ;
  shiftl_0 :> RightIdentity (≪) 0 ;
  shiftl_S : ∀ x n, x ≪ (1 + n) = 2 * x ≪ n
}.

Class ShiftR A B := shiftr: A → B → A.
Infix "≫" := shiftr (at level 33, left associativity).
Notation "(≫)" := shiftr (only parsing).
Instance: Params (@shiftr) 3.

Class ShiftRSpec A B (sl : ShiftR A B) `{Equiv A} `{Equiv B} `{RingOne A} `{RingPlus A} `{RingMult A} `{RingZero B} `{RingOne B} `{RingPlus B} := {
  shiftr_proper : Proper ((=) ==> (=) ==> (=)) (≫) ;
  shiftr_0 :> RightIdentity (≫) 0 ;
  shiftr_S : ∀ x n, x ≫ n = 2 * x ≫ (1 + n) ∨ x ≫ n = 2 * x ≫ (1 + n) + 1
}.

Class DivEuclid A := div_euclid : A → A → A.
Class ModEuclid A := mod_euclid : A → A → A.
Infix "`div`" := div_euclid (at level 30).
Infix "`mod`" := mod_euclid (at level 30).
Instance: Params (@div_euclid) 2.
Instance: Params (@mod_euclid) 2.

Class EuclidSpec A (d : DivEuclid A) (m : ModEuclid A) `{Equiv A} `{Order A} `{RingZero A} `{RingPlus A} `{RingMult A} := {
  div_euclid_proper : Proper ((=) ==> (=) ==> (=)) div_euclid ;
  mod_euclid_proper : Proper ((=) ==> (=) ==> (=)) mod_euclid ;
  div_mod : ∀ x y, y ≠ 0 → x = y * x `div` y + x `mod` y ;
  mod_euclid_rem : ∀ x y, y ≠ 0 → 0 ≤ x `mod` y < y ∨ y < x `mod` y ≤ 0 ;
  div_euclid_0 : ∀ x, x `div` 0 = 0 ;
  mod_euclid_0 : ∀ x, x `mod` 0 = 0
}.

Class CutMinus A := cut_minus : A → A → A.
Infix "∸" := cut_minus (at level 50, left associativity).
Notation "(∸)" := cut_minus (only parsing).
Instance: Params (@cut_minus) 2.

Class CutMinusSpec A (cm : CutMinus A) `{Equiv A} `{RingZero A} `{RingPlus A} `{Order A} := {
  cut_minus_precedes : ∀ x y, y ≤ x → cut_minus x y + y = x ;
  cut_minus_0 : ∀ x y, x ≤ y → cut_minus x y = 0
}.
