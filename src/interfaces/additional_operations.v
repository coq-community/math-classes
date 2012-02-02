Require Import
  Morphisms abstract_algebra.

Class Pow A B := pow : A → B → A.
Infix "^" := pow : mc_scope.
Notation "(^)" := pow (only parsing) : mc_scope.
Notation "( x ^)" := (pow x) (only parsing) : mc_scope.
Notation "(^ n )" := (λ x, x ^ n) (only parsing) : mc_scope.
Instance: Params (@pow) 3.

(* If we make [nat_pow_proper] a subclass, Coq is unable to find it.
However, if we make a global instance in theory.nat_pow, it works? *)
Class NatPowSpec A B (pw : Pow A B) `{Equiv A} `{Equiv B} `{One A} `{Mult A} `{Zero B} `{One B} `{Plus B} := {
  nat_pow_proper : Proper ((=) ==> (=) ==> (=)) (^) ;
  nat_pow_0 : ∀ x, x ^ 0 = 1 ;
  nat_pow_S : ∀ x n, x ^ (1 + n) = x * x ^ n
}.

Class IntPowSpec A B (pow : Pow A B) `{Equiv A} `{Equiv B} `{Zero A} `{One A} `{Mult A} `{Zero B} `{One B} `{Plus B} := {
  int_pow_proper : Proper ((=) ==> (=) ==> (=)) (^) ;
  int_pow_0 : ∀ x, x ^ 0 = 1 ;
  int_pow_base_0 : ∀ (n : B), n ≠ 0 → 0 ^ n = 0 ;
  int_pow_S : ∀ x n, x ≠ 0 → x ^ (1 + n) = x * x ^ n
}.

Class ShiftL A B := shiftl: A → B → A.
Infix "≪" := shiftl (at level 33, left associativity) : mc_scope.
Notation "(≪)" := shiftl (only parsing) : mc_scope.
Notation "( x ≪)" := (shiftl x) (only parsing) : mc_scope.
Notation "(≪ n )" := (λ x, x ≪ n) (only parsing) : mc_scope.
Instance: Params (@shiftl) 3.

Class ShiftLSpec A B (sl : ShiftL A B) `{Equiv A} `{Equiv B} `{One A} `{Plus A} `{Mult A} `{Zero B} `{One B} `{Plus B} := {
  shiftl_proper : Proper ((=) ==> (=) ==> (=)) (≪) ;
  shiftl_0 :> RightIdentity (≪) 0 ;
  shiftl_S : ∀ x n, x ≪ (1 + n) = 2 * x ≪ n
}.

Lemma shiftl_spec_from_nat_pow `{SemiRing A} `{SemiRing B} `{!NatPowSpec A B pw} (sl : ShiftL A B) :
  (∀ x n, x ≪ n = x * 2 ^ n) → ShiftLSpec A B sl.
Proof.
  pose proof nat_pow_proper.
  intros spec. split.
    intros ? ? E1 ? ? E2.
    rewrite 2!spec.
    now rewrite E1, E2.
   intro x. rewrite spec, nat_pow_0. now apply right_identity.
  intros x n. rewrite 2!spec. rewrite nat_pow_S.
  now rewrite ?associativity, (commutativity x 2).
Qed.

Lemma shiftl_spec_from_int_pow `{SemiRing A} `{!PropHolds ((2:A) ≠ 0)} `{SemiRing B} `{!IntPowSpec A B ip} (sl : ShiftL A B) :
  (∀ x n, x ≪ n = x * 2 ^ n) → ShiftLSpec A B sl.
Proof.
  pose proof int_pow_proper.
  intros spec. split.
    intros ? ? E1 ? ? E2.
    rewrite 2!spec. now rewrite E1, E2.
   intro x. rewrite spec, int_pow_0. now apply right_identity.
  intros x n. rewrite 2!spec. rewrite int_pow_S by solve_propholds.
  now rewrite ?associativity, (commutativity x 2).
Qed.

Class ShiftR A B := shiftr: A → B → A.
Infix "≫" := shiftr (at level 33, left associativity) : mc_scope.
Notation "(≫)" := shiftr (only parsing) : mc_scope.
Instance: Params (@shiftr) 3.

Class ShiftRSpec A B (sl : ShiftR A B) `{Equiv A} `{Equiv B} `{One A} `{Plus A} `{Mult A} `{Zero B} `{One B} `{Plus B} := {
  shiftr_proper : Proper ((=) ==> (=) ==> (=)) (≫) ;
  shiftr_0 :> RightIdentity (≫) 0 ;
  shiftr_S : ∀ x n, x ≫ n = 2 * x ≫ (1 + n) ∨ x ≫ n = 2 * x ≫ (1 + n) + 1
}.

Class DivEuclid A := div_euclid : A → A → A.
Class ModEuclid A := mod_euclid : A → A → A.
Infix "`div`" := div_euclid (at level 35) : mc_scope.
Notation "(`div`)" := div_euclid (only parsing) : mc_scope.
Notation "( x `div`)" := (div_euclid x) (only parsing) : mc_scope.
Notation "(`div` y )" := (λ x, x `div` y) (only parsing) : mc_scope.
Infix "`mod`" := mod_euclid (at level 40) : mc_scope.
Notation "(`mod` )" := mod_euclid (only parsing) : mc_scope.
Notation "( x `mod`)" := (mod_euclid x) (only parsing) : mc_scope.
Notation "(`mod` y )" := (λ x, x `mod` y) (only parsing) : mc_scope.
Instance: Params (@div_euclid) 2.
Instance: Params (@mod_euclid) 2.

Class EuclidSpec A (d : DivEuclid A) (m : ModEuclid A) `{Equiv A} `{Le A} `{Lt A} `{Zero A} `{Plus A} `{Mult A} := {
  div_proper : Proper ((=) ==> (=) ==> (=)) (`div`) ;
  mod_proper : Proper ((=) ==> (=) ==> (=)) (`mod`) ;
  div_mod : ∀ x y, y ≠ 0 → x = y * x `div` y + x `mod` y ;
  mod_rem : ∀ x y, y ≠ 0 → 0 ≤ x `mod` y < y ∨ y < x `mod` y ≤ 0 ;
  div_0 : ∀ x, x `div` 0 = 0 ;
  mod_0 : ∀ x, x `mod` 0 = 0
}.

Class CutMinus A := cut_minus : A → A → A.
Infix "∸" := cut_minus (at level 50, left associativity) : mc_scope.
Notation "(∸)" := cut_minus (only parsing) : mc_scope.
Notation "( x ∸)" := (cut_minus x) (only parsing) : mc_scope.
Notation "(∸ y )" := (λ x, x ∸ y) (only parsing) : mc_scope.
Instance: Params (@cut_minus) 2.

Class CutMinusSpec A (cm : CutMinus A) `{Equiv A} `{Zero A} `{Plus A} `{Le A} := {
  cut_minus_le : ∀ x y, y ≤ x → x ∸ y + y = x ;
  cut_minus_0 : ∀ x y, x ≤ y → x ∸ y = 0
}.
