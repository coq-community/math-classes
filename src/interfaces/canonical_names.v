Global Generalizable All Variables.
Set Automatic Introduction.

Set Automatic Coercions Import.
  (* Needed to recover old behavior. Todo: Figure out why the behavior was changed; what was wrong with it? *)

Require Import
 RelationClasses Relation_Definitions Morphisms Setoid Program.
Require Export Unicode.Utf8 Utf8_core.

(* Equality *)
Class Equiv A := equiv: relation A.

(* We use this virtually everywhere, and so use "=" for it: *)
Infix "=" := equiv: type_scope.
Notation "(=)" := equiv (only parsing).
Notation "( f =)" := (equiv f) (only parsing).
Notation "(= f )" := (λ g, equiv g f) (only parsing).
Notation "x ≠ y":= (~ equiv x y): type_scope.

(* For Leibniz equality we use "≡": *)
Infix "≡" := eq (at level 70, no associativity).
  (* Hm, we could define a very low priority Equiv instance for Leibniz equality.. *)

Instance ext_eq (A B: Type) `(Equiv B): Equiv (A → B)
  := λ f g: A → B, ∀ x, f x = g x.

(* Other canonically named relations/operations/constants: *)
Class Decision P := decide: sumbool P (~ P).
Class SemiGroupOp A := sg_op: A → A → A.
Class MonoidUnit A := mon_unit: A.
Class RingPlus A := ring_plus: A → A → A.
Class RingMult A := ring_mult: A → A → A.
Class RingOne A := ring_one: A.
Definition ring_two `{RingOne A} `{RingPlus A} := ring_plus ring_one ring_one.
Class RingZero A := ring_zero: A.
Class GroupInv A := group_inv: A → A.
Class MultInv A `{Equiv A} `{RingZero A} := mult_inv: { x: A | x ≠ ring_zero } → A.
Class Arrows (O: Type): Type := Arrow: O → O → Type.
Infix "⟶" := Arrow (at level 90, right associativity).
Class CatId O `{Arrows O} := cat_id: `(x ⟶ x).
Class CatComp O `{Arrows O} := comp: ∀ {x y z}, (y ⟶ z) → (x ⟶ y) → (x ⟶ z).
Class Order A := precedes: relation A.
Definition precedes_neq `{Equiv A} `{Order A} : Order A := λ (x y : A),  precedes x y ∧ x ≠ y.
Class RalgebraAction A B := ralgebra_action: A → B → B.
Class RingMultInverse {R} (x: R): Type := ring_mult_inverse: R.
Implicit Arguments ring_mult_inverse [[R] [RingMultInverse]].
Implicit Arguments cat_id [[O] [H] [CatId] [x]].
Implicit Arguments decide [[Decision]].

Instance: Params (@precedes) 2.
Instance: Params (@precedes_neq) 3.
Instance: Params (@ring_mult) 2.
Instance: Params (@ring_plus) 2.
Instance: Params (@equiv) 2.

Instance ringplus_is_semigroupop `{f: RingPlus A}: SemiGroupOp A := f.
Instance ringmult_is_semigroupop `{f: RingMult A}: SemiGroupOp A := f.
Instance ringone_is_monoidunit `{c: RingOne A}: MonoidUnit A := c.
Instance ringzero_is_monoidunit `{c: RingZero A}: MonoidUnit A := c.

(* Notations: *)
Notation "0" := ring_zero.
Notation "1" := ring_one.
Notation "2" := ring_two.
Infix "&" := sg_op (at level 50, left associativity).
Infix "+" := ring_plus.
Notation "(+)" := ring_plus (only parsing).
Notation "( x +)" := (ring_plus x) (only parsing).
Notation "(+ x )" := (λ y, ring_plus y x) (only parsing).
Infix "*" := ring_mult.
Notation "( x *)" := (ring_mult x) (only parsing).
  (* We don't add "(*)" and "(*x)" notations because they're too much like comments. *)
Notation "- x" := (group_inv x).
Notation "// x" := (mult_inv x) (at level 35, right associativity).
Infix "≤" := precedes.
Notation "(≤)" := precedes (only parsing).
Infix "<" := precedes_neq.
Notation "(<)" := precedes_neq (only parsing).
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y /\ y < z) (at level 70, y at next level).
Notation "x < y < z" := (x < y /\ y < z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y /\ y ≤ z) (at level 70, y at next level).
Notation "x ⁻¹" := (ring_mult_inverse x) (at level 30).
Infix "◎" := comp (at level 40, left associativity).
  (* Taking over ∘ is just a little too zealous at this point. With our current
   approach, it would require changing all (nondependent) function types A → B
   with A ⟶ B to make them use the canonical name for arrows, which is
   a tad extreme. *)
Notation "(◎)" := comp (only parsing).
Notation "( f ◎)" := (comp f) (only parsing).
Notation "(◎ f )" := (λ g, comp g f) (only parsing).
  (* Haskell style! *)

Notation "(→)" := (λ x y, x → y).

Program Definition dec_mult_inv `{e: Equiv A} `{RingZero A} `{!MultInv A}
  `{∀ x y: A, Decision (equiv x y)} (x: A): A := if decide (equiv x 0) then 0 else // x.

Notation "/ x" := (dec_mult_inv x).

Class RingMinus A `{Equiv A} `{RingPlus A} `{GroupInv A} := ring_minus_sig: ∀ x y : A, { z: A |  z = x + -y }.
Definition ring_minus `{RingMinus A} : A → A → A := λ x y, ` (ring_minus_sig x y).
Infix "-" := ring_minus.
Instance: Params (@ring_minus) 2.

Class FieldDiv A `{RingMult A} `{MultInv A} `{RingZero A} := field_div_sig: ∀ (x : A) (y : { x: A | x ≠ 0 }), { z: A |  z = x * //y }.
Definition field_div `{FieldDiv A}: A → { x: A | x ≠ 0 } → A := λ x y, ` (field_div_sig x y).
Infix "//" := field_div (at level 35, right associativity).
Instance: Params (@field_div) 2.

(* Common properties: *)
Class Commutative `{Equiv B} `(m: A → A → B): Prop := commutativity: `(m x y = m y x).
Class Associative `{Equiv A} (m: A → A → A): Prop := associativity: `(m x (m y z) = m (m x y) z).
Class Inverse `(A → B): Type := inverse: B → A.
Class AntiSymmetric `{ea: Equiv A} (R: relation A): Prop := antisymmetry: `(R x y → R y x → x = y).
Class Distribute `{Equiv A} (f g: A → A → A): Prop :=
  { distribute_l: `(f a (g b c) = g (f a b) (f a c))
  ; distribute_r: `(f (g a b) c = g (f a c) (f b c)) }.
Class HeteroSymmetric {A} {T: A → A → Type} (R: ∀ {x y}, T x y → T y x → Prop): Prop :=
  hetero_symmetric `(a: T x y) (b: T y x): R _ _ a b → R _ _ b a.

Implicit Arguments inverse [[A] [B] [Inverse]].
Implicit Arguments antisymmetry [[A] [ea] [AntiSymmetric]].

(* Some things that hold in N, Z, Q, etc, and which we like to refer to by a common name: *)
Class ZeroProduct A `{Equiv A} `{!RingMult A} `{!RingZero A}: Prop :=
  zero_product: `(x * y = 0 → x = 0 ∨ y = 0).
Class ZeroNeOne A `{Equiv A} `{!RingOne A} `{!RingZero A}: Prop :=
  zero_ne_one: 0 ≠ 1.
Class ZeroNeTwo A `{Equiv A} `{!RingOne A} `{!RingPlus A} `{!RingZero A}: Prop :=
  zero_ne_two: 0 ≠ 2.
    (* todo: this is silly *)

Class ZeroDivisor {R} `{Equiv R} `{RingZero R} `{RingMult R} (x: R): Prop
  := zero_divisor: x ≠ 0 ∧ ∃ y, y ≠ 0 ∧ x * y = 0.

Class NoZeroDivisors R `{Equiv R} `{RingZero R} `{RingMult R}: Prop
  := no_zero_divisors x: ¬ ZeroDivisor x.

Class RingUnit {R} `{Equiv R} `{RingMult R} `{RingOne R} (x: R) `{!RingMultInverse x}: Prop
  := ring_unit_mult_inverse: x * x⁻¹ = 1.