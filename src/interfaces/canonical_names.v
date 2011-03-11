Global Generalizable All Variables.
Global Set Automatic Introduction.

Require Import
 RelationClasses Relation_Definitions Morphisms Setoid Program.
Require Export Unicode.Utf8 Utf8_core.
Require Export workarounds.

(* Equality *)
Class Equiv A := equiv: relation A.

(* We use this virtually everywhere, and so use "=" for it: *)
Infix "=" := equiv: type_scope.
Notation "(=)" := equiv (only parsing).
Notation "( x =)" := (equiv x) (only parsing).
Notation "(= x )" := (λ y, equiv y x) (only parsing).
Notation "x ≠ y":= (¬x = y): type_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing).
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing).

(* Coq sometimes uses an incorrect DefaultRelation, so we override it. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (=) | 3.

(* For Leibniz equality we use "≡": *)
Infix "≡" := eq (at level 70, no associativity).
  (* Hm, we could define a very low priority Equiv instance for Leibniz equality.. *)

Definition ext_equiv `{Equiv A} `{Equiv B}: Equiv (A → B) := ((=) ==> (=))%signature.
Hint Extern 10 (Equiv (_ → _)) => apply @ext_equiv : typeclass_instances. 
Hint Extern 10 (Equiv (relation _)) => apply @ext_equiv : typeclass_instances. (* Due to bug #2491 *)

(** Interestingly, most of the development works fine if this is defined as
  ∀ x, f x = g x.
However, in the end that version was just not strong enough for comfortable rewriting
in setoid-pervasive contexts. *)

(* Other canonically named relations/operations/constants: *)
Class Decision P := decide: sumbool P (¬P).

Class SemiGroupOp A := sg_op: A → A → A.
Class MonoidUnit A := mon_unit: A.
Class RingPlus A := ring_plus: A → A → A.
Class RingMult A := ring_mult: A → A → A.
Class RingOne A := ring_one: A.
Class RingZero A := ring_zero: A.
Class GroupInv A := group_inv: A → A.
Definition NonZero R `{RingZero R} `{Equiv R} := sig (≠ ring_zero).
Class MultInv A `{Equiv A} `{RingZero A} := mult_inv: NonZero A → A.

Class Order A := precedes: relation A.
Definition strictly_precedes `{Equiv A} `{Order A} : Order A := λ (x y : A),  precedes x y ∧ x ≠ y.
Definition NonNeg R `{RingZero R} `{Order R} := sig (precedes ring_zero).
Definition Pos R `{RingZero R} `{Equiv R} `{Order R} := sig (strictly_precedes ring_zero).
Definition NonPos R `{RingZero R} `{Order R} := sig (λ y, precedes y ring_zero).

Class Arrows (O: Type): Type := Arrow: O → O → Type.
Infix "⟶" := Arrow (at level 90, right associativity).
Class CatId O `{Arrows O} := cat_id: `(x ⟶ x).
Class CatComp O `{Arrows O} := comp: ∀ x y z, (y ⟶ z) → (x ⟶ y) → (x ⟶ z).
Class RalgebraAction A B := ralgebra_action: A → B → B.
Class RingMultInverse {R} (x: R): Type := ring_mult_inverse: R.

Implicit Arguments ring_mult_inverse [[R] [RingMultInverse]].
Implicit Arguments cat_id [[O] [H] [CatId] [x]].
Implicit Arguments decide [[Decision]].
Implicit Arguments comp [[O] [H] [CatComp]].

Instance: Params (@ring_mult) 2.
Instance: Params (@ring_plus) 2.
Instance: Params (@equiv) 2.
Instance: Params (@precedes) 2.
Instance: Params (@strictly_precedes) 3.

Instance ringplus_is_semigroupop `{f: RingPlus A}: SemiGroupOp A := f.
Instance ringmult_is_semigroupop `{f: RingMult A}: SemiGroupOp A := f.
Instance ringone_is_monoidunit `{c: RingOne A}: MonoidUnit A := c.
Instance ringzero_is_monoidunit `{c: RingZero A}: MonoidUnit A := c.

Hint Extern 10 (Equiv (_ ⟶ _)) => apply @ext_equiv : typeclass_instances.

(* Notations: *)
Notation "R ₀" := (NonZero R) (at level 20, no associativity).
Notation "R ⁺" := (NonNeg R) (at level 20, no associativity).
Notation "R ₊" := (Pos R) (at level 20, no associativity).
Notation "R ⁻" := (NonPos R) (at level 20, no associativity).
Notation "x ↾ p" := (exist _ x p) (at level 20).

Infix "&" := sg_op (at level 50, left associativity).
Notation "(&)" := sg_op (only parsing).
Notation "( x &)" := (sg_op x) (only parsing).
Notation "(& x )" := (λ y, y & x) (only parsing).

Infix "+" := ring_plus.
Notation "(+)" := ring_plus (only parsing).
Notation "( x +)" := (ring_plus x) (only parsing).
Notation "(+ x )" := (λ y, y + x) (only parsing).

Infix "*" := ring_mult.
(* We don't add "( * )", "( * x )" and "( x * )" notations because they conflict with comments. *)
Notation "( x *.)" := (ring_mult x) (only parsing).
Notation "(.*.)" := ring_mult (only parsing).
Notation "(.* x )" := (λ y, y * x) (only parsing).

Notation "- x" := (group_inv x).
Notation "(-)" := group_inv (only parsing).
Notation "x - y" := (x + -y).

Notation "0" := ring_zero.
Notation "1" := ring_one.
Notation "2" := (1 + 1).
Notation "3" := (1 + (1 + 1)).
Notation "4" := (1 + (1 + (1 + 1))).
Notation "- 1" := (-(1)).
Notation "- 2" := (-(2)).
Notation "- 3" := (-(3)).
Notation "- 4" := (-(4)).

Notation "// x" := (mult_inv x) (at level 35, right associativity).
Notation "(//)" := mult_inv (only parsing).
Notation "x // y" := (x * //y) (at level 35, right associativity).

Infix "≤" := precedes.
Notation "(≤)" := precedes (only parsing).
Notation "( x ≤)" := (precedes x) (only parsing).
Notation "(≤ x )" := (λ y, y ≤ x) (only parsing).

Infix "<" := strictly_precedes.
Notation "(<)" := strictly_precedes (only parsing).
Notation "( x <)" := (strictly_precedes x) (only parsing).
Notation "(< x )" := (λ y, y < x) (only parsing).

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y /\ y < z) (at level 70, y at next level).
Notation "x < y < z" := (x < y /\ y < z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y /\ y ≤ z) (at level 70, y at next level).

Infix "◎" := (comp _ _ _) (at level 40, left associativity).
  (* Taking over ∘ is just a little too zealous at this point. With our current
   approach, it would require changing all (nondependent) function types A → B
   with A ⟶ B to make them use the canonical name for arrows, which is
   a tad extreme. *)
Notation "(◎)" := (comp _ _ _) (only parsing).
Notation "( f ◎)" := (comp _ _ _ f) (only parsing).
Notation "(◎ f )" := (λ g, comp _ _ _ g f) (only parsing).

(* Haskell style! *)
Notation "(→)" := (λ x y, x → y).

Class Coerce A B := coerce: A → B.
Notation "' x" := (coerce x) (at level 20).
Instance: Params (@coerce) 3.

(* Apartness *)
Class Apart A := apart: A → A → Type.
Instance default_apart `{Equiv A} : Apart A | 10 := λ x y, x ≠ y.
Notation "x >< y" := (apart x y) (at level 70, no associativity).
Instance: Params (@apart) 2.

(* Informative strict order (as we have on the reals in CoRN for example) *)
Class CSOrder A := cstrictly_precedes : A → A → Type.
Instance default_cstrictly_precedes `{Equiv A} `{Order A} : CSOrder A | 10 := strictly_precedes.
Notation "x ⋖ y" := (cstrictly_precedes x y) (at level 70, no associativity).
Instance: Params (@cstrictly_precedes) 2.

(* We define a division operation that yields zero for zero elements. A default 
    implementation for decidable fields can be found in theory.fields. *)
Class DecMultInv A `{Equiv A} `{RingZero A} `{RingOne A} `{RingMult A} 
  := dec_mult_inv_sig : ∀ x : A, {z | (x ≠ 0 → x * z = 1) ∧ (x = 0 → z = 0)}.
Definition dec_mult_inv `{DecMultInv A} : A → A := λ x, ` (dec_mult_inv_sig x).
Notation "/ x" := (dec_mult_inv x).
Notation "(/)" := dec_mult_inv (only parsing).
Notation "x / y" := (x * /y).
Instance: Params (@dec_mult_inv_sig) 6.
Instance: Params (@dec_mult_inv) 6.

Class Abs A `{Equiv A} `{Order A} `{RingZero A} `{GroupInv A} := abs_sig: ∀ (x : A), { y : A | (0 ≤ x → y = x) ∧ (x ≤ 0 → y = -x)}.
Definition abs `{Abs A} := λ x : A, ` (abs_sig x).
Instance: Params (@abs_sig) 6.
Instance: Params (@abs) 6.

(* Common properties: *)
Class Inverse `(A → B): Type := inverse: B → A.
Implicit Arguments inverse [[A] [B] [Inverse]].
Notation "f ⁻¹" := (inverse f) (at level 30).

Class LeftIdentity {A} `{Equiv B} (op: A → B → B) (x: A): Prop := left_identity: ∀ y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op: A → B → A) (y: B): Prop := right_identity: ∀ x, op x y = x.

Class LeftAbsorb `{Equiv A} {B} (op: A → B → A) (x: A): Prop := left_absorb: ∀ y, op x y = x.
Class RightAbsorb {A} `{Equiv B} (op: A → B → B) (y: B): Prop := right_absorb: ∀ x, op x y = y.
  (* hm, can we generate left/right instances from right/left+commutativity without causing loops? *)

Class LeftInverse {A} {B} `{Equiv C} (op: A → B → C) (inv: B → A) (unit: C) := left_inverse: ∀ x, op (inv x) x = unit.
Class RightInverse {A} {B} `{Equiv C} (op: A → B → C) (inv: A → B) (unit: C) := right_inverse: ∀ x, op x (inv x) = unit.

Class Commutative `{Equiv B} `(f: A → A → B): Prop := commutativity: `(f x y = f y x).

Class HeteroAssociative {A B C AB BC} `{Equiv ABC} 
     (fA_BC: A → BC → ABC) (fBC: B → C → BC) (fAB_C: AB → C → ABC) (fAB : A → B → AB): Prop
   := associativity : `(fA_BC x (fBC y z) = fAB_C (fAB x y) z).
Class Associative `{Equiv A} f := simple_associativity:> HeteroAssociative f f f f.
Notation ArrowsAssociative C := (∀ {w x y z: C}, HeteroAssociative (◎) (comp z _ _ ) (◎) (comp y x w)).

Class AntiSymmetric `{ea: Equiv A} (R: relation A): Prop := antisymmetry: `(R x y → R y x → x = y).
Implicit Arguments antisymmetry [[A] [ea] [AntiSymmetric]].

Class LeftHeteroDistribute {A B} `{Equiv C} (f: A → B → C) (g_r: B → B → B) (g: C → C → C): Prop 
  := distribute_l : `(f a (g_r b c) = g (f a b) (f a c)).
Class RightHeteroDistribute {A B} `{Equiv C} (f: A → B → C) (g_l: A → A → A) (g: C → C → C): Prop 
  := distribute_r: `(f (g_l a b) c = g (f a c) (f b c)).
Class Distribute `{Equiv A} (f g: A → A → A) : Prop := 
  { simple_distribute_l :> LeftHeteroDistribute f g g 
  ; simple_distribute_r :> RightHeteroDistribute f g g }.

Class HeteroSymmetric {A} {T: A → A → Type} (R: ∀ {x y}, T x y → T y x → Prop): Prop :=
  hetero_symmetric `(a: T x y) (b: T y x): R a b → R b a.

(* Some things that hold in N, Z, Q, etc, and which we like to refer to by a common name: *)
Class ZeroProduct A `{Equiv A} `{!RingMult A} `{!RingZero A}: Prop 
  := zero_product: `(x * y = 0 → x = 0 ∨ y = 0).

Class ZeroDivisor {R} `{Equiv R} `{RingZero R} `{RingMult R} (x: R): Prop
  := zero_divisor: x ≠ 0 ∧ ∃ y, y ≠ 0 ∧ x * y = 0.

Class NoZeroDivisors R `{Equiv R} `{RingZero R} `{RingMult R}: Prop
  := no_zero_divisors x: ¬ZeroDivisor x.

Instance zero_product_no_zero_divisors `{ZeroProduct A} : NoZeroDivisors A.
Proof. intros x [? [? [? E]]]. destruct (zero_product _ _ E); intuition. Qed.

Class RingUnit `{Equiv R} `{RingMult R} `{RingOne R} (x: R) `{!RingMultInverse x}: Prop
  := ring_unit_mult_inverse: x * ring_mult_inverse x = 1.
