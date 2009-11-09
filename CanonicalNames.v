Require Import Relation_Definitions.

Definition decision T := sumbool T (T -> False).
Class Decidable `(r: relation A): Type := decide: forall x y : A, decision (r x y).

(* canonically named relations/operations/constants: *)
Class Equiv A := equiv: relation A.
Class SemiGroupOp A := sg_op: A->A->A.
Class MonoidUnit A := mon_unit: A.
Class RingPlus A := ring_plus: A->A->A.
Class RingMult A := ring_mult: A->A->A.
Class RingOne A := ring_one: A.
Class RingZero A := ring_zero: A.
Class GroupInv A := group_inv: A -> A.
Class MultInv A `{Equiv A} `{RingZero A} := mult_inv: { x: A | ~ equiv x ring_zero } -> A.
Class CatId O (A:O->O->Type) := cat_id: forall {o}, A o o.
Class CatComp O (A:O->O->Type) := comp: forall {x y z}, A y z -> A x y -> A x z.

Instance ringplus_is_semigroupop `{f: RingPlus A}: SemiGroupOp A := f.
Instance ringmult_is_semigroupop `{f: RingMult A}: SemiGroupOp A := f.
Instance ringone_is_monoidunit `{c: RingOne A}: MonoidUnit A := c.
Instance ringzero_is_monoidunit `{c: RingZero A}: MonoidUnit A := c.

(* notations: *)
Global Infix "==" := equiv (at level 70, no associativity).
Global Notation "0" := ring_zero.
Global Notation "1" := ring_one.
Global Infix "&" := sg_op (at level 50, left associativity).
Global Infix "+" := ring_plus.
Global Infix "*" := ring_mult.
Global Notation "- x" := (group_inv x).
Global Notation "// x" := (mult_inv x) (at level 35, right associativity).
  (* The "/ x" notation is introduced later for contexts with decidable equality where
   we can do away with the nonzero proof. *)

(* typical properties: *)
Class Commutative `{Equiv B} `(m: A -> A -> B) := commutativity: forall x y, m x y == m y x.
Class Associative `{Equiv A} (m: A -> A -> A) := associativity: forall x y z, m x (m y z) == m (m x y) z.
Class Distribute `{Equiv A} (f g: A->A->A) :=
  { distribute_l: forall a b c, f a (g b c) == g (f a b) (f a c)
  ; distribute_r: forall a b c, f (g a b) c == g (f a c) (f b c) }.
