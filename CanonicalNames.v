Global Generalizable All Variables.
Require Import RelationClasses Relation_Definitions Morphisms Setoid.

Class Decision (T: Prop) := decide: sumbool T (T -> False).

Implicit Arguments decide [[Decision]].

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
Class Order A := precedes: relation A.
Class RalgebraAction A B := ralgebra_action: A -> B -> B.

Instance: Params (@ring_mult) 2.
Instance: Params (@ring_plus) 2.
Instance: Params (@equiv) 2.

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
Global Infix "<=" := precedes.

(* typical properties: *)
Class Commutative `{Equiv B} `(m: A -> A -> B): Prop := commutativity: forall x y, m x y == m y x.
Class Associative `{Equiv A} (m: A -> A -> A): Prop := associativity: forall x y z, m x (m y z) == m (m x y) z.
Class Injective `{ea: Equiv A} `{eb: Equiv B} (f: A -> B): Prop := injective: forall x y, f x == f y -> x == y.
Class Surjective {A} `{Equiv B} (f: A -> B): Prop := surjective: forall x: B, exists y, f y == x.
Class AntiSymmetric `{Equiv A} (R: relation A): Prop := antisymmetry: forall x y, R x y -> R y x -> x == y.
Class Distribute `{Equiv A} (f g: A->A->A): Prop :=
  { distribute_l: forall a b c, f a (g b c) == g (f a b) (f a c)
  ; distribute_r: forall a b c, f (g a b) c == g (f a c) (f b c) }.

Implicit Arguments injective [[A] [ea] [B] [eb] [Injective]].

Class ZeroProduct A `{Equiv A} `{!RingMult A} `{!RingZero A}: Prop :=
  zero_product: forall (x y: A), x * y == 0 -> x == 0 \/ y == 0.
    (* holds in N, Z, Q.. *)

Class ZeroNeOne A `{Equiv A} `{!RingOne A} `{!RingZero A}: Prop :=
  zero_ne_one: ~ 0 == 1.
