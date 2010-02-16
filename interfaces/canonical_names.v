Global Generalizable All Variables.
Set Automatic Introduction.

Require Import
 RelationClasses Relation_Definitions Morphisms Setoid.

(* Canonically named relations/operations/constants: *)
Class Decision P := decide: sumbool P (~ P).
Class Equiv A := equiv: relation A.
Class SemiGroupOp A := sg_op: A->A->A.
Class MonoidUnit A := mon_unit: A.
Class RingPlus A := ring_plus: A->A->A.
Class RingMult A := ring_mult: A->A->A.
Class RingOne A := ring_one: A.
Class RingZero A := ring_zero: A.
Class GroupInv A := group_inv: A -> A.
Class MultInv A `{Equiv A} `{RingZero A} := mult_inv: { x: A | ~ equiv x ring_zero } -> A.
Class Arrows (O: Type): Type := Arrow: O -> O -> Type.
Infix "-->" := Arrow.
Class CatId O `{Arrows O} := cat_id: forall {o}, o --> o.
Class CatComp O `{Arrows O} := comp: forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).
Class Order A := precedes: relation A.
Class RalgebraAction A B := ralgebra_action: A -> B -> B.

Implicit Arguments decide [[Decision]].

Instance: Params (@ring_mult) 2.
Instance: Params (@ring_plus) 2.
Instance: Params (@equiv) 2.

Instance ringplus_is_semigroupop `{f: RingPlus A}: SemiGroupOp A := f.
Instance ringmult_is_semigroupop `{f: RingMult A}: SemiGroupOp A := f.
Instance ringone_is_monoidunit `{c: RingOne A}: MonoidUnit A := c.
Instance ringzero_is_monoidunit `{c: RingZero A}: MonoidUnit A := c.

(* Notations: *)
Infix "==" := equiv (at level 70, no associativity).
Notation "0" := ring_zero.
Notation "1" := ring_one.
Infix "&" := sg_op (at level 50, left associativity).
Infix "+" := ring_plus.
Infix "*" := ring_mult.
Notation "- x" := (group_inv x).
Notation "// x" := (mult_inv x) (at level 35, right associativity).
Infix "<=" := precedes.

Program Definition dec_mult_inv `{e: Equiv A} `{RingZero A} `{!MultInv A}
  `{forall x y: A, Decision (x == y)} (x: A): A := if decide (x == 0) then 0 else // x.

Notation "/ x" := (dec_mult_inv x).

(* Common properties: *)
Class Commutative `{Equiv B} `(m: A -> A -> B): Prop := commutativity: forall x y, m x y == m y x.
Class Associative `{Equiv A} (m: A -> A -> A): Prop := associativity: forall x y z, m x (m y z) == m (m x y) z.
Class Injective `{ea: Equiv A} `{eb: Equiv B} (f: A -> B): Prop := injective: forall x y, f x == f y -> x == y.
Class Surjective {A} `{Equiv B} (f: A -> B): Prop := surjective: forall x: B, exists y, f y == x.
Class Bijective `{ea: Equiv A} `{eb: Equiv B} (f: A -> B): Prop :=
  { bijective_injective:> Injective f
  ; bijective_surjective:> Surjective f }.
Class AntiSymmetric `{ea: Equiv A} (R: relation A): Prop := antisymmetry: forall x y, R x y -> R y x -> x == y.
Class Distribute `{Equiv A} (f g: A->A->A): Prop :=
  { distribute_l: forall a b c, f a (g b c) == g (f a b) (f a c)
  ; distribute_r: forall a b c, f (g a b) c == g (f a c) (f b c) }.
Class HeteroSymmetric {A} {T: A -> A -> Type} (R: forall x y, T x y -> T y x -> Prop): Prop :=
  hetero_symmetric: forall x y (a: T x y) (b: T y x), R _ _ a b -> R _ _ b a.

Implicit Arguments injective [[A] [ea] [B] [eb] [Injective]].
Implicit Arguments antisymmetry [[A] [ea] [AntiSymmetric]].

(* Some things that hold in N, Z, Q, etc, and which we like to refer to by a common name: *)
Class ZeroProduct A `{Equiv A} `{!RingMult A} `{!RingZero A}: Prop :=
  zero_product: forall (x y: A), x * y == 0 -> x == 0 \/ y == 0.
Class ZeroNeOne A `{Equiv A} `{!RingOne A} `{!RingZero A}: Prop :=
  zero_ne_one: ~ 0 == 1.


Instance Injective_proper `{ea: Equiv A} `{eb: Equiv B} `{!Equivalence eb}:
  Proper (pointwise_relation A eb ==> iff) (@Injective A ea B eb).
Proof.
 intros x y E. unfold pointwise_relation in E.
 split; repeat intro. apply (injective x). do 2 rewrite E. assumption.
 apply (injective y). do 2 rewrite <- E. assumption.
Qed. (* Todo: Find a less awkward place for this. We probably need this for the other common properties, too. *)
