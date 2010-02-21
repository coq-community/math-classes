Require
 Equivalence.
Require Import
 Morphisms Setoid Program.
Require Export
 canonical_names util.

Class Setoid A {e: Equiv A} := setoid_eq:> Equivalence (@equiv A e).

Class SemiGroup A {e: Equiv A} {op: SemiGroupOp A} :=
  { sg_setoid:> Setoid A
  ; sg_ass:> Associative sg_op
  ; sg_mor:> Proper (e ==> e ==> e)%signature sg_op }.

Class Monoid A `{Equiv A} {op: SemiGroupOp A} {unit: MonoidUnit A} :=
  { monoid_semigroup:> SemiGroup A
  ; monoid_lunit: `(mon_unit & x = x)
  ; monoid_runit: `(x & mon_unit = x) }.

Class Group A {e: Equiv A} {op: SemiGroupOp A} {unit: MonoidUnit A} {inv: GroupInv A}: Prop :=
  { group_monoid:> Monoid A
  ; inv_proper:> Proper (e ==> e) inv
  ; inv_l: `(- x & x = mon_unit)
  ; inv_r: `(x & - x = mon_unit) }.

Class AbGroup A `{Equiv A} {op unit inv}: Prop :=
  { abgroup_group:> @Group A _ op unit inv
  ; abgroup_commutative:> Commutative op }.

Class SemiRing A {e: Equiv A} {plus: RingPlus A} {mult: RingMult A} {zero: RingZero A} {one: RingOne A}: Prop :=
  { semiring_mult_monoid:> Monoid A (op:=mult) (unit:=one)
  ; semiring_plus_monoid:> Monoid A (op:=plus) (unit:=zero)
  ; semiring_plus_comm:> Commutative plus
  ; semiring_mult_comm:> Commutative mult
  ; semiring_distr:> Distribute mult plus
  ; mult_0_l: `(0 * x = 0) }.

Class Ring A {e: Equiv A} {plus: RingPlus A} {mult: RingMult A} {inv: GroupInv A} {zero: RingZero A} {one: RingOne A}: Prop :=
  { ring_group:> AbGroup A (op:=plus) (unit:=zero)
  ; ring_monoid:> Monoid A (op:=mult) (unit:=one)
  ; ring_mult_comm:> Commutative mult
  ; ring_dist:> Distribute mult plus }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
   require commutative multiplication. *)

Class Field A {e: Equiv A} {plus mult inv zero one} {mult_inv: MultInv A}: Prop :=
  { field_ring:> @Ring A e plus mult inv zero one
  ; field_0neq1:> ZeroNeOne A
  ; mult_inv_proper:> Proper (sig_relation equiv _ ==> equiv) mult_inv
  ; mult_inverse: `(` x * // x = 1) }.

Class PartialOrder `{e: Equiv A} (R: Order A): Prop :=
  { equ:> Equivalence e
  ; partialorder_proper:> Proper (e ==> e ==> iff) R
  ; partial_preorder:> PreOrder R
  ; partial_antisym:> AntiSymmetric R }.

Class TotalOrder `(Order A): Prop := total_order: Π x y: A, x <= y ∨ y <= x.

Class RingOrder `(e: Equiv A) (plus: RingPlus A) (mult: RingMult A) (zero: RingZero A) (leq: Order A) :=
  { ringorder_partialorder:> PartialOrder leq
  ; ringorder_plus: `(leq x y → (Π z, leq (x + z) (y + z)))
  ; ringorder_mult: `(leq zero x → (Π y, leq 0 y → leq 0 (x * y))) }.
    (* todo: use "precedes" here? *)

Class OrdField A {e: Equiv A} {plus mult inv zero one mult_inv leq}: Prop :=
  { ordfield_field:> @Field A e plus mult inv zero one mult_inv
  ; ordfield_order:> RingOrder e plus mult zero leq }.

Local Infix "<*>" := ralgebra_action (at level 30).

Class Rmodule `(e: Equiv Scalar) `(Equiv Elem) `{RalgebraAction Scalar Elem}
    scalar_plus scalar_mult scalar_inv scalar_zero scalar_one
    elem_plus elem_zero elem_opp: Prop :=
  { rmodule_ring:> @Ring Scalar e scalar_plus scalar_mult scalar_inv scalar_zero scalar_one
  ; rmodule_abgroup:> @AbGroup _ _ elem_plus elem_zero elem_opp
  ; rmodule_distr_l: `(x <*> (a & b) = (x <*> a) & (x <*> b))
  ; rmodule_distr_r: `((x + y) <*> a = (x <*> a) & (y <*> a))
  ; rmodule_assoc: `((x * y) <*> a = x <*> (y <*> a)) }.

Class Ralgebra `(e: Equiv Scalar) `(e': Equiv Elem) `{RalgebraAction Scalar Elem}
    scalar_plus scalar_mult scalar_inv scalar_zero scalar_one
    elem_plus elem_mult elem_zero elem_one elem_opp: Prop :=
  { ralgebra_module:> Rmodule e e'
      scalar_plus scalar_mult scalar_inv scalar_zero scalar_one
      elem_plus elem_zero elem_opp
  ; ralgebra_ring:> @Ring Elem e' elem_plus elem_mult elem_opp elem_zero elem_one
  ; ralgebra_assoc: `(x <*> (a * b) = (x <*> a) * b) }.

Definition is_derivation `{Ralgebra Scalar Elem} (f: Elem → Elem): Prop :=
  True. (* something *)

Class Category O `{!Arrows O} `{Π x y: O, Equiv (x ⟶ y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv:> Π x y: O, Setoid (x ⟶ y)
  ; comp_proper:> Π x y z, Proper (equiv ==> equiv ==> equiv)%signature (@comp _ _ _ x y z)
  ; comp_assoc (w x y z: O) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z):
      c ◎ (b ◎ a) = (c ◎ b) ◎ a
  ; id_l `(a: x ⟶ y): cat_id ◎ a = a
  ; id_r `(a: x ⟶ y): a ◎ cat_id = a }.
      (* note: no equality on objects. *)

(* todo: use my comp everywhere *)

Implicit Arguments comp_assoc [[O] [Arrows0] [H] [CatId0] [CatComp0] [Category] [w] [x] [y] [z]].

(* Morphism classes: *)

Section morphism_classes.

  Context {A B: Type}.

  Class Setoid_Morphism `{Aeq: Equiv A} `{Beq: Equiv B} (f: A → B) :=
    { setoidmod_a: Setoid A
    ; setoidmod_b: Setoid B
    ; sm_proper:> Proper (equiv ==> equiv) f }.

  Class SemiGroup_Morphism {Aeq Beq Aop Bop} (f: A → B) :=
    { a_sg: @SemiGroup A Aeq Aop
    ; b_sg: @SemiGroup B Beq Bop
    ; sg_mor_op_proper:> Setoid_Morphism f (* todo: rename *)
    ; preserves_sg_op: `(f (a & a') = f a & f a') }.

  Class Monoid_Morphism {Ae Be Aunit Bunit Amult Bmult} (f: A → B) :=
    { monmor_a: @Monoid A Ae Amult Aunit
    ; monmor_b: @Monoid B Be Bmult Bunit
    ; monmor_sgmor:> SemiGroup_Morphism f
    ; preserves_mon_unit: f mon_unit = mon_unit }.

  Class Group_Morphism {Aeq Beq Aop Bop Aunit Bunit Ainv Binv} (f: A → B):=
    { groupmor_a: @Group A Aeq Aop Aunit Ainv
    ; groupmor_b: @Group B Beq Bop Bunit Binv
    ; groupmor_monoidmor:> Monoid_Morphism f
    ; preserves_inv: `(f (- x) = - f x) }.

  Class SemiRing_Morphism {Ae Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f: A → B) :=
    { semiringmor_a: @SemiRing A Ae Aplus Amult Azero Aone
    ; semiringmor_b: @SemiRing B Be Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor:> @Monoid_Morphism Ae Be Azero Bzero Aplus Bplus f
    ; semiringmor_mult_mor:> @Monoid_Morphism Ae Be Aone Bone Amult Bmult f }.

  Class Ring_Morphism {Ae Aplus Amult Aopp Azero Aone Be Bplus Bmult Bopp Bzero Bone} (f: A → B) :=
    { ringmor_a: @Ring A Ae Aplus Amult Aopp Azero Aone
    ; ringmor_b: @Ring B Be Bplus Bmult Bopp Bzero Bone
    ; ringmor_groupmor:> @Group_Morphism _ _ Aplus Bplus Azero Bzero Aopp Bopp f
    ; ringmor_monoidmor:> @Monoid_Morphism _ _ Aone Bone Amult Bmult f }.

End morphism_classes.

  (* The structure instance fields in the morphism classed used to be coercions, but
   that ultimately caused too much problems. *)

(* Todo: We really introduce way too many names in the above, but Coq currently doesn't seem to support nameless class fields.  *)
