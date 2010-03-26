Set Automatic Introduction.

Require
 Equivalence.
Require Import
 Morphisms Setoid Program.
Require Export
 canonical_names util.

Class LeftIdentity {A} `{Equiv B} (op: A → B → B) (x: A): Prop := left_identity: Π y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op: A → B → A) (y: B): Prop := right_identity: Π x, op x y = x.

Class LeftAbsorb `{Equiv A} {B} (op: A → B → A) (x: A): Prop := left_absorb: Π y, op x y = x.
Class RightAbsorb {A} `{Equiv B} (op: A → B → B) (y: B): Prop := right_absorb: Π x, op x y = y.
  (* hm, can we generate left/right instances from right/left+commutativity without causing loops? *)

Section upper_classes.

  Context A {e: Equiv A}.

  Class Setoid: Prop := setoid_eq:> Equivalence (@equiv A e).

  Class SemiGroup {op: SemiGroupOp A}: Prop :=
    { sg_setoid:> Setoid
    ; sg_ass:> Associative sg_op
    ; sg_mor:> Proper (e ==> e ==> e)%signature sg_op }.

  Class Monoid {op: SemiGroupOp A} {unit: MonoidUnit A}: Prop :=
    { monoid_semigroup:> SemiGroup
    ; monoid_left_id:> LeftIdentity sg_op mon_unit
    ; monoid_right_id:> RightIdentity sg_op mon_unit }.

  Class CommutativeMonoid {op unit}: Prop :=
    { commonoid_mon:> @Monoid op unit
    ; commonoid_commutative:> Commutative op }.

  Class Group {op: SemiGroupOp A} {unit: MonoidUnit A} {inv: GroupInv A}: Prop :=
    { group_monoid:> Monoid
    ; inv_proper:> Proper (e ==> e) inv (* todo: use Setoid_Morphism *)
    ; ginv_l: `(- x & x = mon_unit)
    ; ginv_r: `(x & - x = mon_unit) }.

  Class AbGroup {op unit inv}: Prop :=
    { abgroup_group:> @Group op unit inv
    ; abgroup_commutative:> Commutative op }.

  Context {plus: RingPlus A} {mult: RingMult A} {zero: RingZero A} {one: RingOne A}.

  Class SemiRing: Prop :=
    { semiring_mult_monoid:> CommutativeMonoid (op:=mult) (unit:=one)
    ; semiring_plus_monoid:> CommutativeMonoid (op:=plus) (unit:=zero)
    ; semiring_distr:> Distribute mult plus
    ; semiring_left_absorb:> LeftAbsorb ring_mult 0 }.

  Context {inv: GroupInv A}.

  Class Ring: Prop :=
    { ring_group:> AbGroup (op:=plus) (unit:=zero)
    ; ring_monoid:> CommutativeMonoid (op:=mult) (unit:=one)
    ; ring_dist:> Distribute mult plus }.

    (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain: Prop :=
    { intdom_ring:> Ring
    ; intdom_nontrivial:> ZeroNeOne A
    ; intdom_nozeroes:> NoZeroDivisors A }.

  Class Field {mult_inv: MultInv A}: Prop :=
    { field_ring:> Ring
    ; field_0neq1:> ZeroNeOne A
    ; mult_inv_proper:> Proper (sig_relation (=) _ ==> (=)) mult_inv
    ; mult_inverse: `(` x * // x = 1) }.

End upper_classes.

Implicit Arguments inv_proper [[A] [e] [op] [unit] [inv] [Group]].
Implicit Arguments ginv_l [[A] [e] [op] [unit] [inv] [Group]].
Implicit Arguments ginv_r [[A] [e] [op] [unit] [inv] [Group]].
Implicit Arguments field_0neq1 [[A] [e] [plus] [mult] [zero] [one] [inv] [mult_inv] [Field]].
Implicit Arguments mult_inverse [[A] [e] [plus] [mult] [zero] [one] [inv] [mult_inv0] [Field]].
Implicit Arguments sg_mor [[A] [e] [op] [SemiGroup]].

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
  { ordfield_field:> @Field A e plus mult zero one inv mult_inv
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
  ; ralgebra_ring:> @Ring Elem e' elem_plus elem_mult elem_zero elem_one elem_opp
  ; ralgebra_assoc: `(x <*> (a * b) = (x <*> a) * b) }.

Definition is_derivation `{Ralgebra Scalar Elem} (f: Elem → Elem): Prop :=
  True. (* something *)

Class Category O `{!Arrows O} `{Π x y: O, Equiv (x ⟶ y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv:> Π x y, Setoid (x ⟶ y)
  ; comp_proper:> Π x y z,
    Proper (equiv ==> equiv ==> equiv)%signature (comp: (y ⟶ z) → (x ⟶ y) → x ⟶ z)
  ; comp_assoc w x y z (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z):
      c ◎ (b ◎ a) = (c ◎ b) ◎ a
  ; id_l `(a: x ⟶ y): cat_id ◎ a = a
  ; id_r `(a: x ⟶ y): a ◎ cat_id = a }.
      (* note: no equality on objects. *)

(* todo: use my comp everywhere *)

Implicit Arguments comp_assoc [[O] [Arrows0] [H] [CatId0] [CatComp0] [Category] [w] [x] [y] [z]].

Section morphism_classes.

  Context {A B: Type} `{Aeq: Equiv A} `{Beq: Equiv B}.

  Class Setoid_Morphism (f: A → B) :=
    { setoidmor_a: Setoid A
    ; setoidmor_b: Setoid B
    ; sm_proper:> Proper (equiv ==> equiv) f }.

  Class SemiGroup_Morphism {Aop Bop} (f: A → B) :=
    { sgmor_a: @SemiGroup A Aeq Aop
    ; sgmor_b: @SemiGroup B Beq Bop
    ; sgmor_setmor:> Setoid_Morphism f (* todo: rename *)
    ; preserves_sg_op: `(f (a & a') = f a & f a') }.

  Class Monoid_Morphism {Aunit Bunit Amult Bmult} (f: A → B) :=
    { monmor_a: @Monoid A Aeq Amult Aunit
    ; monmor_b: @Monoid B Beq Bmult Bunit
    ; monmor_sgmor:> SemiGroup_Morphism f
    ; preserves_mon_unit: f mon_unit = mon_unit }.

  Class Group_Morphism {Aop Bop Aunit Bunit Ainv Binv} (f: A → B):=
    { groupmor_a: @Group A Aeq Aop Aunit Ainv
    ; groupmor_b: @Group B Beq Bop Bunit Binv
    ; groupmor_monoidmor:> Monoid_Morphism f
    ; preserves_inv: `(f (- x) = - f x) }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f: A → B) :=
    { semiringmor_a: @SemiRing A Aeq Aplus Amult Azero Aone
    ; semiringmor_b: @SemiRing B Beq Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor:> @Monoid_Morphism Azero Bzero Aplus Bplus f
    ; semiringmor_mult_mor:> @Monoid_Morphism Aone Bone Amult Bmult f }.

  Class Ring_Morphism {Aplus Amult Aopp Azero Aone Bplus Bmult Bopp Bzero Bone} (f: A → B) :=
    { ringmor_a: @Ring A Aeq Aplus Amult Azero Aone Aopp
    ; ringmor_b: @Ring B Beq Bplus Bmult Bzero Bone Bopp
    ; ringmor_groupmor:> @Group_Morphism Aplus Bplus Azero Bzero Aopp Bopp f
    ; ringmor_monoidmor:> @Monoid_Morphism Aone Bone Amult Bmult f }.

End morphism_classes.

  (* The structure instance fields in the morphism classed used to be coercions, but
   that ultimately caused too much problems. *)

(* Todo: We really introduce way too many names in the above, but Coq currently doesn't seem to support nameless class fields.  *)

Section jections.

  Context `{ea: Equiv A} `{eb: Equiv B} (f: A → B) `{!Inv f}.

  Class Injective: Prop :=
    { injective: `(f x = f y → x = y)
    ; injective_mor:> Setoid_Morphism f }.

  Class Surjective: Prop :=
    { surjective: f ∘ inv = id (* a.k.a. "split-epi" *)
    ; surjective_mor:> Setoid_Morphism f }.

  Class Bijective: Prop :=
    { bijective_injective:> Injective
    ; bijective_surjective:> Surjective }.

End jections.

Implicit Arguments injective [[A] [ea] [B] [eb] [Injective]].

Instance Setoid_Morphism_proper `{ea: Equiv A} `{eb: Equiv B}: Proper ((=) ==> iff) (@Setoid_Morphism A B _ _).
Proof.
 cut (Π (x y: A → B), x = y → Setoid_Morphism x → Setoid_Morphism y).
  firstorder.
 intros x y E [AS BS P].
 constructor; try apply _. intros v w E'.
 rewrite <- (E v), <- (E w), E'. reflexivity.
Qed.

Instance: Π A `{Setoid B}, Setoid (A -> B).
Proof. constructor; repeat intro; firstorder. Qed.

Instance Injective_proper `{ea: Equiv A} `{eb: Equiv B}: Proper ((=) ==> iff) (@Injective A ea B eb).
Proof with intuition.
 cut (Π (x y: A → B), x = y → Injective x → Injective y).
  split; repeat intro.
   apply H with x...
  destruct (injective_mor y).
  apply H with y...
 repeat intro.
 destruct (injective_mor x).
 constructor.
  repeat intro.
  apply (injective x).
  rewrite (H x0), (H y0)...
 rewrite <- H...
Qed. 

Instance Injective_comp `{Equiv A} `{Equiv B} `{Equiv C} (g: A → B) (f: B → C):
  Injective f → Injective g → Injective (f ∘ g).
Proof. firstorder. Qed.
