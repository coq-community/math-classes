Set Automatic Introduction.

Require
 Equivalence.
Require Import
 Morphisms Setoid Program.
Require Export
 canonical_names util.

Class LeftIdentity {A} `{Equiv B} (op: A → B → B) (x: A): Prop := left_identity: ∀ y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op: A → B → A) (y: B): Prop := right_identity: ∀ x, op x y = x.

Class LeftAbsorb `{Equiv A} {B} (op: A → B → A) (x: A): Prop := left_absorb: ∀ y, op x y = x.
Class RightAbsorb {A} `{Equiv B} (op: A → B → B) (y: B): Prop := right_absorb: ∀ x, op x y = y.
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
    { intdom_ring: Ring 
    ; intdom_nontrivial:> ZeroNeOne A
    ; intdom_nozeroes:> NoZeroDivisors A }.

  (* For a strange reason Ring instances of Integers are sometimes obtained by
    Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
    instance with a low priority instead of using intdom_ring:> Ring forces Coq to
    take the right way *)
  Global Instance intdom_is_ring `{IntegralDomain} : Ring | 10. 
  Proof. apply intdom_ring. Qed.

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

Section cancellation.
  Context `{e : Equiv A} (Rel : relation A) (P : A → Prop) (op : A → A → A).

  Class LeftCancellation := 
    left_cancellation : ∀ z, P z → ∀ {x y}, Rel (op z x) (op z y) → Rel x y.
  Class RightCancellation := 
    right_cancellation : ∀ z, P z → ∀ {x y}, Rel (op x z) (op y z) → Rel x y.
End cancellation.

Implicit Arguments left_cancellation [[A] [Rel] [P] [LeftCancellation] [x] [y]].
Implicit Arguments right_cancellation [[A] [Rel] [P] [RightCancellation] [x] [y]].

Class PartialOrder `{e: Equiv A} (R: Order A): Prop :=
  { poset_setoid :> Equivalence e (* Setoid A introduces instance resolution bugs, todo: investigate *)
  ; poset_proper:> Proper (e ==> e ==> iff) R
  ; poset_preorder:> PreOrder R
  ; poset_antisym:> AntiSymmetric R }.

Class TotalOrder `(Order A): Prop := total_order: ∀ x y: A, x ≤ y ∨ y ≤ x.

Class RingOrder `(e: Equiv A) (plus: RingPlus A) (mult: RingMult A) (zero: RingZero A) (leq: Order A) :=
  { ringorder_partialorder:> PartialOrder leq
  ; ringorder_plus: `(x ≤ y → ∀ z, x + z ≤ y + z)
  ; ringorder_mult: `(0 ≤ x → ∀ y, 0 ≤ y → 0 ≤ x * y) }.

Class OrdRing A {e: Equiv A} {plus mult inv zero one leq}: Prop :=
  { ordring_ring:> @Ring A e plus mult zero one inv 
  ; ordring_order:> RingOrder e plus mult zero leq }.

Class OrdField A {e: Equiv A} {plus mult inv zero one mult_inv leq}: Prop :=
  { ordfield_field:> @Field A e plus mult zero one inv mult_inv
  ; ordfield_order:> RingOrder e plus mult zero leq }.

Instance ordfield_is_ordring `{OrdField A} : OrdRing A.

Class Category O `{!Arrows O} `{∀ x y: O, Equiv (x ⟶ y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv:> ∀ x y, Setoid (x ⟶ y)
  ; comp_proper:> ∀ x y z,
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

Implicit Arguments setoidmor_a [[A] [B] [Aeq] [Beq] [Setoid_Morphism]].
Implicit Arguments setoidmor_b [[A] [B] [Aeq] [Beq] [Setoid_Morphism]].

Implicit Arguments monmor_a [[A] [B] [Aeq] [Beq] [Aunit] [Bunit] [Amult] [Bmult] [Monoid_Morphism]].
Implicit Arguments monmor_b [[A] [B] [Aeq] [Beq] [Aunit] [Bunit] [Amult] [Bmult] [Monoid_Morphism]].

Implicit Arguments ringmor_a [[A] [B] [Aeq] [Beq]
   [Aplus] [Amult] [Aopp] [Azero] [Aone] [Bplus] [Bmult] [Bopp] [Bzero] [Bone] [Ring_Morphism]].
Implicit Arguments ringmor_b [[A] [B] [Aeq] [Beq]
   [Aplus] [Amult] [Aopp] [Azero] [Aone] [Bplus] [Bmult] [Bopp] [Bzero] [Bone] [Ring_Morphism]].

(* These are only necessary because for reasons unknown ot me the [f] argument is
 made implicit by default. Waiting to hear from Matthieu about this. *)

Section jections.

  Context `{ea: Equiv A} `{eb: Equiv B} (f: A → B) `{inv: !Inverse f}.

  Class Injective: Prop :=
    { injective: `(f x = f y → x = y)
    ; injective_mor:> Setoid_Morphism f }.

  Class Surjective: Prop :=
    { surjective: f ∘ inverse f = id (* a.k.a. "split-epi" *)
    ; surjective_mor:> Setoid_Morphism f }.

  Class Bijective: Prop :=
    { bijective_injective:> Injective
    ; bijective_surjective:> Surjective }.

End jections.

Implicit Arguments injective [[A] [ea] [B] [eb] [Injective]].
