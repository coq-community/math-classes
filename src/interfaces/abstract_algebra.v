Require
 Equivalence.
Require Import
 Morphisms Setoid Program.
Require Export
 canonical_names util setoid_tactics.

Section upper_classes.
  Context A {e: Equiv A}.

  Class Setoid: Prop := setoid_eq:> Equivalence (@equiv A e).

  Class SemiGroup {op: SemiGroupOp A}: Prop :=
    { sg_setoid:> Setoid
    ; sg_ass:> Associative sg_op
    ; sg_mor:> Proper ((=) ==> (=) ==> (=)) sg_op }.

  Class Monoid {op: SemiGroupOp A} {unit: MonoidUnit A}: Prop :=
    { monoid_semigroup:> SemiGroup
    ; monoid_left_id:> LeftIdentity sg_op mon_unit
    ; monoid_right_id:> RightIdentity sg_op mon_unit }.

  Class CommutativeMonoid {op unit}: Prop :=
    { commonoid_mon:> @Monoid op unit
    ; commonoid_commutative:> Commutative op }.

  Class Group {op: SemiGroupOp A} {unit: MonoidUnit A} {inv: GroupInv A}: Prop :=
    { group_monoid:> Monoid
    ; inv_proper:> Proper ((=) ==> (=)) (-) (* todo: use Setoid_Morphism *)
    ; ginv_l:> LeftInverse sg_op group_inv mon_unit
    ; ginv_r:> RightInverse sg_op group_inv mon_unit }.

  Class AbGroup {op unit inv}: Prop :=
    { abgroup_group:> @Group op unit inv
    ; abgroup_commutative:> Commutative op }.

  Context {plus: RingPlus A} {mult: RingMult A} {zero: RingZero A} {one: RingOne A}.

  Class SemiRing: Prop :=
    { semiring_mult_monoid:> CommutativeMonoid (op:=mult) (unit:=one)
    ; semiring_plus_monoid:> CommutativeMonoid (op:=plus) (unit:=zero)
    ; semiring_distr:> Distribute (.*.) (+)
    ; semiring_left_absorb:> LeftAbsorb (.*.) 0 }.

  Context {inv: GroupInv A}.

  Class Ring: Prop :=
    { ring_group:> AbGroup (op:=plus) (unit:=zero)
    ; ring_monoid:> CommutativeMonoid (op:=mult) (unit:=one)
    ; ring_dist:> Distribute (.*.) (+) }.

    (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain: Prop :=
    { intdom_ring: Ring 
    ; intdom_nontrivial:> PropHolds (1 ≠ 0)
    ; intdom_nozeroes:> NoZeroDivisors A }.

  Class Field {mult_inv: MultInv A}: Prop :=
    { field_ring:> Ring
    ; field_nontrivial:> PropHolds (1 ≠ 0)
    ; mult_inv_proper:> Proper ((=) ==> (=)) (//)
    ; mult_inverse: `( `x * // x = 1) }.
End upper_classes.

(* 
For a strange reason Ring instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> Ring forces Coq to
take the right way 
*)
Hint Extern 10 (Ring _) => apply @intdom_ring : typeclass_instances.

Implicit Arguments inv_proper [[A] [e] [op] [unit] [inv] [Group]].
Implicit Arguments ginv_l [[A] [e] [op] [unit] [inv] [Group]].
Implicit Arguments ginv_r [[A] [e] [op] [unit] [inv] [Group]].
Implicit Arguments mult_inverse [[A] [e] [plus] [mult] [zero] [one] [inv] [mult_inv0] [Field]].
Implicit Arguments sg_mor [[A] [e] [op] [SemiGroup]].

Section cancellation.
  Context `{e : Equiv A} (op : A → A → A) (z : A).

  Class LeftCancellation := left_cancellation : `(op z x = op z y → x = y).
  Class RightCancellation := right_cancellation : `(op x z = op y z → x = y).
End cancellation.

Class Category O `{!Arrows O} `{∀ x y: O, Equiv (x ⟶ y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv:> ∀ x y, Setoid (x ⟶ y)
  ; comp_proper:> ∀ x y z, Proper ((=) ==> (=) ==> (=)) (comp x y z)
  ; comp_assoc :> ArrowsAssociative O
  ; id_l :> `(LeftIdentity (comp x y y) cat_id)
  ; id_r :> `(RightIdentity (comp x x y) cat_id) }.
      (* note: no equality on objects. *)

(* todo: use my comp everywhere *)

Implicit Arguments comp_assoc [[O] [Arrows0] [H] [CatId0] [CatComp0] [Category] [w] [x] [y] [z]].

Section morphism_classes.
  Context {A B: Type} `{Aeq: Equiv A} `{Beq: Equiv B}.

  Class Setoid_Morphism (f: A → B) :=
    { setoidmor_a: Setoid A
    ; setoidmor_b: Setoid B
    ; sm_proper:> Proper ((=) ==> (=)) f }.

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

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f: A → B) :=
    { semiringmor_a: @SemiRing A Aeq Aplus Amult Azero Aone
    ; semiringmor_b: @SemiRing B Beq Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor:> @Monoid_Morphism Azero Bzero Aplus Bplus f
    ; semiringmor_mult_mor:> @Monoid_Morphism Aone Bone Amult Bmult f }.
End morphism_classes.

  (* The structure instance fields in the morphism classed used to be coercions, but
   that ultimately caused too much problems. *)

(* Todo: We really introduce way too many names in the above, but Coq currently doesn't seem to support nameless class fields.  *)

Implicit Arguments setoidmor_a [[A] [B] [Aeq] [Beq] [Setoid_Morphism]].
Implicit Arguments setoidmor_b [[A] [B] [Aeq] [Beq] [Setoid_Morphism]].

Implicit Arguments monmor_a [[A] [B] [Aeq] [Beq] [Aunit] [Bunit] [Amult] [Bmult] [Monoid_Morphism]].
Implicit Arguments monmor_b [[A] [B] [Aeq] [Beq] [Aunit] [Bunit] [Amult] [Bmult] [Monoid_Morphism]].

(* These are only necessary because for reasons unknown ot me the [f] argument is
 made implicit by default. Waiting to hear from Matthieu about this. *)

Section jections.
  Context `{ea: Equiv A} `{eb: Equiv B} (f: A → B) `{inv: !Inverse f}.

  Class Injective: Prop :=
    { injective: `(f x = f y → x = y)
    ; injective_mor:> Setoid_Morphism f }.

  Class Surjective: Prop :=
    { surjective: f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *)
    ; surjective_mor:> Setoid_Morphism f }.

  Class Bijective: Prop :=
    { bijective_injective:> Injective
    ; bijective_surjective:> Surjective }.
End jections.

Implicit Arguments injective [[A] [ea] [B] [eb] [Injective]].

Class PartialOrder `{e: Equiv A} (o : Order A): Prop :=
  { poset_setoid : Setoid A (* Making this a coercion results in instance resolution loops *)
  ; poset_proper:> Proper ((=) ==> (=) ==> iff) o
  ; poset_preorder:> PreOrder o
  ; poset_antisym:> AntiSymmetric o }.

Class TotalOrder `(o : Order A): Prop := total_order: ∀ x y: A, x ≤ y ∨ y ≤ x.

Section order_maps.
  Context `{Equiv A} `{oA : Order A} `{Equiv B} `{oB : Order B} (f : A → B).

  Class Order_Morphism := 
    { order_morphism_mor : Setoid_Morphism f (* Making this a coercion makes instance resolution slow *)
    ; order_morphism_proper_a :> Proper ((=) ==> (=) ==> iff) oA
    ; order_morphism_proper_b :> Proper ((=) ==> (=) ==> iff) oB }.

  Class OrderPreserving := 
    { order_preserving_morphism :> Order_Morphism 
    ; order_preserving : `(x ≤ y → f x ≤ f y) }.

  Class OrderPreservingBack := 
    { order_preserving_back_morphism :> Order_Morphism
    ; order_preserving_back : `(f x ≤ f y → x ≤ y) }.

  Class OrderEmbedding := 
    { order_embedding_preserving :> OrderPreserving
    ; order_embedding_back :> OrderPreservingBack }.

  Class OrderIsomorphism `{!Inverse f} := 
    { order_iso_embedding :> OrderEmbedding
    ; order_iso_surjective :> Surjective f }.

  Class StrictlyOrderPreserving := 
    { strictly_order_preserving_morphism :> Order_Morphism
    ; strictly_order_preserving : `(x < y → f x < f y) }.
End order_maps.

Class SemiRingOrder `{Equiv A} `{RingPlus A} `{RingMult A} `{RingZero A} (o : Order A) :=
  { srorder_partialorder:> PartialOrder (≤)
  ; srorder_plus : `(x ≤ y ↔ ∃ z, 0 ≤ z ∧ y = x + z)
  ; srorder_mult: `(0 ≤ x → ∀ y, 0 ≤ y → 0 ≤ x * y) }.

Class RingOrder `{Equiv A} `{RingPlus A} `{RingMult A} `{RingZero A} (o : Order A) :=
  { ringorder_partialorder:> PartialOrder (≤)
  ; ringorder_plus :> ∀ z, OrderPreserving ((+) z)
  ; ringorder_mult: `(0 ≤ x → ∀ y, 0 ≤ y → 0 ≤ x * y) }.
