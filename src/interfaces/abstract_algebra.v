Require
 Equivalence.
Require Export
 Morphisms Setoid Program
 canonical_names util workarounds setoid_tactics.

(* 
For various structures we omit declaration of substructures. For example, if we 
say:

Class Setoid_Morphism :=
  { setoidmor_a :> Setoid A
  ; setoidmor_b :> Setoid B
  ; sm_proper :> Proper ((=) ==> (=)) f }.

then each time a Setoid instance is required, Coq will try to prove that a
Setoid_Morphism exists. This obviously results in an enormous blow-up of the
search space. Moreover, one should be careful to declare a Setoid_Morphisms
as a substructure. Consider [f t1 t2], now if we want to perform setoid rewriting
in [t2] Coq will first attempt to prove that [f t1] is Proper, for which it will 
attempt to prove [Setoid_Morphism (f t1)]. If many structures declare
Setoid_Morphism as a substructure, setoid rewriting will become horribly slow.
*)

(* An unbundled variant of the former CoRN RSetoid *)
Class Setoid A {e: Equiv A} : Prop := setoid_eq:> Equivalence (@equiv A e).

(* An unbundled variant of the former CoRN CSetoid. We do not 
  include that a proof that A is a Setoid because that can be derived. *)
Class StrongSetoid A {e: Equiv A} `{ap : Apart A} : Prop :=
  { strong_setoid_irreflexive :> Irreflexive (⪥) 
  ; strong_setoid_symmetric :> Symmetric (⪥) 
  ; strong_setoid_cotrans :> CoTransitive (⪥) 
  ; tight_apart : ∀ x y, ¬x ⪥ y ↔ x = y }.

Section setoid_morphisms.
  Context {A B : Type} {Ae: Equiv A} {Aap: Apart A} {Be: Equiv B} {Bap : Apart B} (f: A → B).

  Class Setoid_Morphism :=
    { setoidmor_a: Setoid A
    ; setoidmor_b: Setoid B
    ; sm_proper:> Proper ((=) ==> (=)) f }. 

  Class StrongSetoid_Morphism :=
    { strong_setoidmor_a: StrongSetoid A
    ; strong_setoidmor_b: StrongSetoid B
    ; strong_extensionality : ∀ x y, f x ⪥ f y → x ⪥ y }.
End setoid_morphisms.

Implicit Arguments sm_proper [[A] [B] [Ae] [Be] [f] [Setoid_Morphism]].

Section setoid_binary_morphisms.
  Context {A B C : Type} {Ae: Equiv A} {Aap: Apart A} 
    {Be: Equiv B} {Bap : Apart B} {Ce: Equiv C} {Cap : Apart C} (f: A → B → C).

  Class StrongSetoid_BinaryMorphism :=
    { strong_binary_setoidmor_a: StrongSetoid A
    ; strong_binary_setoidmor_b: StrongSetoid B
    ; strong_binary_setoidmor_c: StrongSetoid C
    ; strong_binary_extensionality : ∀ x₁ y₁ x₂ y₂, f x₁ y₁ ⪥ f x₂ y₂ → x₁ ⪥ x₂ ∨ y₁ ⪥ y₂ }.
End setoid_binary_morphisms.

(*
Since apartness usually only becomes relevant when considering fields (e.g. the 
real numbers), we do not include it in the lower part of the algebraic hierarchy
(as opposed to CoRN).
*)
Section upper_classes.
  Context A {e: Equiv A}.

  Class SemiGroup {op: SemiGroupOp A}: Prop :=
    { sg_setoid:> Setoid A
    ; sg_ass:> Associative (&)
    ; sg_op_proper:> Proper ((=) ==> (=) ==> (=)) (&) }.

  Class Monoid {op: SemiGroupOp A} {unit: MonoidUnit A}: Prop :=
    { monoid_semigroup:> SemiGroup
    ; monoid_left_id:> LeftIdentity (&) mon_unit
    ; monoid_right_id:> RightIdentity (&) mon_unit }.

  Class CommutativeMonoid {op unit}: Prop :=
    { commonoid_mon:> @Monoid op unit
    ; commonoid_commutative:> Commutative (&) }.

  Class Group {op unit} {inv: GroupInv A}: Prop :=
    { group_monoid:> @Monoid op unit
    ; inv_proper:> Setoid_Morphism (-)
    ; ginv_l:> LeftInverse (&) (-) mon_unit
    ; ginv_r:> RightInverse (&) (-) mon_unit }.

  Class AbGroup {op unit inv}: Prop :=
    { abgroup_group:> @Group op unit inv
    ; abgroup_commutative:> Commutative (&) }.

  Context {plus: RingPlus A} {mult: RingMult A} {zero: RingZero A} {one: RingOne A}.

  Class SemiRing: Prop :=
    { semiring_mult_monoid:> @CommutativeMonoid ringmult_is_semigroupop ringone_is_monoidunit
    ; semiring_plus_monoid:> @CommutativeMonoid ringplus_is_semigroupop ringzero_is_monoidunit
    ; semiring_distr:> Distribute (.*.) (+)
    ; semiring_left_absorb:> LeftAbsorb (.*.) 0 }.

  Context {inv: GroupInv A}.

  Class Ring: Prop :=
    { ring_group:> @AbGroup ringplus_is_semigroupop ringzero_is_monoidunit _
    ; ring_monoid:> @CommutativeMonoid ringmult_is_semigroupop ringone_is_monoidunit
    ; ring_dist:> Distribute (.*.) (+) }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain: Prop :=
    { intdom_ring: Ring 
    ; intdom_nontrivial: PropHolds (1 ≠ 0)
    ; intdom_nozeroes:> NoZeroDivisors A }.

  (* We do not include strong extensionality for (-) and (/) because it can de derived *)
  Class Field {ap: Apart A} {mult_inv: MultInv A} : Prop :=
    { field_ring:> Ring
    ; field_strongsetoid:> StrongSetoid A
    ; field_plus_ext:> StrongSetoid_BinaryMorphism (+)
    ; field_mult_ext:> StrongSetoid_BinaryMorphism (.*.)
    ; field_nontrivial: PropHolds (1 ⪥ 0)
    ; mult_inv_proper:> Setoid_Morphism (//)
    ; mult_inverse: ∀ x, `x // x = 1 }.

  (* We let /0 = 0 so properties as Injective (/), f (/x) = / (f x), --x = x, /x * /y = /(x * y) 
    hold without any additional assumptions *)
  Class DecField {dec_mult_inv: DecMultInv A}: Prop :=
    { decfield_ring:> Ring
    ; decfield_nontrivial: PropHolds (1 ≠ 0)
    ; dec_mult_inv_proper:> Setoid_Morphism (/)
    ; dec_mult_inv_0: /0 = 0
    ; dec_mult_inverse: ∀ x, x ≠ 0 → x / x = 1 }.
End upper_classes.

(* Due to bug #2528 *)
Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ⪥ 0)) => eapply @field_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @decfield_nontrivial : typeclass_instances.

(* 
For a strange reason Ring instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> Ring forces Coq to
take the right way 
*)
Hint Extern 10 (Ring _) => apply @intdom_ring : typeclass_instances.

Implicit Arguments tight_apart [[A] [e] [ap] [StrongSetoid]].
Implicit Arguments mult_inverse [[A] [e] [plus] [mult] [zero] [one] [inv] [ap] [mult_inv0] [Field]].
Implicit Arguments dec_mult_inverse [[A] [e] [plus] [mult] [zero] [one] [inv] [dec_mult_inv0] [DecField]].
Implicit Arguments dec_mult_inv_0 [[A] [e] [plus] [mult] [zero] [one] [inv] [dec_mult_inv0] [DecField]].
Implicit Arguments sg_op_proper [[A] [e] [op] [SemiGroup]].

(* Although cancellation is similar to being injective, we want a proper
  name to refer to this commonly used notion. *)
Section cancellation.
  Context `{e : Equiv A} `{ap : Apart A} (op : A → A → A) (z : A).

  Class LeftCancellation := left_cancellation : `(op z x = op z y → x = y).
  Class RightCancellation := right_cancellation : `(op x z = op y z → x = y).

  Class StrongLeftCancellation := strong_left_cancellation : `(x ⪥ y → op z x ⪥ op z y).
  Class StrongRightCancellation := strong_right_cancellation : `(x ⪥ y → op x z ⪥ op y z).
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
  Context {A B : Type} {Ae: Equiv A} {Be: Equiv B}.

  Class SemiGroup_Morphism {Aop Bop} (f: A → B) :=
    { sgmor_a: @SemiGroup A Ae Aop
    ; sgmor_b: @SemiGroup B Be Bop
    ; sgmor_setmor:> Setoid_Morphism f
    ; preserves_sg_op: `(f (a & a') = f a & f a') }.

  Class Monoid_Morphism {Aunit Bunit Amult Bmult} (f: A → B) :=
    { monmor_a: @Monoid A Ae Amult Aunit
    ; monmor_b: @Monoid B Be Bmult Bunit
    ; monmor_sgmor:> SemiGroup_Morphism f
    ; preserves_mon_unit: f mon_unit = mon_unit }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f: A → B) :=
    { semiringmor_a: @SemiRing A Ae Aplus Amult Azero Aone
    ; semiringmor_b: @SemiRing B Be Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor:> @Monoid_Morphism ringzero_is_monoidunit ringzero_is_monoidunit 
            ringplus_is_semigroupop ringplus_is_semigroupop f
    ; semiringmor_mult_mor:> @Monoid_Morphism ringone_is_monoidunit ringone_is_monoidunit 
            ringmult_is_semigroupop ringmult_is_semigroupop f }.

  Context {Aap: Apart A} {Bap: Apart B}.
  Class StrongSemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f: A → B) :=
    { strong_semiringmor_sr_mor:> @SemiRing_Morphism Aplus Amult Azero Aone Bplus Bmult Bzero Bone f
    ; strong_semiringmor_strong_mor:> StrongSetoid_Morphism f }.
End morphism_classes.

Implicit Arguments monmor_a [[A] [B] [Ae] [Be] [Aunit] [Bunit] [Amult] [Bmult] [Monoid_Morphism]].
Implicit Arguments monmor_b [[A] [B] [Ae] [Be] [Aunit] [Bunit] [Amult] [Bmult] [Monoid_Morphism]].

(* These are only necessary because for reasons unknown ot me the [f] argument is
 made implicit by default. Waiting to hear from Matthieu about this. *)

Section jections.
  Context {A B : Type} {Ae: Equiv A} {Aap: Apart A} 
    {Be: Equiv B} {Bap : Apart B} (f: A → B) `{inv: !Inverse f}.

  Class StrongInjective: Prop :=
    { strong_injective: ∀ x y, x ⪥ y → f x ⪥ f y
    ; strong_injective_mor: StrongSetoid_Morphism f }.

  Class Injective: Prop :=
    { injective: ∀ x y, f x = f y → x = y
    ; injective_mor: Setoid_Morphism f }.

  Class Surjective: Prop :=
    { surjective: f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *)
    ; surjective_mor: Setoid_Morphism f }.

  Class Bijective: Prop :=
    { bijective_injective:> Injective
    ; bijective_surjective:> Surjective }.
End jections.
