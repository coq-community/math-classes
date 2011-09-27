Require Export
  canonical_names util decision propholds workarounds setoid_tactics.

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
Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

(* An unbundled variant of the former CoRN CSetoid. We do not 
  include a proof that A is a Setoid because it can be derived. *)
Class StrongSetoid A {Ae : Equiv A} `{Aap : Apart A} : Prop :=
  { strong_setoid_irreflexive :> Irreflexive (≶) 
  ; strong_setoid_symmetric :> Symmetric (≶) 
  ; strong_setoid_cotrans :> CoTransitive (≶) 
  ; tight_apart : ∀ x y, ¬x ≶ y ↔ x = y }.

Implicit Arguments tight_apart [[A] [Ae] [Aap] [StrongSetoid]].

Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Aap : Apart A} {Be : Equiv B} {Bap : Apart B} (f : A → B).

  Class Setoid_Morphism :=
    { setoidmor_a : Setoid A
    ; setoidmor_b : Setoid B
    ; sm_proper :> Proper ((=) ==> (=)) f }. 

  Class StrongSetoid_Morphism :=
    { strong_setoidmor_a : StrongSetoid A
    ; strong_setoidmor_b : StrongSetoid B
    ; strong_extensionality : ∀ x y, f x ≶ f y → x ≶ y }.
End setoid_morphisms.

Implicit Arguments sm_proper [[A] [B] [Ae] [Be] [f] [Setoid_Morphism]].

Section setoid_binary_morphisms.
  Context {A B C} {Ae: Equiv A} {Aap: Apart A} 
    {Be: Equiv B} {Bap : Apart B} {Ce: Equiv C} {Cap : Apart C} (f : A → B → C).

  Class StrongSetoid_BinaryMorphism :=
    { strong_binary_setoidmor_a : StrongSetoid A
    ; strong_binary_setoidmor_b : StrongSetoid B
    ; strong_binary_setoidmor_c : StrongSetoid C
    ; strong_binary_extensionality : ∀ x₁ y₁ x₂ y₂, f x₁ y₁ ≶ f x₂ y₂ → x₁ ≶ x₂ ∨ y₁ ≶ y₂ }.
End setoid_binary_morphisms.

(*
Since apartness usually only becomes relevant when considering fields (e.g. the 
real numbers), we do not include it in the lower part of the algebraic hierarchy
(as opposed to CoRN).
*)
Section upper_classes.
  Context A {Ae : Equiv A}.

  Class SemiGroup {Aop: SgOp A} : Prop :=
    { sg_setoid :> Setoid A
    ; sg_ass :> Associative (&)
    ; sg_op_proper :> Proper ((=) ==> (=) ==> (=)) (&) }.

  Class CommutativeSemiGroup {Aop : SgOp A} : Prop :=
    { comsg_setoid :> @SemiGroup Aop
    ; comsg_ass :> Commutative (&) }.

  Class SemiLattice {Aop : SgOp A} : Prop :=
    { semilattice_sg :> @CommutativeSemiGroup Aop
    ; semilattice_idempotent :> BinaryIdempotent (&)}.

  Class Monoid {Aop : SgOp A} {Aunit : MonUnit A} : Prop :=
    { monoid_semigroup :> SemiGroup
    ; monoid_left_id :> LeftIdentity (&) mon_unit
    ; monoid_right_id :> RightIdentity (&) mon_unit }.

  Class CommutativeMonoid {Aop Aunit} : Prop :=
    { commonoid_mon :> @Monoid Aop Aunit
    ; commonoid_commutative :> Commutative (&) }.

  Class Group {Aop Aunit} {Anegate : Negate A} : Prop :=
    { group_monoid :> @Monoid Aop Aunit
    ; negate_proper :> Setoid_Morphism (-)
    ; negate_l :> LeftInverse (&) (-) mon_unit
    ; negate_r :> RightInverse (&) (-) mon_unit }.

  Class BoundedSemiLattice {Aop Aunit} : Prop :=
    { bounded_semilattice_mon :> @CommutativeMonoid Aop Aunit
    ; bounded_semilattice_idempotent :> BinaryIdempotent (&)}.

  Class AbGroup {Aop Aunit Anegate} : Prop :=
    { abgroup_group :> @Group Aop Aunit Anegate
    ; abgroup_commutative :> Commutative (&) }.

  Context {Aplus : Plus A} {Amult : Mult A} {Azero : Zero A} {Aone : One A}.

  Class SemiRing : Prop :=
    { semiplus_monoid :> @CommutativeMonoid plus_is_sg_op zero_is_mon_unit
    ; semimult_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; semiring_distr :> LeftDistribute (.*.) (+)
    ; semiring_left_absorb :> LeftAbsorb (.*.) 0 }.

  Context {Anegate : Negate A}.

  Class Ring : Prop :=
    { ring_group :> @AbGroup plus_is_sg_op zero_is_mon_unit _
    ; ring_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; ring_dist :> LeftDistribute (.*.) (+) }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain : Prop :=
    { intdom_ring : Ring 
    ; intdom_nontrivial : PropHolds (1 ≠ 0)
    ; intdom_nozeroes :> NoZeroDivisors A }.

  (* We do not include strong extensionality for (-) and (/) because it can de derived *)
  Class Field {Aap: Apart A} {Arecip: Recip A} : Prop :=
    { field_ring :> Ring
    ; field_strongsetoid :> StrongSetoid A
    ; field_plus_ext :> StrongSetoid_BinaryMorphism (+)
    ; field_mult_ext :> StrongSetoid_BinaryMorphism (.*.)
    ; field_nontrivial : PropHolds (1 ≶ 0)
    ; recip_proper :> Setoid_Morphism (//)
    ; recip_inverse : ∀ x, `x // x = 1 }.

  (* We let /0 = 0 so properties as Injective (/), f (/x) = / (f x), / /x = x, /x * /y = /(x * y) 
    hold without any additional assumptions *)
  Class DecField {Adec_recip : DecRecip A} : Prop :=
    { decfield_ring :> Ring
    ; decfield_nontrivial : PropHolds (1 ≠ 0)
    ; dec_recip_proper :> Setoid_Morphism (/)
    ; dec_recip_0 : /0 = 0
    ; dec_recip_inverse : ∀ x, x ≠ 0 → x / x = 1 }.
End upper_classes.

(* Due to bug #2528 *)
Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≶ 0)) => eapply @field_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @decfield_nontrivial : typeclass_instances.

(* 
For a strange reason Ring instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> Ring forces Coq to
take the right way 
*)
Hint Extern 10 (Ring _) => apply @intdom_ring : typeclass_instances.

Implicit Arguments recip_inverse [[A] [Ae] [Aplus] [Amult] [Azero] [Aone] [Anegate] [Aap] [Arecip] [Field]].
Implicit Arguments dec_recip_inverse [[A] [Ae] [Aplus] [Amult] [Azero] [Aone] [Anegate] [Adec_recip] [DecField]].
Implicit Arguments dec_recip_0 [[A] [Ae] [Aplus] [Amult] [Azero] [Aone] [Anegate] [Adec_recip] [DecField]].
Implicit Arguments sg_op_proper [[A] [Ae] [Aop] [SemiGroup]].

Section lattice.
  Context A `{Ae: Equiv A} {Ajoin: Join A} {Ameet: Meet A} `{Abottom : Bottom A}.

  Class JoinSemiLattice : Prop := 
    join_semilattice :> @SemiLattice A Ae join_is_sg_op.
  Class BoundedJoinSemiLattice : Prop := 
    bounded_join_semilattice :> @BoundedSemiLattice A Ae join_is_sg_op bottom_is_mon_unit.
  Class MeetSemiLattice : Prop := 
    meet_semilattice :> @SemiLattice A Ae meet_is_sg_op.

  Class Lattice : Prop := 
    { lattice_join :> JoinSemiLattice
    ; lattice_meet :> MeetSemiLattice
    ; join_meet_absorption :> Absorption (⊔) (⊓) 
    ; meet_join_absorption :> Absorption (⊓) (⊔)}.

  Class DistributiveLattice : Prop := 
    { distr_lattice_lattice :> Lattice
    ; join_meet_distr_l :> LeftDistribute (⊔) (⊓) }.
End lattice.

Class Category O `{!Arrows O} `{∀ x y: O, Equiv (x ⟶ y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv :> ∀ x y, Setoid (x ⟶ y)
  ; comp_proper :> ∀ x y z, Proper ((=) ==> (=) ==> (=)) (comp x y z)
  ; comp_assoc :> ArrowsAssociative O
  ; id_l :> ∀ x y, LeftIdentity (comp x y y) cat_id
  ; id_r :> ∀ x y, RightIdentity (comp x x y) cat_id }.
      (* note: no equality on objects. *)

(* todo: use my comp everywhere *)
Implicit Arguments comp_assoc [[O] [Arrows0] [H] [CatId0] [CatComp0] [Category] [w] [x] [y] [z]].

Section morphism_classes.
  Context {A B} {Ae : Equiv A} {Be : Equiv B}.

  Class SemiGroup_Morphism {Aop Bop} (f : A → B) :=
    { sgmor_a : @SemiGroup A Ae Aop
    ; sgmor_b : @SemiGroup B Be Bop
    ; sgmor_setmor :> Setoid_Morphism f
    ; preserves_sg_op : ∀ x y, f (x & y) = f x & f y }.

  Class JoinSemiLattice_Morphism {Ajoin Bjoin} (f : A → B) :=
    { join_slmor_a : @JoinSemiLattice A Ae Ajoin
    ; join_slmor_b : @JoinSemiLattice B Be Bjoin
    ; join_slmor_sgmor :> @SemiGroup_Morphism join_is_sg_op join_is_sg_op f }.

  Class MeetSemiLattice_Morphism {Ameet Bmeet} (f : A → B) :=
    { meet_slmor_a : @MeetSemiLattice A Ae Ameet
    ; meet_slmor_b : @MeetSemiLattice B Be Bmeet
    ; meet_slmor_sgmor :> @SemiGroup_Morphism meet_is_sg_op meet_is_sg_op f }.

  Class Monoid_Morphism {Aunit Bunit Aop Bop} (f : A → B) :=
    { monmor_a : @Monoid A Ae Aop Aunit
    ; monmor_b : @Monoid B Be Bop Bunit
    ; monmor_sgmor :> SemiGroup_Morphism f
    ; preserves_mon_unit : f mon_unit = mon_unit }.

  Class BoundedJoinSemiLattice_Morphism {Abottom Bbottom Ajoin Bjoin} (f : A → B) :=
    { bounded_join_slmor_a : @BoundedJoinSemiLattice A Ae Ajoin Abottom
    ; bounded_join_slmor_b : @BoundedJoinSemiLattice B Be Bjoin Bbottom
    ; bounded_join_slmor_monmor :> @Monoid_Morphism bottom_is_mon_unit bottom_is_mon_unit join_is_sg_op join_is_sg_op f }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { semiringmor_a : @SemiRing A Ae Aplus Amult Azero Aone
    ; semiringmor_b : @SemiRing B Be Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor :> @Monoid_Morphism zero_is_mon_unit zero_is_mon_unit plus_is_sg_op plus_is_sg_op f
    ; semiringmor_mult_mor :> @Monoid_Morphism one_is_mon_unit one_is_mon_unit mult_is_sg_op mult_is_sg_op f }.

  Class Lattice_Morphism {Ajoin Ameet Bjoin Bmeet} (f : A → B) :=
    { latticemor_a : @Lattice A Ae Ajoin Ameet
    ; latticemor_b : @Lattice B Be Bjoin Bmeet
    ; latticemor_join_mor :> JoinSemiLattice_Morphism f
    ; latticemor_meet_mor :> MeetSemiLattice_Morphism f }.

  Context {Aap : Apart A} {Bap : Apart B}.
  Class StrongSemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { strong_semiringmor_sr_mor :> @SemiRing_Morphism Aplus Amult Azero Aone Bplus Bmult Bzero Bone f
    ; strong_semiringmor_strong_mor :> StrongSetoid_Morphism f }.
End morphism_classes.

Section jections.
  Context {A B} {Ae : Equiv A} {Aap : Apart A} 
    {Be : Equiv B} {Bap : Apart B} (f : A → B) `{inv : !Inverse f}.

  Class StrongInjective : Prop :=
    { strong_injective : ∀ x y, x ≶ y → f x ≶ f y
    ; strong_injective_mor : StrongSetoid_Morphism f }.

  Class Injective : Prop :=
    { injective : ∀ x y, f x = f y → x = y
    ; injective_mor : Setoid_Morphism f }.

  Class Surjective : Prop :=
    { surjective : f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *)
    ; surjective_mor : Setoid_Morphism f }.

  Class Bijective : Prop :=
    { bijective_injective :> Injective
    ; bijective_surjective :> Surjective }.
End jections.
