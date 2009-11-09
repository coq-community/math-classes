Require Equivalence.

Require Import Morphisms Setoid Program.

Require Export CanonicalNames.

(* the stack itself: *)

Class SemiGroup `(e: Equiv A) (o: SemiGroupOp A) :=
 { sg_eq:> Equivalence e
 ; sg_ass:> Associative o
 ; sg_mor:> Proper (e ==> e ==> e)%signature sg_op }.

Class Monoid `(e: Equiv A) `(o: SemiGroupOp A) (u: MonoidUnit A) :=
  { monoid_semigroup:> SemiGroup e o
  ; lunit: forall x, mon_unit & x == x
  ; runit: forall x, x & mon_unit == x }.

Class Group `(e: Equiv A) (o: SemiGroupOp A) (u: MonoidUnit A) (inv: GroupInv A) :=
  { group_monoid:> Monoid e o u
  ; inv_proper:> Proper (e ==> e) inv
  ; inv_l: forall x, - x & x == mon_unit
  ; inv_r: forall x, x & - x == mon_unit }.

Class AbGroup {A: Type} (e: Equiv A) plus zero inv :=
  { abgroup_group:> Group e plus zero inv
  ; ab_com:> Commutative plus }.

Class SemiRing `(e: Equiv A) (plus: RingPlus A) (mult: RingMult A)
    (zero: RingZero A) (one: RingOne A) :=
  { semiring_mult_monoid:> Monoid e mult one
  ; semiring_plus_monoid:> Monoid e plus zero
  ; semiring_plus_comm:> Commutative plus
  ; semiring_mult_comm:> Commutative mult
  ; semiring_distr:> Distribute mult plus
  ; mult_0_l: forall x, 0 * x == 0 }.

(*Definition semiring_cat := homo_cat semiring_sig.sig semiring_sig.E.*)

Class Ring `(e: Equiv A) (plus: RingPlus A) (mult: RingMult A) (inv: GroupInv A)
  (zero: RingZero A) (one: RingOne A) :=
  { ring_group:> AbGroup e plus zero inv
  ; ring_monoid:> Monoid e mult one
  ; ring_mult_comm:> Commutative mult
  ; ring_dist:> Distribute mult plus }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
   require commutative multiplication. *)

Definition sig_relation {A} (R: relation A) (P: A -> Prop): relation (sig P)
  := fun a b => R (proj1_sig a) (proj1_sig b).
   (* todo: move to util *)

Class Field `(e: Equiv A) plus mult inv zero one (mult_inv: MultInv A) :=
  { field_ring:> Ring e plus mult inv zero one
  ; field_0neq1: ~ 0 == 1
  ; mult_inv_proper: Proper (sig_relation equiv _ ==> equiv) mult_inv
  ; mult_inverse: forall x, ` x * // x == 1 }.

Class OrdField `(e: Equiv A) plus mult inv zero one mult_inv (leq: relation A) :=
  { ordfield_field:> Field e plus mult inv zero one mult_inv
  ; ordfield_preorder: PreOrder leq
  ; ordfield_partialorder: PartialOrder e leq
  ; leq_plus: forall x y, leq x y -> forall z, leq (x + z) (y + z)
  ; leq_zero_mult: forall x, leq zero x -> forall y, leq 0 y -> leq 0 (x * y) }.

(* morphism classes: *)

Class SemiGroup_Morphism {A B Aeq Beq Aop Bop} (f: A -> B) :=
  { a_sg:> SemiGroup Aeq Aop
  ; b_sg:> SemiGroup Beq Bop
  ; sg_mor_op_proper:> Proper (Aeq ==> Beq) f
  ; preserves_sg_op: forall a a': A, f (a & a') == f a & f a' }.

Class Monoid_Morphism {A B Ae Be Aunit Bunit Amult Bmult} (f: A -> B) :=
  { monmor_a:> Monoid Ae Amult Aunit
  ; monmor_b:> Monoid Be Bmult Bunit
  ; monmor_sgmor:> @SemiGroup_Morphism A B _ _ _ _ f
  ; preserves_mon_unit: f mon_unit == mon_unit }.

Class Group_Morphism {A B Aeq Beq Aop Bop Aunit Bunit Ainv Binv} (f: A -> B):=
  { groupmor_a:> Group Aeq Aop Aunit Ainv
  ; groupmor_b:> Group Beq Bop Bunit Binv
  ; groupmor_monoidmor:> @Monoid_Morphism A B Aeq Beq Aunit Bunit Aop Bop f
  ; preserves_inv: forall x, f (- x) == - f x }.

Class SemiRing_Morphism {A B Ae Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f: A->B) :=
 { Aring:> SemiRing Ae Aplus Amult Azero Aone
 ; Bring:> SemiRing Be Bplus Bmult Bzero Bone
 ; semiringmor_plus_mor:> @Monoid_Morphism _ _ Ae Be Azero Bzero Aplus Bplus f
 ; semiringmor_mult_mor:> @Monoid_Morphism _ _ Ae Be Aone Bone Amult Bmult f }.

Class Ring_Morphism {A B Ae Aplus Amult Aopp Azero Aone Be Bplus Bmult Bopp Bzero Bone} (f: A->B) :=
 { ringmor_a:> Ring Ae Aplus Amult Aopp Azero Aone
 ; ringmor_b:> Ring Be Bplus Bmult Bopp Bzero Bone
 ; ringmor_groupmor:> @Group_Morphism A B _ _ Aplus Bplus Azero Bzero Aopp Bopp f
 ; ringmor_monoidmor:> @Monoid_Morphism A B _ _ Aone Bone Amult Bmult f }.
