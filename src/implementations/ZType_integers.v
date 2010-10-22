Require 
  rings
  theory.integers
  signed_binary_positive_integers.

Require Import 
  ZSig ZSigZAxioms 
  ZArith
  Sumbool 
  Program
  Morphisms
  interfaces.integers 
  abstract_algebra.

Module ZType_Integers (Import anyZ: ZType).

Module axioms := ZTypeIsZAxioms anyZ.

Instance anyZ_eq : Equiv t := eq.
Instance: RingPlus t := add.
Instance anyZ_zero: RingZero t := zero.
Instance anyZ_one: RingOne t := one.
Instance: RingMult t := mul.
Instance: GroupInv t := opp.

Instance: Setoid t.

Instance: ∀ x y: t, Decision (x = y). 
Proof with auto.
   intros x y. 
   destruct (Sumbool.sumbool_of_bool (eq_bool x y)).
   left. apply Zeq_bool_eq. rewrite <-spec_eq_bool...
   right. apply Zeq_bool_neq. rewrite <-spec_eq_bool...
Qed.

Ltac unfold_equiv := unfold equiv, anyZ_eq, eq.

Program Instance: RingMinus t := sub.
Next Obligation.
  unfold_equiv.
  rewrite spec_add. rewrite spec_opp.
  apply spec_sub.
Qed.

Lemma anyZ_ring_theory: ring_theory zero one add mul sub opp eq.
Proof.
  repeat split; repeat intro; axioms.zify; auto with zarith.
Qed.

Instance: Ring t.
Proof.
  apply (@rings.from_stdlib_ring_theory.from_stdlib_ring_theory
    t _ _ _ _ _ _ _ anyZ_ring_theory); apply _.
Qed.

Instance: Ring_Morphism to_Z.
Proof with try apply _; auto.
  repeat (split; try apply _); repeat intro...
  apply spec_add... 
  apply spec_0...
  apply spec_opp...
  apply spec_mul... 
  apply spec_1...
Qed.

Lemma of_Z_to_Z x : of_Z (to_Z x) = x.
Proof.
  unfold_equiv.
  rewrite spec_of_Z. auto.
Qed.

Instance: Proper (equiv ==> equiv) of_Z.
Proof.
  repeat intro. rewrite H. (* slow *)
  reflexivity.
Qed.

Instance: Ring_Morphism of_Z.
Proof with try apply _; auto.
  repeat (split; try apply _); repeat intro; unfold_equiv. 
  rewrite spec_add. repeat rewrite spec_of_Z...
  unfold mon_unit at 2. unfold anyZ_zero. rewrite spec_0. rewrite spec_of_Z...
  rewrite spec_opp. repeat rewrite spec_of_Z...
  rewrite spec_mul. repeat rewrite spec_of_Z...
  unfold mon_unit. unfold anyZ_one. rewrite spec_1. rewrite spec_of_Z...
Qed.

Instance: IntegersToRing t := theory.integers.retract_is_int_to_ring to_Z.
Instance: Integers t := theory.integers.retract_is_int of_Z to_Z of_Z_to_Z.
End ZType_Integers.