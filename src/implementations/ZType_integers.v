Require Import 
  ZSig ZSigZAxioms 
  ZArith
  Sumbool 
  Program
  Morphisms
  interfaces.integers 
  abstract_algebra
  positive_integers_naturals
  orders.semiring
  signed_binary_positive_integers
  rings
  theory.integers.

Module ZType_Integers (Import anyZ: ZType).

Module axioms := ZTypeIsZAxioms anyZ.

Instance anyZ_eq : Equiv t := eq.
Instance: RingPlus t := add.
Instance anyZ_0: RingZero t := zero.
Instance anyZ_1: RingOne t := one.
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

Lemma anyZ_ring_theory: ring_theory zero one add mul sub opp eq.
Proof.
  repeat split; repeat intro; axioms.zify; auto with zarith.
Qed.

Instance: Ring t.
Proof.
  apply (@rings.from_stdlib_ring_theory.from_stdlib_ring_theory
    t _ _ _ _ _ _ _ anyZ_ring_theory); apply _.
Qed.

Program Instance: RingMinus t := sub.
Next Obligation.
  unfold_equiv.
  rewrite spec_add. rewrite spec_opp.
  apply spec_sub.
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
  unfold mon_unit at 2. unfold anyZ_0. rewrite spec_0. rewrite spec_of_Z...
  rewrite spec_opp. repeat rewrite spec_of_Z...
  rewrite spec_mul. repeat rewrite spec_of_Z...
  unfold mon_unit. unfold anyZ_1. rewrite spec_1. rewrite spec_of_Z...
Qed.

Global Instance: IntegersToRing t := theory.integers.retract_is_int_to_ring to_Z.
Global Instance: Integers t := theory.integers.retract_is_int of_Z to_Z of_Z_to_Z.

Lemma to_Z_sr_precedes_Zle x y : (to_Z x <= to_Z y)%Z → x ≤ y.
Proof.
  intro.
  rewrite <-of_Z_to_Z, <-(of_Z_to_Z y). 
  apply (integers.preserve_sr_order of_Z).
  apply Zle_sr_precedes. assumption.
Qed.

Lemma to_Z_Zle_sr_precedes x y : x ≤ y → (to_Z x <= to_Z y)%Z.
Proof.
  intro E.
  apply sr_precedes_Zle.
  apply (integers.preserve_sr_order to_Z). assumption.
Qed.

Global Program Instance: IntAbs t (ZPos t) := abs.
Next Obligation.
  apply to_Z_sr_precedes_Zle.
  rewrite spec_abs.
  rewrite preserves_0.
  apply Zabs_pos.
Qed.

Next Obligation with auto.
  rewrite ZPos_to_semiring_self.
  unfold_equiv. 
  rewrite preserves_opp.
  rewrite spec_abs.
  destruct (Zabs_dec (to_Z x))...
Qed.

Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y, match (compare x y) with
  | Lt => left _
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  apply to_Z_sr_precedes_Zle.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  apply Zlt_le_weak. assumption.
Qed.

Next Obligation.
  apply to_Z_sr_precedes_Zle.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  apply Zeq_le. assumption.
Qed.

(* This proof is ugly, clean it up? *)
Next Obligation with auto.
  intros E.
  apply to_Z_Zle_sr_precedes in E.
  rewrite spec_compare in *.
  destruct (Zle_lt_or_eq (to_Z x) (to_Z y) E) as [E2 | E2].
  assert (E2a:=Zlt_compare (to_Z x) (to_Z y) E2). 
    destruct ((to_Z x ?= to_Z y)%Z)...
  rewrite E2 in *. rename H into H. (* fix the dirty name *)
  apply H. symmetry. apply Zcompare_refl.
Qed.

Next Obligation.
  split; intro; discriminate.
Qed.

End ZType_Integers.
