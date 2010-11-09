Require orders.orders signed_binary_positive_integers.
Require Import 
  ZSig ZSigZAxioms ZArith Program Morphisms
  positive_integers_naturals 
  abstract_algebra interfaces.integers interfaces.additional_operations
  theory.rings theory.integers theory.additional_operations
  orders.semiring.  

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
  intros x y E. rewrite E. (* slow *)
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

(* Efficient minus *)
Global Program Instance: RingMinus t := sub.
Next Obligation.
  unfold_equiv.
  rewrite spec_add. rewrite spec_opp.
  apply spec_sub.
Qed.

(* Relation between Zorder and ≤ *)
Lemma to_Z_sr_precedes_Zle x y : x ≤ y → (to_Z x <= to_Z y)%Z.
Proof.
  intro E.
  apply signed_binary_positive_integers.sr_precedes_Zle.
  apply (integers.preserve_sr_order to_Z). assumption.
Qed.

Lemma to_Z_Zle_sr_precedes x y : (to_Z x <= to_Z y)%Z → x ≤ y.
Proof.
  intro.
  rewrite <-of_Z_to_Z, <-(of_Z_to_Z y). 
  apply (integers.preserve_sr_order of_Z).
  apply signed_binary_positive_integers.Zle_sr_precedes. assumption.
Qed.

Lemma to_Z_sr_precedes_Zlt x y : x < y → (to_Z x < to_Z y)%Z.
Proof with auto.
  intros [E1 E2].
  destruct (Zorder.Zle_lt_or_eq (to_Z x) (to_Z y))... apply to_Z_sr_precedes_Zle...
  contradiction.
Qed.

Lemma to_Z_Zlt_sr_precedes x y : (to_Z x < to_Z y)%Z → x < y.
Proof with auto.
  intro E.
  split. apply to_Z_Zle_sr_precedes, Zorder.Zlt_le_weak...
  apply Zorder.Zlt_not_eq...
Qed.

(* Efficient comparison *)
Global Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y, match (compare x y) with
  | Lt => left _
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  apply to_Z_Zle_sr_precedes.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  apply Zlt_le_weak. assumption.
Qed.

Next Obligation.
  apply to_Z_Zle_sr_precedes.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  apply Zeq_le. assumption.
Qed.

(* This proof is ugly, clean it up? *)
Next Obligation with auto.
  intros E.
  apply to_Z_sr_precedes_Zle in E.
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

Global Program Instance: IntAbs t (ZPos t) := abs.
Next Obligation.
  apply to_Z_Zle_sr_precedes.
  rewrite spec_abs.
  rewrite preserves_0.
  apply Zabs_pos.
Qed.

Next Obligation with auto.
  rewrite ZPos_to_semiring_self.
  unfold_equiv. 
  rewrite (preserves_opp (abs x)).
  rewrite spec_abs.
  destruct (Zabs_dec (to_Z x))...
Qed.

(* Efficient division *)
Global Instance Ztype_euclid (x :t) (y : {z : t | z ≠ 0}) : Euclid x y (div x (`y)) (modulo x (`y)).
Proof with auto.
  destruct y as [y Ey].
  split; simpl.
  apply axioms.div_mod. intro E. apply Ey. apply E.
  destruct (Z_mod_remainder (to_Z x) (to_Z y)) as [[Hl Hr] | [Hl Hr]].
  intro. apply Ey. apply (injective to_Z). rewrite preserves_0...
  left; split.
  apply to_Z_Zle_sr_precedes. rewrite spec_modulo, preserves_0...
  apply to_Z_Zlt_sr_precedes. rewrite spec_modulo... 
  right; split.
  apply to_Z_Zlt_sr_precedes. rewrite spec_modulo...
  apply to_Z_Zle_sr_precedes. rewrite spec_modulo, preserves_0...
Qed.

Obligation Tactic := idtac.
Global Program Instance: DivEuclid t := div.
Next Obligation.
  intros x y. exists (modulo x (`y)). apply _.
Qed.

Global Program Instance: ModEuclid t := modulo.
Next Obligation.
  intros x y. exists (div x (`y)). apply _.
Qed.

Lemma ZType_succ_plus_1 x : succ x = 1 + x.
Proof.
  unfold_equiv. rewrite spec_succ, preserves_plus, preserves_1. 
  rewrite commutativity. reflexivity.
Qed.

Lemma ZType_two_2 : two = 2.
Proof.
  unfold_equiv. rewrite spec_2. unfold "2". 
  rewrite preserves_plus, preserves_1.
  reflexivity.
Qed.

(* Efficient nat_pow *)
Global Program Instance anyZ_pow: NatPow t (ZPos t) := pow.
Next Obligation with try reflexivity; auto.
  intros x n. 
  change (nat_pow_spec x n ((λ x n, pow x (`n)) x n)). (* This is stupid ... *)
  apply nat_pow_spec_from_properties.
  intros x1 y1 E1 [x2 Ex2] [y2 Ey2] E2. 
  unfold equiv, sig_equiv, sig_relation in E2. simpl in *. rewrite E1, E2... 
  intros x1. rewrite preserves_0.  rewrite axioms.pow_0_r...
  intros x1 n1. rewrite preserves_plus, preserves_1. 
  rewrite <-axioms.pow_succ_r. rewrite ZType_succ_plus_1...
  destruct n1. simpl. apply to_Z_sr_precedes_Zle...
Qed.

(* Efficient log2 *)
Global Program Instance: Log (2:t) (ZPos t) := log2.
Next Obligation with auto.
  intros x. 
  apply to_Z_Zle_sr_precedes.
  rewrite spec_log2, preserves_0.
  apply Z.log2_nonneg.
Qed.

Next Obligation with auto.
  intros [x Ex]. 
  destruct (axioms.log2_spec x) as [E1 E2].
    apply to_Z_sr_precedes_Zlt...
  unfold nat_pow, nat_pow_sig, anyZ_pow; simpl.
  split. 
  apply to_Z_Zle_sr_precedes. rewrite <-ZType_two_2...
  apply to_Z_Zlt_sr_precedes. rewrite ZType_succ_plus_1, commutativity, ZType_two_2 in E2...
Qed.

End ZType_Integers.
