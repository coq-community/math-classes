Require 
  orders.integers signed_binary_positive_integers.
Require Import 
  ZSig ZSigZAxioms ZArith Program Morphisms
  nonneg_integers_naturals 
  abstract_algebra interfaces.integers interfaces.additional_operations
  theory.rings theory.integers theory.nat_pow
  orders.semirings.  

Module ZType_Integers (Import anyZ: ZType).

Module axioms := ZTypeIsZAxioms anyZ.

(* 
   We use the following inductive type to hide the actual notion of equality on [t]. 
   This is needed because [vm_compute] will otherwise evaluate proofs...
   For example, consider [@decide (eq x y) (Decide_instance x y)]. Here 
   [eq x y] is defined as [Zeq (to_Z x) (to_Z y)] and hence vm_compute will 
   evaluate [to_Z x] and [to_Z y]. This is obviously painfully slow and unnecessary.
*)
Inductive ZType_eq' (x y: t) : Prop := mk_ZType_eq' : eq x y → ZType_eq' x y.

Lemma ZType_eq_correct x y : eq x y ↔ ZType_eq' x y.
Proof. intuition. Qed.

Lemma ZType_neq_correct x y : ~eq x y ↔ ~ZType_eq' x y.
Proof. split; intros E F; apply E, ZType_eq_correct; assumption. Qed.

Ltac rewrite_equiv := repeat rewrite <-ZType_eq_correct in *; repeat rewrite <-ZType_neq_correct in *.

Instance ZType_eq : Equiv t := ZType_eq'.
Instance ZType_plus : RingPlus t := add.
Instance ZType_0 : RingZero t := zero.
Instance ZType_1 : RingOne t := one.
Instance ZType_mult : RingMult t := mul.
Instance ZType_inv: GroupInv t := opp.

Instance: Setoid t | 10.
Proof with auto.
  repeat split; rewrite_equiv. 
   symmetry...
  transitivity y...
Qed.

Program Instance: ∀ x y: t, Decision (x = y) := λ x y, match (compare x y) with
  | Eq => left _
  | _ => right _
  end.
Next Obligation. 
  apply ZType_eq_correct, Zcompare_Eq_eq. rewrite <-spec_compare. auto. 
Qed.
Next Obligation. 
  rewrite spec_compare in *.
  rewrite_equiv. intros E. 
  apply Zcompare_Eq_iff_eq in E. auto.
Qed.

Ltac unfold_equiv := rewrite_equiv; unfold equiv, ZType_eq, eq in *.

Lemma ZType_ring_theory: ring_theory zero one add mul sub opp ZType_eq.
Proof.
  repeat split; repeat intro; axioms.zify; auto with zarith.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) ZType_plus. 
Proof. intros x1 y1 E1 x2 y2 E2. rewrite_equiv. rewrite E1, E2. reflexivity. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) ZType_mult. 
Proof. intros x1 y1 E1 x2 y2 E2. rewrite_equiv. rewrite E1, E2. reflexivity. Qed.

Instance: Proper ((=) ==> (=)) ZType_inv. 
Proof. intros x1 y1 E1. rewrite_equiv. rewrite E1. reflexivity. Qed.

Instance: Ring t | 10 := rings.from_stdlib_ring_theory ZType_ring_theory.

Instance: Proper ((=) ==> (=)) of_Z.
Proof. intros x y E. unfold_equiv. repeat f_equal. assumption. Qed.

Instance: Proper ((=) ==> (=)) to_Z. 
Proof. intros x y E. unfold_equiv. auto. Qed.

Instance: SemiRing_Morphism to_Z.
Proof with try apply _; auto.
  repeat (split; try apply _); unfold equiv; repeat intro...
     apply spec_add... 
    apply spec_0...
   apply spec_mul... 
  apply spec_1...
Qed.

Instance: Inverse to_Z := of_Z.

Instance: Surjective to_Z.
Proof. constructor. intros x y E. rewrite <- E. apply spec_of_Z. apply _. Qed.

Instance: Injective to_Z.
Proof. constructor. unfold_equiv. intuition. apply _. Qed.

Instance: Bijective to_Z.

Instance: Inverse of_Z := to_Z.

Instance: Bijective of_Z.
Proof. apply jections.flip_bijection, _. Qed.

Instance: SemiRing_Morphism of_Z.
Proof. change (SemiRing_Morphism (inverse to_Z)). split; apply _. Qed.

Instance: IntegersToRing t := retract_is_int_to_ring of_Z.
Instance: Integers t := retract_is_int of_Z.

(* Relation between Zorder and ≤ *)
Lemma to_Z_sr_precedes_Zle x y : x ≤ y → (to_Z x <= to_Z y)%Z.
Proof.
  intro E.
  pose proof (order_preserving to_Z) as P. apply P. auto.
Qed.

Lemma to_Z_Zle_sr_precedes x y : (to_Z x <= to_Z y)%Z → x ≤ y.
Proof.
  intro. 
  rewrite <-(jections.surjective_applied' of_Z x), <-(jections.surjective_applied' of_Z y). 
  pose proof (order_preserving of_Z) as P. apply P. assumption. 
Qed.

Lemma to_Z_sr_precedes_Zlt x y : x < y → (to_Z x < to_Z y)%Z.
Proof with intuition.
  intros [E1 E2]. unfold_equiv.
  destruct (Zorder.Zle_lt_or_eq (to_Z x) (to_Z y))... 
  apply to_Z_sr_precedes_Zle...
Qed.

Lemma to_Z_Zlt_sr_precedes x y : (to_Z x < to_Z y)%Z → x < y.
Proof with auto.
  intro E.
  split. apply to_Z_Zle_sr_precedes, Zorder.Zlt_le_weak...
  unfold_equiv. apply Zorder.Zlt_not_eq...
Qed.

(* Efficient comparison *)
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y, match (compare x y) with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  apply orders.not_precedes_sprecedes.
  apply to_Z_Zlt_sr_precedes. assumption.
Qed.

Next Obligation with intuition.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate...
  apply to_Z_Zle_sr_precedes, Zeq_le...
  apply orders.sprecedes_weaken, to_Z_Zlt_sr_precedes...
Qed.

Program Instance: IntAbs t (t⁺) := abs.
Next Obligation.
  apply to_Z_Zle_sr_precedes.
  rewrite spec_abs.
  rewrite preserves_0.
  apply Zabs_pos.
Qed.

Next Obligation with auto.
  rewrite <-(naturals.to_semiring_unique NonNeg_inject). simpl.
  unfold_equiv. 
  rewrite (preserves_inv (abs x)).
  rewrite spec_abs.
  destruct (Zabs_dec (to_Z x))...
Qed.

Program Instance: Abs t := abs.
Next Obligation with trivial.
  split; intros E; unfold_equiv; rewrite spec_abs.
   apply Z.abs_eq...
   apply to_Z_sr_precedes_Zle in E. rewrite preserves_0 in E...
  apply to_Z_sr_precedes_Zle in E. rewrite preserves_0 in E...
  rewrite preserves_inv.
  apply Z.abs_neq...
Qed.

(* Efficient division *)
Lemma Ztype_euclid (x : t) (y : {z : t | z ≠ 0}) : Euclid x y (div x (`y)) (modulo x (`y)).
Proof with auto.
  destruct y as [y Ey].
  split; simpl.
   unfold_equiv.
   apply axioms.div_mod...
  destruct (Z_mod_remainder (to_Z x) (to_Z y)) as [[Hl Hr] | [Hl Hr]].
    intro. apply Ey. apply (injective to_Z). rewrite preserves_0...
   left; split.
    apply to_Z_Zle_sr_precedes. rewrite spec_modulo, preserves_0...
   apply to_Z_Zlt_sr_precedes. rewrite spec_modulo...
  right; split.
   apply to_Z_Zlt_sr_precedes. rewrite spec_modulo...
  apply to_Z_Zle_sr_precedes. rewrite spec_modulo, preserves_0...
Qed. 

Local Obligation Tactic := idtac.
Program Instance: DivEuclid t := div.
Next Obligation.
  intros x y. exists (modulo x (`y)). apply Ztype_euclid.
Qed.

Program Instance: ModEuclid t := modulo.
Next Obligation.
  intros x y. exists (div x (`y)). apply Ztype_euclid.
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

(* Efficient [nat_pow] *)
Instance: Proper ((=) ==> (=) ==> (=)) pow. 
Proof. intros x1 y1 E1 x2 y2 E2. rewrite_equiv. rewrite E1, E2. reflexivity. Qed.

Program Instance ZType_pow: NatPow t (t⁺) := pow.
Next Obligation with try reflexivity; auto.
  intros x n. 
  change (nat_pow_spec x n ((λ x n, pow x (`n)) x n)). (* This is stupid... pattern is not helpful either *)
  apply nat_pow_spec_from_properties.
    intros x1 y1 E1 [x2 Ex2] [y2 Ey2] E2. 
    unfold equiv, NonNeg_equiv in E2. simpl in *. rewrite_equiv.
    rewrite E1, E2... 
   intros x1. unfold_equiv. apply axioms.pow_0_r.
  intros x1 [n1 En1]. simpl. unfold_equiv. 
  rewrite <-ZType_succ_plus_1.
  apply axioms.pow_succ_r.
  apply to_Z_sr_precedes_Zle...
Qed.

(* Efficient [log 2] *)
Program Instance: Log (2:t) (t⁺) := log2.
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
  unfold nat_pow, nat_pow_sig, ZType_pow; simpl.
  apply to_Z_Zle_sr_precedes in E1. apply to_Z_Zlt_sr_precedes in E2.
  rewrite ZType_two_2 in E1, E2. 
  rewrite ZType_succ_plus_1, commutativity in E2...
Qed.

(* Efficient [shiftl] *)
Program Instance: ShiftLeft t (t⁺) := λ x y, shiftl x y.
Next Obligation.
  intros x [y Ey].
  unfold additional_operations.pow, nat_pow, nat_pow_sig, ZType_pow.
  unfold_equiv. simpl.
  rewrite rings.preserves_mult, spec_pow.
  rewrite spec_shiftl, Z.shiftl_mul_pow2.
   rewrite <-ZType_two_2, spec_2. reflexivity.
  apply to_Z_sr_precedes_Zle in Ey. rewrite preserves_0 in Ey. assumption.
Qed. 
(* This proof could possibly be much shorter by using the correctness of shiftl on Z *)

Program Instance: ShiftRight t (t⁺) := λ x y, shiftr x y.
Next Obligation. 
Admitted.

End ZType_Integers.
