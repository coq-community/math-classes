Require
  stdlib_binary_integers theory.integers orders.semirings.
Require Import
  ZSig ZSigZAxioms NArith ZArith
  nonneg_integers_naturals interfaces.orders
  abstract_algebra interfaces.integers interfaces.additional_operations.

Module ZType_Integers (Import anyZ: ZType).

Module axioms := ZTypeIsZAxioms anyZ.

Instance ZType_equiv : Equiv t := eq.
Instance ZType_plus : Plus t := add.
Instance ZType_0 : Zero t := zero.
Instance ZType_1 : One t := one.
Instance ZType_mult : Mult t := mul.
Instance ZType_negate: Negate t := opp.

Instance: Setoid t | 10 := {}.

Program Instance: ∀ x y: t, Decision (x = y) := λ x y,
  match compare x y with
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  apply Zcompare_Eq_eq. now rewrite <-spec_compare.
Qed.
Next Obligation.
  rewrite spec_compare in *.
  intros E.
  apply Zcompare_Eq_iff_eq in E. auto.
Qed.

Ltac unfold_equiv := unfold equiv, ZType_equiv, eq in *.

Lemma ZType_ring_theory: ring_theory zero one add mul sub opp eq.
Proof. repeat split; repeat intro; axioms.zify; auto with zarith. Qed.

Local Instance: Ring t := rings.from_stdlib_ring_theory ZType_ring_theory.

Instance inject_ZType_Z: Cast t Z := to_Z.

Instance: Proper ((=) ==> (=)) to_Z.
Proof. intros x y E. easy. Qed.

Instance: SemiRing_Morphism to_Z.
Proof.
  repeat (split; try apply _).
     exact spec_add.
    exact spec_0.
   exact spec_mul.
  exact spec_1.
Qed.

Instance inject_Z_ZType: Cast Z t := of_Z.
Instance: Inverse to_Z := of_Z.

Instance: Surjective to_Z.
Proof. constructor. intros x y E. rewrite <- E. apply spec_of_Z. apply _. Qed.

Instance: Injective to_Z.
Proof. constructor. unfold_equiv. intuition. apply _. Qed.

Instance: Bijective to_Z := {}.

Instance: Inverse of_Z := to_Z.

Instance: Bijective of_Z.
Proof. apply jections.flip_bijection. Qed.

Instance: SemiRing_Morphism of_Z.
Proof. change (SemiRing_Morphism (to_Z⁻¹)). split; apply _. Qed.

Instance: IntegersToRing t := integers.retract_is_int_to_ring of_Z.
Instance: Integers t := integers.retract_is_int of_Z.

(* Order *)
Instance ZType_le: Le t := le.
Instance ZType_lt: Lt t := lt.

Instance: Proper ((=) ==> (=) ==> iff) ZType_le.
Proof.
  intros ? ? E1 ? ? E2. unfold ZType_le, le. unfold equiv, ZType_equiv, eq in *.
  now rewrite E1, E2.
Qed.

Instance: SemiRingOrder ZType_le.
Proof. now apply (rings.projected_ring_order to_Z). Qed.

Instance: OrderEmbedding to_Z.
Proof. now repeat (split; try apply _). Qed.

Instance: TotalRelation ZType_le.
Proof. now apply (maps.projected_total_order to_Z). Qed.

Instance: FullPseudoSemiRingOrder ZType_le ZType_lt.
Proof.
  rapply semirings.dec_full_pseudo_srorder.
  intros x y.
  change (to_Z x < to_Z y ↔ x ≤ y ∧ x ≠ y).
  now rewrite orders.lt_iff_le_ne.
Qed.

(* Efficient comparison *)
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y,
  match compare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  now apply orders.lt_not_le_flip.
Qed.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate; try intuition.
   now apply Zeq_le.
  now apply orders.lt_le.
Qed.

Program Instance: Abs t := abs.
Next Obligation.
  split; intros E; unfold_equiv; rewrite spec_abs.
   apply Z.abs_eq.
   apply (order_preserving to_Z) in E.
   now rewrite rings.preserves_0 in E.
  rewrite rings.preserves_negate.
  apply Z.abs_neq.
  apply (order_preserving to_Z) in E.
  now rewrite rings.preserves_0 in E.
Qed.

(* Efficient division *)
Instance ZType_div: DivEuclid t := anyZ.div.
Instance ZType_mod: ModEuclid t := modulo.

Instance: EuclidSpec t ZType_div ZType_mod.
Proof.
  split; try apply _; unfold div_euclid, ZType_div.
     intros x y E. now apply axioms.div_mod.
    intros x y Ey.
    destruct (Z_mod_remainder (to_Z x) (to_Z y)) as [[Hl Hr] | [Hl Hr]].
      intro. apply Ey. apply (injective to_Z). now rewrite rings.preserves_0.
     left; split.
      apply (order_reflecting to_Z). now rewrite spec_modulo, rings.preserves_0.
     apply (strictly_order_reflecting to_Z). now rewrite spec_modulo.
    right; split.
      apply (strictly_order_reflecting to_Z). now rewrite spec_modulo.
     apply (order_reflecting to_Z). now rewrite spec_modulo, rings.preserves_0.
   intros x. unfold_equiv. rewrite spec_div, rings.preserves_0. now apply Zdiv_0_r.
  intros x. unfold_equiv. rewrite spec_modulo, rings.preserves_0. now apply Zmod_0_r.
Qed.

Lemma ZType_succ_1_plus x : succ x = 1 + x.
Proof.
  unfold_equiv. rewrite spec_succ, rings.preserves_plus, rings.preserves_1.
  now rewrite commutativity.
Qed.

Lemma ZType_two_2 : two = 2.
Proof.
  unfold_equiv. rewrite spec_2.
  now rewrite rings.preserves_plus, rings.preserves_1.
Qed.

(* Efficient [nat_pow] *)
Program Instance ZType_pow: Pow t (t⁺) := pow.

Instance: NatPowSpec t (t⁺) ZType_pow.
Proof.
  split.
    intros x1 y1 E1 [x2] [y2] E2.
    now apply axioms.pow_wd.
   intros x1. apply axioms.pow_0_r.
  intros x [n ?].
  unfold_equiv. unfold "^", ZType_pow. simpl.
  rewrite <-axioms.pow_succ_r; try easy.
  now rewrite ZType_succ_1_plus.
Qed.

Program Instance ZType_Npow: Pow t N := pow_N.

Instance: NatPowSpec t N ZType_Npow.
Proof.
  split; unfold "^", ZType_Npow.
    intros x1 y1 E1 x2 y2 E2. unfold_equiv.
    now rewrite 2!spec_pow_N, E1, E2.
   intros x1. unfold_equiv.
   now rewrite spec_pow_N, rings.preserves_1.
  intros x n. unfold_equiv.
  rewrite spec_mul, 2!spec_pow_N.
  rewrite rings.preserves_plus, Z.pow_add_r.
    now rewrite rings.preserves_1, Z.pow_1_r.
   easy.
  now apply Z_of_N_le_0.
Qed.

(*
(* Efficient [log 2] *)
Program Instance: Log (2:t) (t⁺) := log2.
Next Obligation with auto.
  intros x.
  apply to_Z_Zle_sr_le.
  rewrite spec_log2, preserves_0.
  apply Z.log2_nonneg.
Qed.

Next Obligation with auto.
  intros [x Ex].
  destruct (axioms.log2_spec x) as [E1 E2].
   apply to_Z_sr_le_Zlt...
  unfold nat_pow, nat_pow_sig, ZType_pow; simpl.
  apply to_Z_Zle_sr_le in E1. apply to_Z_Zlt_sr_le in E2.
  rewrite ZType_two_2 in E1, E2.
  rewrite ZType_succ_plus_1, commutativity in E2...
Qed.
*)

(* Efficient [shiftl] *)
Program Instance ZType_shiftl: ShiftL t (t⁺) := shiftl.

Instance: ShiftLSpec t (t⁺) ZType_shiftl.
Proof.
  apply shiftl_spec_from_nat_pow.
  intros x [y Ey].
  unfold additional_operations.pow, ZType_pow, additional_operations.shiftl, ZType_shiftl.
  unfold_equiv. simpl.
  rewrite rings.preserves_mult, spec_pow.
  rewrite spec_shiftl, Z.shiftl_mul_pow2.
   now rewrite <-ZType_two_2, spec_2.
  apply (order_preserving to_Z) in Ey. now rewrite rings.preserves_0 in Ey.
Qed.

(* Efficient [shiftr] *)
Program Instance: ShiftR t (t⁺) := shiftr.

End ZType_Integers.
