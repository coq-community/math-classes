Require
  MathClasses.theory.fields MathClasses.implementations.stdlib_rationals MathClasses.theory.int_pow.
From Coq Require Import QArith.
Require Import
  Bignums.SpecViaQ.QSig
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders
  MathClasses.interfaces.integers MathClasses.interfaces.rationals MathClasses.interfaces.additional_operations
  MathClasses.theory.rings MathClasses.theory.rationals.

Module QType_Rationals (Import anyQ: QType).

Module Import props := QProperties anyQ.

#[global]
Instance QType_equiv: Equiv t := eq.
#[global]
Instance QType_plus: Plus t := add.
#[global]
Instance QType_0: Zero t := zero.
#[global]
Instance QType_1: One t := one.
#[global]
Instance QType_mult: Mult t := mul.
#[global]
Instance QType_negate: Negate t := opp.
#[global]
Instance QType_dec_recip: DecRecip t := inv.

#[global]
Instance: Setoid t := {}.

#[global]
Instance: ∀ x y: t, Decision (x = y).
Proof with intuition.
refine (λ x y,
  (match anyQ.eq_bool x y as p return p ≡ Qeq_bool (to_Q x) (to_Q y) → Decision (x = y) with
  | true => λ e, left _
  | false => λ e, right _
  end) (anyQ.spec_eq_bool x y)).
    (* hm, do we really need the anyQ.spec_eq_bool in here? *)

apply Qeq_bool_iff... apply Qeq_bool_neq... Qed.

  (* We could get the above for free from the fact that anyQ.eq is just projected Qeq,
   but that mean that any comparison would involve two conversion to Q, which is
   a premature pessimization. *)

Ltac unfold_equiv := unfold equiv, QType_equiv, eq.

Add Ring Q : Qsrt.
Lemma anyQ_field_theory: field_theory zero one add mul sub opp anyQ.div inv eq.
  (* No idea why this is missing in QSig. *)
Proof.
 constructor.
    constructor; intros; qify; ring.
   exact neq_1_0.
  exact div_mul_inv.
 exact mul_inv_diag_l.
Qed.

#[global]
Instance: DecField t.
Proof.
  refine (dec_fields.from_stdlib_field_theory anyQ_field_theory _).
  unfold eq. now rewrite spec_inv, spec_0.
Qed.

(* Type-classified facts about to_Q/of_Q: *)
#[global]
Instance inject_QType_Q: Cast t Q := to_Q.

#[global]
Instance: Setoid_Morphism to_Q.
Proof. constructor; try apply _. intros x y. auto. Qed.

#[global]
Instance: SemiRing_Morphism to_Q.
Proof. repeat (constructor; try apply _); intros; qify; reflexivity. Qed.

#[global]
Instance inject_Q_QType: Cast Q t := of_Q.
#[global]
Instance: Inverse to_Q := of_Q.

#[global]
Instance: Surjective to_Q.
Proof. constructor. intros x y E. rewrite <- E. apply spec_of_Q. apply _. Qed.

#[global]
Instance: Injective to_Q.
Proof. constructor. auto. apply _. Qed.

#[global]
Instance: Bijective to_Q := {}.

#[global]
Instance: Inverse of_Q := to_Q.

#[global]
Instance: Bijective of_Q.
Proof. apply jections.flip_bijection. Qed.

#[global]
Instance: SemiRing_Morphism of_Q.
Proof. change (SemiRing_Morphism (to_Q⁻¹)). split; apply _. Qed.

#[global]
Instance: RationalsToFrac t := iso_to_frac of_Q.
#[global]
Instance: Rationals t := iso_is_rationals of_Q.

(* Order *)
#[global]
Instance QType_le: Le t := le.
#[global]
Instance QType_lt: Lt t := lt.

#[global]
Instance: Proper ((=) ==> (=) ==> iff) QType_le.
Proof.
  intros ? ? E1 ? ? E2. unfold QType_le, le, equiv, QType_equiv, eq in *.
  now rewrite E1, E2.
Qed.

#[global]
Instance: SemiRingOrder QType_le.
Proof. now apply (rings.projected_ring_order to_Q). Qed.

#[global]
Instance: OrderEmbedding to_Q.
Proof. now repeat (split; try apply _). Qed.

#[global]
Instance: TotalRelation QType_le.
Proof. now apply (maps.projected_total_order to_Q). Qed.

#[global]
Instance: FullPseudoSemiRingOrder QType_le QType_lt.
Proof.
  rapply semirings.dec_full_pseudo_srorder.
  intros x y.
  change (to_Q x < to_Q y ↔ x ≤ y ∧ x ≠ y).
  now rewrite orders.lt_iff_le_ne.
Qed.

(* Efficient comparison *)
#[global]
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y,
  match compare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Qcompare_spec (to_Q x) (to_Q y)); try discriminate.
  now apply orders.lt_not_le_flip.
Qed.

Next Obligation.
  rewrite spec_compare in *.
  destruct (Qcompare_spec (to_Q x) (to_Q y)); try discriminate; try intuition.
   now apply Zorder.Zeq_le.
  now apply orders.lt_le.
Qed.

(* Efficient [int_pow] *)
#[global]
Program Instance QType_Zpow: Pow t Z := power.

#[global]
Instance: IntPowSpec t Z QType_Zpow.
Proof.
  split; try apply _; unfold_equiv.
    intros. now rewrite spec_power, preserves_1.
   intros. rewrite spec_power, preserves_0.
   now apply int_pow_base_0.
  intros ? ? E. rewrite preserves_mult, 2!spec_power.
  rewrite preserves_0 in E.
  now apply int_pow_S.
Qed.

#[global]
Program Instance QType_Npow: Pow t N := λ x n, power x (Z_of_N n).

#[global]
Instance: NatPowSpec t N QType_Npow.
Proof.
  split; unfold "^", QType_Npow.
    solve_proper.
   intros. rewrite preserves_0. apply int_pow_0.
  intros ? ?. rewrite preserves_plus, preserves_1.
  apply int_pow.int_pow_S_nonneg.
  apply nat_int.to_semiring_nonneg.
Qed.

End QType_Rationals.
