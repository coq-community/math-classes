Require
  theory.fields stdlib_rationals.
Require Import
  QArith QSig
  abstract_algebra 
  interfaces.integers interfaces.rationals interfaces.additional_operations
  theory.rings theory.rationals.

Module QType_Rationals (Import anyQ: QType).

Module Import props := QProperties anyQ.

Instance QType_equiv: Equiv t := eq.
Instance QType_plus: RingPlus t := add.
Instance QType_0: RingZero t := zero.
Instance QType_1: RingOne t := one.
Instance QType_mult: RingMult t := mul.
Instance QType_opp: GroupInv t := opp.
Instance QType_mult_inv: MultInv t := λ x, inv (proj1_sig x).

Instance: Setoid t := {}.

Instance: ∀ x y: t, Decision (x = y) := λ x y,
  (match anyQ.eq_bool x y as p return p ≡ Qeq_bool (to_Q x) (to_Q y) → Decision (x = y) with
  | true => λ e, left _
  | false => λ e, right _
  end) (anyQ.spec_eq_bool x y).
    (* hm, do we really need the anyQ.spec_eq_bool in here? *)

Proof with intuition. apply Qeq_bool_iff... apply Qeq_bool_neq... Qed.

  (* We could get the above for free from the fact that anyQ.eq is just projected Qeq,
   but that mean that any comparison would involve two conversion to Q, which is
   a premature pessimization. *)

Ltac unfold_equiv := unfold equiv, QType_equiv, eq.

Add Ring Q : Qsrt.
Lemma anyQ_field_theory: field_theory zero one add mul sub opp div inv eq.
  (* No idea why this is missing in QSig. *)
Proof.
 constructor. 
    constructor; intros; qify; ring.
   exact neq_1_0.
  exact div_mul_inv.
 exact mul_inv_diag_l.
Qed.

Instance: Field t.
Proof. apply (fields.from_stdlib_field_theory anyQ_field_theory). Qed.

(* Type-classified facts about to_Q/of_Q: *)
Instance inject_QType_Q: Coerce t Q := to_Q.

Instance: Setoid_Morphism to_Q.
Proof. constructor; try apply _. intros x y. auto. Qed.

Instance: SemiRing_Morphism to_Q.
Proof. repeat (constructor; try apply _); intros; qify; reflexivity. Qed.

Instance inject_Q_QType: Coerce Q t := of_Q.
Instance: Inverse to_Q := of_Q.

Instance: Surjective to_Q.
Proof. constructor. intros x y E. rewrite <- E. apply spec_of_Q. apply _. Qed.

Instance: Injective to_Q.
Proof. constructor. auto. apply _. Qed.

Instance: Bijective to_Q := {}.

Instance: Inverse of_Q := to_Q.

Instance: Bijective of_Q.
Proof. apply jections.flip_bijection, _. Qed.

Instance: SemiRing_Morphism of_Q.
Proof. change (SemiRing_Morphism (to_Q⁻¹)). split; apply _. Qed.

Instance: RationalsToFrac t := iso_to_frac of_Q.
Instance: Rationals t := iso_is_rationals of_Q.

Program Instance Qtype_dec_mult_inv: DecMultInv t := inv.
Next Obligation.
  split; intros E. 
   rewrite commutativity. now apply mul_inv_diag_l.
  rewrite E. unfold_equiv. now qify.
Qed.

(* Order *)
Instance QType_le: Order t := le.

Instance: Proper ((=) ==> (=) ==> iff) QType_le.
Proof. 
  intros ? ? E1 ? ? E2. unfold QType_le, le, equiv, QType_equiv, eq in *. 
  now rewrite E1, E2.
Qed.

Instance: OrderEmbedding to_Q.
Proof. now repeat (split; try apply _). Qed.

Instance: RingOrder QType_le.
Proof rings.embed_ringorder to_Q.

Instance: TotalOrder QType_le.
Proof maps.embed_totalorder to_Q.

Lemma QType_lt_coincides x y : lt x y ↔ x < y.
Proof. unfold lt. now rewrite stdlib_rationals.Qlt_coincides. Qed.

(* Efficient comparison *)
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y, match (compare x y) with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Qcompare_spec (to_Q x) (to_Q y)); try discriminate.
  apply orders.not_precedes_sprecedes.
  now apply QType_lt_coincides.
Qed.

Next Obligation.
  rewrite spec_compare in *.
  destruct (Qcompare_spec (to_Q x) (to_Q y)); try discriminate; try intuition.
   now apply Zeq_le.
  now apply orders.sprecedes_weaken, QType_lt_coincides.
Qed.

(* Efficient [int_pow] *)
Program Instance QType_Zpow: Pow t Z := power.

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

Program Instance QType_Npow: Pow t N := λ x n, power x (Z_of_N n).

Instance: NatPowSpec t N QType_Npow.
Proof.
  split; unfold "^", QType_Npow.
    solve_proper.
   intros. rewrite preserves_0. apply int_pow_0.
  intros ? ?. rewrite preserves_plus, preserves_1.
  apply int_pow.int_pow_S_nonneg.
  apply naturals.to_semiring_nonneg.
Qed.

End QType_Rationals.
