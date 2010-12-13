Require
  theory.fields stdlib_rationals.
Require Import
  QArith QSig
  abstract_algebra 
  natpair_integers
  interfaces.integers interfaces.rationals interfaces.additional_operations
  theory.rationals.

Module QType_Rationals (Import anyQ: QType).

Module Import props := QProperties anyQ.

(* Todo: we need a similar trick as in ZType_integers for Equiv t *)
Instance QType_eq: Equiv t := eq.
Instance QType_plus: RingPlus t := add.
Instance QType_0: RingZero t := zero.
Instance QType_1: RingOne t := one.
Instance QType_mult: RingMult t := mul.
Instance QType_inv: GroupInv t := opp.
Instance QType_mult_inv: MultInv t := λ x, inv (proj1_sig x).

Instance: Setoid t.

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

Ltac unfold_equiv := unfold equiv, QType_eq, eq.

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

Program Instance: RingMinus t := sub.
Next Obligation. apply sub_add_opp. Qed.

Program Instance: FieldDiv t := div.
Next Obligation. apply div_mul_inv. Qed.

(* Type-classified facts about to_Q/of_Q: *)
Instance: Setoid_Morphism to_Q.
Proof. constructor; try apply _. intros x y. auto. Qed.

Instance: Ring_Morphism to_Q.
Proof. repeat (constructor; try apply _); intros; qify; reflexivity. Qed.

Instance: Inverse to_Q := of_Q.

Instance: Surjective to_Q.
Proof. constructor. intros x y E. rewrite <- E. apply spec_of_Q. apply _. Qed.

Instance: Injective to_Q.
Proof. constructor. auto. apply _. Qed.

Instance: Bijective to_Q.

Instance: Inverse of_Q := to_Q.

Instance: Bijective of_Q.
Proof. apply jections.flip_bijection, _. Qed.

Instance: Ring_Morphism of_Q.
Proof. change (Ring_Morphism (inverse anyQ.to_Q)). apply _. Qed.

Instance: Inverse (λ p, integers_to_ring (Z nat) t (fst p) * / integers_to_ring (Z nat) t (snd p)) := isomorphism_is_inj_inv of_Q.
Instance: Rationals t := isomorphism_is_rationals of_Q.

Global Program Instance Qtype_dec_mult_inv: DecMultInv t := inv.
Next Obligation.
  split; intros E. 
   rewrite commutativity. apply mul_inv_diag_l; trivial.
  rewrite E. unfold_equiv. qify. reflexivity.
Qed.

End QType_Rationals.
