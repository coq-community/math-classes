Set Automatic Introduction.

Require
  theory.fields stdlib_rationals.
Require Import
  QArith QSig
  abstract_algebra 
  natpair_integers
  interfaces.integers interfaces.rationals interfaces.additional_operations
  theory.rationals.

Module QType_Rationals (Import anyQ: QType).

Module props := QProperties anyQ.

(* Todo: we need a similar trick as in ZType_integers for Equiv t *)
Instance qev: Equiv t := eq.
Instance: RingPlus t := add.
Instance: RingZero t := zero.
Instance: RingOne t := one.
Instance: RingMult t := mul.
Instance: GroupInv t := opp.
Instance anyQ_mult_inv: MultInv t := λ x, inv (proj1_sig x).

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

Ltac unfold_equiv := unfold equiv, qev, eq.

Lemma anyQ_field_theory: field_theory zero one add mul sub opp div inv eq.
  (* No idea why this is missing in QSig. *)
Proof.
 constructor. constructor.
            exact props.add_0_l.
           exact props.add_comm.
          exact props.add_assoc.
         exact props.mul_1_l.
        exact props.mul_comm.
       exact props.mul_assoc.
      exact props.mul_add_distr_r.
     exact props.sub_add_opp .
    exact props.add_opp_diag_r.
   exact props.neq_1_0.
  exact props.div_mul_inv.
 exact props.mul_inv_diag_l.
Qed.

Instance: Field t.
Proof.
 apply (fields.from_stdlib_field_theory anyQ_field_theory).
Qed.

Program Instance: RingMinus t := sub.
Next Obligation. 
  apply props.sub_add_opp.
Qed.

Program Instance: FieldDiv t := div.
Next Obligation.
  apply props.div_mul_inv.
Qed.

(* Type-classified facts about to_Q/of_Q: *)
Instance: Setoid_Morphism to_Q.
Proof. constructor; try apply _. intros x y. auto. Qed.

Instance: Ring_Morphism to_Q.
Proof.
 repeat (constructor; try apply _).
     exact anyQ.spec_add.
    exact anyQ.spec_0.
   exact anyQ.spec_opp.
  exact anyQ.spec_mul.
 exact anyQ.spec_1.
Qed.

Instance: Inverse to_Q := of_Q.

Instance: Surjective to_Q.
Proof. constructor. exact spec_of_Q. apply _. Qed.

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

(* Relation to dec_mult_inv *)
Lemma Qtype_inv_dec_mult_inv q : /q = inv q.
Proof.
  unfold dec_mult_inv.
  case (decide (q = 0)); intros E.
  rewrite E. unfold_equiv. rewrite spec_inv, rings.preserves_0. reflexivity.
  reflexivity.
Qed.

End QType_Rationals.
