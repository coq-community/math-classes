Set Automatic Introduction.

Require
  setoids fields stdlib_rationals.

Require Import
  QArith QSig Program
  jections abstract_algebra 
  interfaces.integers interfaces.rationals interfaces.additional_operations.

Module QType_Rationals (Import anyQ: QType).

Module props := QProperties anyQ.

Instance qev: Equiv t := eq.
Instance: RingPlus t := add.
Instance: RingZero t := zero.
Instance: RingOne t := one.
Instance: RingMult t := mul.
Instance: GroupInv t := opp.
Instance anyQ_mult_inv: MultInv t := λ x, inv (proj1_sig x).

Instance: Setoid anyQ.t.

Instance: ∀ x y: anyQ.t, Decision (x = y) := λ x y,
  (match anyQ.eq_bool x y as p return p ≡ Qeq_bool (anyQ.to_Q x) (anyQ.to_Q y) → Decision (x = y) with
  | true => λ e, left _
  | false => λ e, right _
  end) (anyQ.spec_eq_bool x y).
    (* hm, do we really need the anyQ.spec_eq_bool in here? *)

Proof with intuition. apply Qeq_bool_iff... apply Qeq_bool_neq... Qed.

  (* We could get the above for free from the fact that anyQ.eq is just projected Qeq,
   but that mean that any comparison would involve two conversion to Q, which is
   a premature pessimization. *)

Ltac unfold_equiv := unfold equiv, qev, eq.

Lemma anyQ_field_theory:
 field_theory anyQ.zero anyQ.one anyQ.add anyQ.mul anyQ.sub anyQ.opp anyQ.div anyQ.inv anyQ.eq.
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

Instance: Field anyQ.t.
Proof.
 apply (@fields.from_stdlib_field_theory
  anyQ.t anyQ.zero _ _ _ _ _ _ _ _ anyQ_field_theory); apply _.
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

Instance: Setoid_Morphism anyQ.to_Q.
Proof. constructor; try apply _. intros x y. auto. Qed.

Instance: Ring_Morphism anyQ.to_Q.
Proof.
 repeat (constructor; try apply _).
     exact anyQ.spec_add.
    exact anyQ.spec_0.
   exact anyQ.spec_opp.
  exact anyQ.spec_mul.
 exact anyQ.spec_1.
Qed.

Instance: Inverse anyQ.to_Q := anyQ.of_Q.

Instance: Surjective anyQ.to_Q.
Proof. constructor. exact anyQ.spec_of_Q. apply _. Qed.     

Instance: Injective anyQ.to_Q.
Proof. constructor. auto. apply _. Qed.

Instance: Bijective anyQ.to_Q.

Instance: Inverse anyQ.of_Q := anyQ.to_Q.

Instance: Bijective anyQ.of_Q.
Proof. apply flip_bijection, _. Qed.

Instance: Ring_Morphism anyQ.of_Q.
Proof. change (Ring_Morphism (inverse anyQ.to_Q)). apply _. Qed.

(* And finally, Rationals: *)

Lemma undec q: q ≠ 0 → / q = anyQ.inv q.
Proof.
 intros. unfold dec_mult_inv.
 set (decide (q = 0)).
 destruct s; simpl. intuition.
 reflexivity.
Qed.

Definition inject_Z': Z → anyQ.t := anyQ.of_Q ∘ inject_Z.

Let inject := (λ p: Z * Z, inject_Z' (fst p) * / inject_Z' (snd p)).

Instance: Setoid_Morphism inject.
Proof.
 unfold inject.
 constructor; try apply _.
 intros ?? E.
 unfold inject_Z', compose.
 rewrite E. reflexivity.
Qed.

Instance: Inverse inject := inverse stdlib_rationals.inject ∘ anyQ.to_Q.

Instance: Surjective inject.
Proof with try apply _.
 constructor...
 intro.
 change (anyQ.to_Q (anyQ.of_Q (inject_Z (Qnum (anyQ.to_Q x))) *
  / anyQ.of_Q (inject_Z (' Qden (anyQ.to_Q x)))) == anyQ.to_Q x).
 destruct (anyQ.to_Q x).
 simpl.
 rewrite (@rings.preserves_mult anyQ.t Q _ _ _ _ _ _ _ _ _ _ anyQ.to_Q _).
 unfold inject_Z.
 rewrite anyQ.spec_of_Q.
 change (ring_mult (Qnum # 1) (anyQ.to_Q (/ anyQ.of_Q (' Qden # 1))) = Qnum # Qden).
 pose proof (_: Proper _ (ring_mult: Q → Q → Q)).
 transitivity ((Qnum # 1) * anyQ.to_Q (anyQ.inv (anyQ.of_Q (' Qden # 1)))).
  apply H. reflexivity.
  rewrite undec. reflexivity.
  unfold equiv, qev, anyQ.eq.
  rewrite anyQ.spec_of_Q, anyQ.spec_0.
  discriminate.
 transitivity ((Qnum # 1) * Qinv (anyQ.to_Q (anyQ.of_Q (' Qden # 1)))).
  apply H. reflexivity.
  apply anyQ.spec_inv.
 transitivity ((Qnum # 1) * Qinv (' Qden # 1)).
  apply H. reflexivity.
  rewrite anyQ.spec_of_Q. reflexivity.
 change ((Qnum * 1 * ' Qden)%Z ≡ (Qnum * ' Qden)%Z).
 ring.
Qed. (* todo: clean up *)

Instance: Rationals anyQ.t.
Proof alt_Build_Rationals anyQ.t Z inject_Z' _ _.

End QType_Rationals.
