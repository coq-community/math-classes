Require
  stdlib_binary_integers Field QArith.Qfield theory.fields.
Require Import
  Ring Morphisms QArith_base Qabs Qpower
  abstract_algebra interfaces.rationals field_of_fractions
  theory.rings  theory.rationals additional_operations.

(* canonical names for relations/operations/constants: *)
Instance Q_eq: Equiv Q := Qeq.
Instance Q_0 : RingZero Q := 0%Q.
Instance Q_1 : RingOne Q := 1%Q.
Instance Q_opp : GroupInv Q := Qopp.
Instance Q_plus : RingPlus Q := Qplus.
Instance Q_mult : RingMult Q := Qmult.
Program Instance Q_mult_inv : MultInv Q := Qinv.

(* properties: *)
Instance: Setoid Q.

Instance: Field Q.
Proof fields.from_stdlib_field_theory Qfield.Qsft.

(* order: *)
Instance: Order Q := Qle.

Instance: RingOrder Qle.
Proof with auto.
  repeat (split; try apply _)...
      exact Qle_refl.
     exact Qle_trans.
    exact Qle_antisym.
   intros. apply Qplus_le_compat... apply Qle_refl.
  intros. apply Qmult_le_0_compat...
Qed.

Instance: TotalOrder Qle.
Proof with auto.
  intros x y.
  destruct (Qlt_le_dec x y)...
  left. apply Qlt_le_weak...
Qed.

Program Instance: ∀ x y: Q, Decision (x ≤ y) := λ y x, 
  match Qlt_le_dec x y with
  | left _ => right _
  | right _ => left _
  end.
Next Obligation. now apply Qlt_not_le. Qed. 

Lemma Qlt_coincides x y : (x < y)%Q ↔ x < y.
Proof with trivial.
  split.
   intro. split. apply Qlt_le_weak... apply Qlt_not_eq...
  intros [E1 E2]. destruct (proj1 (Qle_lteq _ _) E1)... destruct E2...
Qed.

(* misc: *)
Instance: ∀ x y: Q, Decision (x = y) := Qeq_dec.

Instance inject_Z_Q: Coerce Z Q := inject_Z.

Instance: Proper ((=) ==> (=)) inject_Z. 
Proof. intros x y H. unfold inject_Z. repeat red. simpl. now rewrite H. Qed.

Instance: SemiRing_Morphism inject_Z. 
Proof.
  repeat (split; try apply _).
  intros x y. repeat red. simpl. now rewrite ?Zmult_1_r.
Qed.

Instance: Injective inject_Z.
Proof.
 constructor. 2: apply _.
 intros x y. change (x * 1 = y * 1 → x = y). rewrite 2!mult_1_r. intuition.
Qed.

Program Definition Q_to_fracZ (x : Q) : Frac Z := frac (Qnum x) (Zpos (Qden x)) _.

Instance: Proper ((=) ==> (=)) Q_to_fracZ.
Proof. intros ? ? E. easy. Qed.

Instance: SemiRing_Morphism Q_to_fracZ.
Proof. repeat (split; try apply _). Qed.

Instance: Injective Q_to_fracZ.
Proof. split; try apply _. intros ? ? E. easy. Qed.

Instance: RationalsToFrac Q := alt_to_frac Q_to_fracZ.
Instance: Rationals Q := alt_Build_Rationals Q_to_fracZ inject_Z.

Program Instance Q_dec_mult_inv: DecMultInv Q := Qinv.
Next Obligation.
  split; intros E. 
   now apply Qmult_inv_r.
  now rewrite E.
Qed.

Program Instance: Abs Q := Qabs.
Next Obligation with trivial.
  split; intros E.
   now apply Qabs_pos.
  now apply Qabs_neg.
Qed.

Instance Q_pow: Pow Q Z := Qpower.

Instance: IntPowSpec Q Z Q_pow.
Proof.
  split.
     apply _.
    reflexivity.
   exact Qpower_0. 
  intros. now apply Qpower_plus.
Qed.
