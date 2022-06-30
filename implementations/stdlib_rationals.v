Require
  MathClasses.implementations.stdlib_binary_integers Coq.setoid_ring.Field Coq.QArith.Qfield MathClasses.theory.rationals.
Require Import
  Coq.ZArith.ZArith
  Coq.setoid_ring.Ring Coq.QArith.QArith_base Coq.QArith.Qabs Coq.QArith.Qpower
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.rationals
  MathClasses.interfaces.orders MathClasses.interfaces.additional_operations
  MathClasses.implementations.field_of_fractions MathClasses.orders.integers.

(* canonical names for relations/operations/constants: *)
#[global]
Instance Q_eq: Equiv Q := Qeq.
#[global]
Instance Q_0 : Zero Q := 0%Q.
#[global]
Instance Q_1 : One Q := 1%Q.
#[global]
Instance Q_opp : Negate Q := Qopp.
#[global]
Instance Q_plus : Plus Q := Qplus.
#[global]
Instance Q_mult : Mult Q := Qmult.
#[global]
Instance Q_recip : DecRecip Q := Qinv.

(* properties: *)
#[global]
Instance: Setoid Q := {}.

#[global]
Instance: DecField Q.
Proof dec_fields.from_stdlib_field_theory Qfield.Qsft eq_refl.

(* misc: *)
#[global]
Instance: ∀ x y: Q, Decision (x = y) := Qeq_dec.

#[global]
Instance inject_Z_Q: Cast Z Q := inject_Z.

#[global]
Instance: Proper ((=) ==> (=)) inject_Z.
Proof. intros x y H. unfold inject_Z. repeat red. simpl. now rewrite H. Qed.

#[global]
Instance: SemiRing_Morphism inject_Z.
Proof.
  repeat (split; try apply _).
  intros x y. repeat red. simpl. now rewrite ?Zmult_1_r.
Qed.

#[global]
Instance: Injective inject_Z.
Proof.
 constructor. 2: apply _.
 intros x y. change (x * 1 = y * 1 → x = y). rewrite 2!rings.mult_1_r. intuition.
Qed.

#[global]
Program Instance Q_to_fracZ: Cast Q (Frac Z) := λ x, frac (Qnum x) (Zpos (Qden x)) _.

#[global]
Instance: Proper ((=) ==> (=)) Q_to_fracZ.
Proof. intros ? ? E. easy. Qed.

#[global]
Instance: SemiRing_Morphism Q_to_fracZ.
Proof. repeat (split; try apply _). Qed.

#[global]
Instance: Injective Q_to_fracZ.
Proof. split; try apply _. intros ? ? E. easy. Qed.

#[global]
Instance: RationalsToFrac Q := rationals.alt_to_frac Q_to_fracZ.
#[global]
Instance: Rationals Q := rationals.alt_Build_Rationals Q_to_fracZ inject_Z.

(* order: *)
#[global]
Instance Q_le: Le Q := Qle.
#[global]
Instance Q_lt: Lt Q := Qlt.

#[global]
Instance: SemiRingOrder Q_le.
Proof.
  assert (PartialOrder Q_le).
   repeat (split; try apply _).
      exact Qle_refl.
    exact Qle_trans.
   exact Qle_antisym.
  apply (rings.from_ring_order (Rle:=Q_le)).
   repeat (split; try apply _).
   intros. apply Qplus_le_compat. now apply Qle_refl. easy.
  intros. now apply Qmult_le_0_compat.
Qed.

#[global]
Instance: TotalRelation Q_le.
Proof.
  intros x y.
  destruct (Qlt_le_dec x y); auto.
  left. now apply Qlt_le_weak.
Qed.

#[global]
Instance: FullPseudoSemiRingOrder Q_le Q_lt.
Proof.
  rapply (semirings.dec_full_pseudo_srorder (R:=Q)).
  split.
   intro. split. now apply Zorder.Zlt_le_weak. now apply Zorder.Zlt_not_eq.
  intros [E1 E2]. destruct (Zorder.Zle_lt_or_eq _ _ E1). easy. now destruct E2.
Qed.

#[global]
Program Instance: ∀ x y: Q, Decision (x ≤ y) := λ y x,
  match Qlt_le_dec x y with
  | left _ => right _
  | right _ => left _
  end.
Next Obligation. now apply Qlt_not_le. Qed.

(* additional operations *)
#[global]
Program Instance: Abs Q := Qabs.
Next Obligation.
  split; intros E.
   now apply Qabs_pos.
  now apply Qabs_neg.
Qed.

#[global]
Instance Q_pow: Pow Q Z := Qpower.

#[global]
Instance: IntPowSpec Q Z Q_pow.
Proof.
  split.
     apply _.
    reflexivity.
   exact Qpower_0.
  intros. now apply Qpower_plus.
Qed.

#[global]
Instance Q_Npow: Pow Q N := λ x n, Qpower x (cast N Z n).

#[global]
Instance: NatPowSpec Q N Q_Npow.
Proof.
  split.
    unfold pow, Q_Npow. solve_proper.
   reflexivity.
  intros. unfold pow, Q_Npow.
  rewrite rings.preserves_plus.
  rewrite Qpower_plus'.
   reflexivity.
  change (1 + cast N Z n ≠ 0).
  apply orders.lt_ne_flip.
  apply nat_int.le_iff_lt_S.
  apply nat_int.to_semiring_nonneg.
Qed.

#[global]
Instance Q_shiftl: ShiftL Q Z := λ x k,
  match k with
  | Z0 => x
  | Zpos p => Qmake (Z.shiftl (Qnum x) (Zpos p)) (Qden x)
  | Zneg p => Qmake (Qnum x) (shift_pos p (Qden x))
  end.

#[global]
Instance: ShiftLSpec Q Z Q_shiftl.
Proof.
  apply shiftl_spec_from_int_pow.
  unfold shiftl, Q_shiftl.
  intros [n d] [|p|p].
    change ((n#d) = (n#d) * 1).
    now rewrite rings.mult_1_r.
   unfold Qnum, Qden.
   rewrite !Qmake_Qdiv. unfold Qdiv.
   rewrite Z.shiftl_mul_pow2 by auto with zarith.
   rewrite Zmult_comm, inject_Z_mult, Zpower_Qpower by now destruct p.
   now rewrite <-Qmult_assoc, Qmult_comm.
  unfold Qnum, Qden.
  rewrite !Qmake_Qdiv. unfold Qdiv.
  rewrite shift_pos_correct.
  change (Zpower_pos 2 p) with (2 ^ (Zpos p))%Z.
  rewrite Zmult_comm, inject_Z_mult, Zpower_Qpower by now destruct p.
  now rewrite Qinv_mult_distr, Qmult_assoc.
Qed.
