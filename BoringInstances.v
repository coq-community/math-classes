
Require BinPos.

Require Import CanonicalNames Structures Morphisms RingOps List.

Section list_instances.

  Implicit Arguments app [[A]].

  Variable A: Type.

  Global Instance list_setoid: Equiv (list A) := eq.

  Global Instance: SemiGroupOp (list A) := app.

  Global Instance: Proper (equiv ==> equiv ==> equiv)%signature app.
  Proof. unfold equiv, list_setoid. repeat intro. subst. reflexivity. Qed.

  Global Instance app_assoc_inst: Associative app.
  Proof. repeat intro. symmetry. apply (app_ass x y z). Qed.

  Global Instance: SemiGroup equiv app.

  Global Instance: Monoid _ app nil := { lunit := fun _ => refl_equal _ }.
  Proof. symmetry. apply (app_nil_end x). Qed.

End list_instances.

Section positive_instances.

  (* canonical names for relations/operations/constants: *)
  Global Instance pos_equiv: Equiv BinPos.positive := eq.
  Global Instance: SemiGroupOp BinPos.positive := BinPos.Pplus.
  Global Instance: RingMult BinPos.positive := BinPos.Pmult.
  Global Instance: MonoidUnit BinPos.positive := BinPos.xH.

  (* propers: *)
  Global Instance: Proper (equiv ==> equiv ==> equiv) BinPos.Pplus.
  Proof. unfold equiv, pos_equiv. repeat intro. subst. reflexivity. Qed.
  Global Instance: Proper (equiv ==> equiv ==> equiv) BinPos.Pmult.
  Proof. unfold equiv, pos_equiv. repeat intro. subst. reflexivity. Qed.

  (* properties: *)
  Global Instance: Associative BinPos.Pplus := BinPos.Pplus_assoc.
  Global Instance: Associative BinPos.Pmult := BinPos.Pmult_assoc.
  Global Instance: Commutative BinPos.Pplus := BinPos.Pplus_comm.
  Global Instance: Commutative BinPos.Pmult := BinPos.Pmult_comm.
  Global Instance: Distribute BinPos.Pmult BinPos.Pplus :=
    { distribute_l := BinPos.Pmult_plus_distr_l; distribute_r := BinPos.Pmult_plus_distr_r }.

  (* structures: *)
  Global Instance: SemiGroup equiv BinPos.Pplus.
  Global Instance: SemiGroup equiv BinPos.Pmult.
  Global Instance: Monoid equiv BinPos.Pmult BinPos.xH :=
    { lunit := fun _ => refl_equal _; runit := BinPos.Pmult_1_r }.

  (* misc: *)
  Global Instance: Decidable pos_equiv := BinPos.positive_eq_dec.

End positive_instances.

Require Mult Peano_dec Ring.

Section nat_instances.

  (* canonical names for relations/operations/constants: *)
  Global Instance nat_equiv: Equiv nat := eq.
  Global Instance: RingPlus nat := plus.
  Global Instance: RingZero nat := 0%nat.
  Global Instance: RingOne nat := 1%nat.
  Global Instance: RingMult nat := mult.

  (* propers: *)
  Global Instance: Proper (equiv ==> equiv ==> equiv) plus.
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.
  Global Instance: Proper (equiv ==> equiv ==> equiv) mult.
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

  (* properties: *)
  Global Instance: Associative plus := Plus.plus_assoc.
  Global Instance: Associative mult := Mult.mult_assoc.
  Global Instance: Commutative plus := Plus.plus_comm.
  Global Instance: Commutative mult := Mult.mult_comm.
  Global Instance: Distribute mult plus :=
    { distribute_l := Mult.mult_plus_distr_l; distribute_r := Mult.mult_plus_distr_r }.

  (* structures: *)  
  Global Instance: SemiGroup equiv plus.
  Global Instance: SemiGroup equiv mult.
  Global Instance: Monoid equiv plus 0%nat := { lunit := Plus.plus_0_l; runit := Plus.plus_0_r }.
  Global Instance: Monoid equiv mult 1%nat := { lunit := Mult.mult_1_l; runit := Mult.mult_1_r }.
  Global Instance nat_semiring: SemiRing equiv plus mult 0%nat 1%nat := { mult_0_l := Mult.mult_0_l }.

  (* misc *)
  Global Instance: Decidable nat_equiv := Peano_dec.eq_nat_dec.

End nat_instances.

Definition nat_semi_ring_theory: Ring_theory.semi_ring_theory 0 1 ring_plus ring_mult equiv
  := RingOps.SemiRing_semi_ring_theory nat.
Add Ring nat: nat_semi_ring_theory.

Section Z_instances.

  (* canonical names: *)
  Global Instance z_equiv: Equiv BinInt.Z := eq.
  Global Instance: RingPlus BinInt.Z := BinInt.Zplus.
  Global Instance: RingZero BinInt.Z := BinInt.Z0.
  Global Instance: RingOne BinInt.Z := BinInt.Zpos BinPos.xH.
  Global Instance: RingMult BinInt.Z := BinInt.Zmult.
  Global Instance: GroupInv BinInt.Z := BinInt.Zopp.

  (* propers: *)
  Global Instance: Proper (equiv ==> equiv ==> equiv) BinInt.Zplus.
  Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.
  Global Instance: Proper (equiv ==> equiv ==> equiv) BinInt.Zmult.
  Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.
  Global Instance: Proper (equiv ==> equiv) BinInt.Zopp.
  Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.

  (* properties: *)
  Global Instance: Associative BinInt.Zplus := BinInt.Zplus_assoc.
  Global Instance: Associative BinInt.Zmult := BinInt.Zmult_assoc.
  Global Instance: Commutative BinInt.Zplus := BinInt.Zplus_comm.
  Global Instance: Commutative BinInt.Zmult := BinInt.Zmult_comm.
  Global Instance: Distribute BinInt.Zmult BinInt.Zplus :=
    { distribute_l := BinInt.Zmult_plus_distr_r; distribute_r := BinInt.Zmult_plus_distr_l }.

  (* structures: *)
  Global Instance: SemiGroup equiv BinInt.Zplus.
  Global Instance: SemiGroup equiv BinInt.Zmult.
  Global Instance Zplus_monoid: Monoid equiv BinInt.Zplus BinInt.Z0
    := { lunit := BinInt.Zplus_0_l; runit := BinInt.Zplus_0_r }.
  Global Instance: Monoid equiv BinInt.Zmult (BinInt.Zpos BinPos.xH) := { lunit := BinInt.Zmult_1_l; runit := BinInt.Zmult_1_r }.
  Global Instance: Group equiv BinInt.Zplus BinInt.Z0 BinInt.Zopp := { inv_l := BinInt.Zplus_opp_l; inv_r := BinInt.Zplus_opp_r }.
  Global Instance: AbGroup equiv BinInt.Zplus BinInt.Z0 BinInt.Zopp.
  Global Instance Zring: Ring equiv BinInt.Zplus BinInt.Zmult BinInt.Zopp BinInt.Z0 (BinInt.Zpos BinPos.xH).

  (* misc: *)
  Global Instance: Decidable z_equiv := ZArith_dec.Z_eq_dec.

End Z_instances.

Definition Z_ring_theory: Ring_theory.ring_theory 0 1 ring_plus ring_mult (fun x y => x + - y) group_inv equiv
  := RingOps.Ring_ring_theory BinInt.Z.
Add Ring Z: Z_ring_theory.

Require Import QArith_base CanonicalNames.

Section Q_instances.

  (* canonical names for relations/operations/constants: *)
  Global Instance q_equiv: Equiv Q := Qeq.
  Global Instance: RingZero Q := 0%Q.
  Global Instance: RingOne Q := 1%Q.
  Global Instance: GroupInv Q := Qopp.
  Global Instance: RingPlus Q := Qplus.
  Global Instance: RingMult Q := Qmult.
  Global Program Instance: MultInv Q := Qinv.

  (* properties: *)
  Global Instance: Commutative Qplus := Qplus_comm.
  Global Instance: Associative Qplus := Qplus_assoc.
  Global Instance: Associative Qmult := Qmult_assoc.
  Global Instance: Commutative Qmult := Qmult_comm.
  Global Instance: Transitive Qle := Qle_trans.
  Global Instance: Reflexive Qle := Qle_refl.
  Global Instance Qle_PreOrder: PreOrder Qle.

  Global Instance: PartialOrder q_equiv Qle.
   unfold PartialOrder, relation_conjunction,
     predicate_intersection, pointwise_extension, Basics.flip.
   split.
    intros H. rewrite H. split; reflexivity.
   intros [A B]. apply Qle_antisym; assumption.
  Qed.

  Lemma Qplus_opp_l x: Qplus (-x) x == 0%Q.
  Proof. intros. rewrite commutativity. apply Qplus_opp_r. Qed.

  (* division: *)

  Program Definition Qinv' (x: { x: Q | ~ Qeq x 0 }): Q := Qinv x.

  Lemma Qmult_inv_r' x: proj1_sig x * Qinv' x == 1.
  Proof.
   destruct x. unfold Qinv'. simpl.
   apply Qmult_inv_r. assumption.
  Qed.

  Global Instance: Proper (sig_relation equiv _ ==> equiv) Qinv'.
  Proof.
   unfold Qinv', sig_relation.
   intros [x p] [y q]. simpl.
   intro. rewrite H. reflexivity.
  Qed.

  (* structures: *)
  Global Instance: SemiGroup q_equiv Qplus.
  Global Instance: SemiGroup q_equiv Qmult.
  Global Instance: Monoid q_equiv Qplus 0%Q := { lunit := Qplus_0_l; runit := Qplus_0_r }.
  Global Instance: Monoid q_equiv Qmult 1%Q := { lunit := Qmult_1_l; runit := Qmult_1_r }.
  Global Instance: Group q_equiv Qplus 0%Q Qopp := { inv_r := Qplus_opp_r; inv_l := Qplus_opp_l }.
  Global Instance: AbGroup q_equiv Qplus 0%Q Qopp.
  Global Instance: Distribute Qmult Qplus := { distribute_l := Qmult_plus_distr_r; distribute_r := Qmult_plus_distr_l }.
  Global Instance Qring: Ring q_equiv Qplus Qmult Qopp 0%Q 1%Q.

  Global Instance: Field q_equiv Qplus Qmult Qopp 0%Q 1%Q Qinv' := { mult_inverse := Qmult_inv_r' }.
  Proof. discriminate. Qed.
  Global Instance: OrdField q_equiv Qplus Qmult Qopp 0%Q 1%Q Qinv' Qle.
  Proof with auto.
   apply (@Build_OrdField Q q_equiv Qplus Qmult Qopp 0%Q 1%Q Qinv' Qle Field_instance_0 Qle_PreOrder _); intros.
    apply Qplus_le_compat...
    reflexivity.
   apply Qmult_le_0_compat...
  Qed.

  (* misc: *)
  Global Instance: Decidable q_equiv := Qeq_dec.

End Q_instances.

Require Field.
Require Import FieldOps.

Definition Q_field_theory: Field_theory.field_theory 0 1 ring_plus ring_mult (fun x y => x + - y)
  group_inv (fun x y => x * / y) dec_mult_inv CanonicalNames.equiv
    := FieldOps.Field_field_theory.
Add Field Q: Q_field_theory.
