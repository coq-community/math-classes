Require
 BinPos.
Require Import
 Morphisms List
 Structures RingOps.

Section list_instances.

  Implicit Arguments app [[A]].

  Variable A: Type.

  Global Instance list_setoid: Equiv (list A) := eq.

  Global Instance: SemiGroupOp (list A) := app.

  Global Instance: Proper (equiv ==> equiv ==> equiv)%signature app.
  Proof. unfold equiv, list_setoid. repeat intro. subst. reflexivity. Qed.

  Global Instance app_assoc_inst: Associative app.
  Proof. repeat intro. symmetry. apply (app_ass x y z). Qed.

  Global Instance: SemiGroup (list A).

  Global Instance: MonoidUnit (list A) := nil.

  Global Instance: Monoid (list A) := { monoid_lunit := fun x => @refl_equal _ x }.
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
  Global Instance: SemiGroup _ (op:=BinPos.Pplus).
  Global Instance: SemiGroup _ (op:=BinPos.Pmult).
  Global Instance: Monoid _ (op:=BinPos.Pmult) :=
    { monoid_lunit := fun _ => @refl_equal _ _; monoid_runit := BinPos.Pmult_1_r }.

  (* misc: *)
  Global Instance positive_eq_dec: forall (x y: BinPos.positive), Decision (x == y) := BinPos.positive_eq_dec.

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
  Instance: SemiGroup nat (op:=plus).
  Instance: SemiGroup nat (op:=mult).
  Instance: Monoid _ (op:=plus) (unit:=0%nat) := { monoid_lunit := Plus.plus_0_l; monoid_runit := Plus.plus_0_r }.
  Instance: Monoid _ (op:=mult) (unit:=1%nat) := { monoid_lunit := Mult.mult_1_l; monoid_runit := Mult.mult_1_r }.
  Global Instance nat_semiring: !SemiRing nat := { mult_0_l := Mult.mult_0_l }.

  (* misc *)
  Global Instance: forall x y: nat, Decision (x == y) := Peano_dec.eq_nat_dec.

End nat_instances.

Add Ring nat: (RingOps.SemiRing_semi_ring_theory nat).

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
  Instance: SemiGroup _ (op:=BinInt.Zplus).
  Instance: SemiGroup _ (op:=BinInt.Zmult).
  Instance: Monoid _ (op:=BinInt.Zplus) (unit:=BinInt.Z0)
    := { monoid_lunit := BinInt.Zplus_0_l; monoid_runit := BinInt.Zplus_0_r }.
  Instance: Monoid _ (op:=BinInt.Zmult) (unit:=BinInt.Zpos BinPos.xH)
    := { monoid_lunit := BinInt.Zmult_1_l; monoid_runit := BinInt.Zmult_1_r }.
  Instance: @Group _ _ (BinInt.Zplus) (BinInt.Z0) _
    := { inv_l := BinInt.Zplus_opp_l; inv_r := BinInt.Zplus_opp_r }.
  Instance: AbGroup BinInt.Z (op:=BinInt.Zplus) (unit:=BinInt.Z0).
  Global Instance: Ring BinInt.Z.

  (* misc: *)
  Global Instance: forall x y: BinInt.Z, Decision (x == y) := ZArith_dec.Z_eq_dec.

End Z_instances.

Add Ring Z: (RingOps.Ring_ring_theory BinInt.Z).

Require Import QArith_base CanonicalNames Structures.

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
  Global Instance: AntiSymmetric Qle := Qle_antisym.
  Global Instance: PartialOrder Qle.

  Lemma Qplus_opp_l x: Qplus (-x) x == 0%Q.
  Proof. intros. rewrite commutativity. apply Qplus_opp_r. Qed.

  (* division: *)

  Program Instance: MultInv Q := Qinv.

  Lemma Qmult_inv_r' x: proj1_sig x * mult_inv x == 1.
  Proof. destruct x. apply Qmult_inv_r. assumption. Qed.

  Global Instance: Proper (sig_relation equiv _ ==> equiv) mult_inv.
  Proof. 
   unfold sig_relation. intros [x p] [y q]. simpl. intro E.
   change (/ x == / y). rewrite E. reflexivity.
  Qed.

  (* structures: *)
  Instance: SemiGroup _ (op:=Qplus).
  Instance: SemiGroup _ (op:=Qmult).
  Instance: Monoid Q (op:=Qplus) (unit:=0%Q) := { monoid_lunit := Qplus_0_l; monoid_runit := Qplus_0_r }.
  Instance: Monoid Q (op:=Qmult) (unit:=1%Q) := { monoid_lunit := Qmult_1_l; monoid_runit := Qmult_1_r }.
  Instance: @Group Q q_equiv Qplus 0%Q Qopp := { inv_r := Qplus_opp_r; inv_l := Qplus_opp_l }.
  Instance: AbGroup Q (op:=Qplus) (unit:=0%Q).
  Instance: Distribute Qmult Qplus := { distribute_l := Qmult_plus_distr_r; distribute_r := Qmult_plus_distr_l }.
  Instance: Ring Q.
  Instance: ZeroNeOne Q. Proof. discriminate. Qed.
  Instance: Field Q := { mult_inverse := Qmult_inv_r' }.
  Instance: Order Q := Qle.

  Global Instance: RingOrder q_equiv Qplus Qmult 0%Q Qle.
  Proof with auto.
   constructor; try apply _; intros.
    apply Qplus_le_compat...
    reflexivity.
   apply Qmult_le_0_compat...
  Qed.

  Global Instance: OrdField Q.

  (* misc: *)
  Global Instance: forall x y: Q, Decision (x == y) := Qeq_dec.

End Q_instances.

Require Field.
Require Import FieldOps.

Add Field Q: (FieldOps.Field_field_theory Q).
