Require
  signed_binary_positive_integers Field theory.fields.
Require Import
  Ring Morphisms QArith_base
  abstract_algebra theory.rings interfaces.rationals.

(* canonical names for relations/operations/constants: *)
Instance q_equiv: Equiv Q := Qeq.
Instance: RingZero Q := 0%Q.
Instance: RingOne Q := 1%Q.
Instance: GroupInv Q := Qopp.
Instance: RingPlus Q := Qplus.
Instance: RingMult Q := Qmult.
Program Instance: MultInv Q := Qinv.

(* properties: *)
Instance: Commutative Qplus := Qplus_comm.
Instance: Associative Qplus := Qplus_assoc.
Instance: Associative Qmult := Qmult_assoc.
Instance: Commutative Qmult := Qmult_comm.
Instance: Transitive Qle := Qle_trans.
Instance: Reflexive Qle := Qle_refl.
Instance Qle_PreOrder: PreOrder Qle.
Instance: AntiSymmetric Qle := Qle_antisym.
Instance: PartialOrder Qle.

Lemma Qplus_opp_l x: Qplus (-x) x == 0%Q.
Proof. intros. rewrite commutativity. apply Qplus_opp_r. Qed.

(* division: *)

Program Instance: MultInv Q := Qinv.

Lemma Qmult_inv_r' x: proj1_sig x * mult_inv x == 1.
Proof. destruct x. apply Qmult_inv_r. assumption. Qed.

Instance: Proper (sig_relation equiv _ ==> equiv) mult_inv.
Proof. 
 unfold sig_relation. intros [x p] [y q]. simpl. intro E.
 change (/ x == / y)%Q. rewrite E. reflexivity.
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

Instance: RingOrder q_equiv Qplus Qmult 0%Q Qle.
Proof with auto.
 constructor; try apply _; intros.
  apply Qplus_le_compat...
  reflexivity.
 apply Qmult_le_0_compat...
Qed.

Instance: OrdField Q.

(* misc: *)
Instance: forall x y: Q, Decision (x == y) := Qeq_dec.

Add Field Q: (theory.fields.stdlib_field_theory Q).

Instance: Proper (equiv ==> equiv) inject_Z. Proof. intros x y H. rewrite H. reflexivity. Qed.

Instance: SemiGroup_Morphism inject_Z (Aop:=Zmult) (Bop:=Qmult) := { preserves_sg_op := fun _ _  => refl_equal }.

Instance: SemiGroup_Morphism inject_Z (Aop:=Zplus) (Bop:=Qplus) := { preserves_sg_op := _ }.
Proof. intros. unfold inject_Z, sg_op, Qplus. repeat rewrite Zmult_1_r. reflexivity. Qed.

Instance: Monoid_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) (Amult:=Zplus) (Bmult:=Qplus) := { preserves_mon_unit := refl_equal }.

Instance: Monoid_Morphism inject_Z (Aunit:=1%Z) (Bunit:=1%Q) (Amult:=Zmult) (Bmult:=Qmult) := { preserves_mon_unit := refl_equal }.

Instance: Group_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) := { preserves_inv := fun _ => refl_equal }.

Instance: Ring_Morphism inject_Z. 

Instance: Injective inject_Z.
Proof. intros x y. change (x * 1 == y * 1 -> x == y). do 2 rewrite mult_1_r. intuition. Qed.

Instance ding: Surjective (fun p => inject_Z (fst p) * / inject_Z (snd p)).
Proof. unfold dec_mult_inv. intros [num den]. exists (num, Zpos den). rewrite Qmake_Qdiv. reflexivity. Qed.

Instance Qrat: Rationals Q.
Proof alt_Build_Rationals _ _ inject_Z _ _.
