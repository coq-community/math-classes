Require
  signed_binary_positive_integers Field Qfield theory.fields.
Require Import
  Ring Morphisms QArith_base
  abstract_algebra theory.rings interfaces.rationals canonical_names
  theory.rationals.

(* canonical names for relations/operations/constants: *)
Instance q_equiv: Equiv Q := Qeq.
Instance: RingZero Q := 0%Q.
Instance: RingOne Q := 1%Q.
Instance: GroupInv Q := Qopp.
Instance: RingPlus Q := Qplus.
Instance: RingMult Q := Qmult.
Program Instance: MultInv Q := Qinv.

(* properties: *)

Instance: Setoid Q.

Instance: Field Q.
Proof fields.from_stdlib_field_theory Qfield.Qsft.

(* order: *)
(*
Instance: Transitive Qle := Qle_trans.
Instance: Reflexive Qle := Qle_refl.
Instance Qle_PreOrder: PreOrder Qle.
Instance: AntiSymmetric Qle := Qle_antisym.
Instance: PartialOrder Qle.
Instance: Order Q := Qle.

Instance: RingOrder q_equiv Qplus Qmult 0%Q Qle.
Proof with auto.
 constructor; try apply _; intros.
  apply Qplus_le_compat...
  reflexivity.
 apply Qmult_le_0_compat...
Qed.

Instance: OrdField Q.
*)
(* misc: *)
Instance: ∀ x y: Q, Decision (x = y) := Qeq_dec.

Instance: Proper ((=) ==> (=)) inject_Z. 
Proof. intros x y H. rewrite H. reflexivity. Qed.

Instance: Setoid_Morphism inject_Z.

Instance: SemiGroup_Morphism inject_Z (Aop:=Zmult) (Bop:=Qmult) := { preserves_sg_op := λ _ _ , refl_equal }.

Instance: SemiGroup_Morphism inject_Z (Aop:=Zplus) (Bop:=Qplus) := { preserves_sg_op := _ }.
Proof. intros. unfold inject_Z, sg_op, Qplus. repeat rewrite Zmult_1_r. reflexivity. Qed.

Instance: Monoid_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) (Amult:=Zplus) (Bmult:=Qplus) := { preserves_mon_unit := refl_equal }.

Instance: Monoid_Morphism inject_Z (Aunit:=1%Z) (Bunit:=1%Q) (Amult:=Zmult) (Bmult:=Qmult) := { preserves_mon_unit := refl_equal }.

Instance: Group_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) := { preserves_inv := λ _, refl_equal }.

Instance: Ring_Morphism inject_Z. 

Instance: Injective inject_Z.
Proof.
 constructor. 2: apply _.
 intros x y. change (x * 1 = y * 1 → x = y). do 2 rewrite mult_1_r. intuition.
Qed.

Let inject p := inject_Z (fst p) * / inject_Z (snd p).

Instance: Setoid_Morphism inject.
Proof.
 constructor; try apply _.
 intros ?? E. unfold inject. rewrite E. reflexivity.
Qed.

Instance: Inverse inject := λ x, (Qnum x, Zpos (Qden x)).

Instance: Surjective (λ p, inject_Z (fst p) * / inject_Z (snd p)).
Proof.
 constructor. 2: apply _.
 intros [num den]. unfold Basics.compose, id.
 simpl. rewrite Qmake_Qdiv. reflexivity.
Qed.

Instance Qrat: Rationals Q.
Proof alt_Build_Rationals _ _ inject_Z _ _.

(* Relation to dec_mult_inv *)
Lemma Qinv_dec_mult_inv (q : Q) : /q = Qinv q.
Proof.
  unfold dec_mult_inv.
  case (decide (q = 0)); intros E.
  rewrite E. reflexivity.
  reflexivity.
Qed.