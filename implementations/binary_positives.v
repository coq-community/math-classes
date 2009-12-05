Require Import
  Morphisms
  abstract_algebra.

(* canonical names for relations/operations/constants: *)
Instance pos_equiv: Equiv BinPos.positive := eq.
Instance: SemiGroupOp BinPos.positive := BinPos.Pplus.
Instance: RingMult BinPos.positive := BinPos.Pmult.
Instance: MonoidUnit BinPos.positive := BinPos.xH.

(* propers: *)
Instance: Proper (equiv ==> equiv ==> equiv) BinPos.Pplus.
Proof. unfold equiv, pos_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper (equiv ==> equiv ==> equiv) BinPos.Pmult.
Proof. unfold equiv, pos_equiv. repeat intro. subst. reflexivity. Qed.

(* properties: *)
Instance: Associative BinPos.Pplus := BinPos.Pplus_assoc.
Instance: Associative BinPos.Pmult := BinPos.Pmult_assoc.
Instance: Commutative BinPos.Pplus := BinPos.Pplus_comm.
Instance: Commutative BinPos.Pmult := BinPos.Pmult_comm.
Instance: Distribute BinPos.Pmult BinPos.Pplus :=
  { distribute_l := BinPos.Pmult_plus_distr_l; distribute_r := BinPos.Pmult_plus_distr_r }.

(* structures: *)
Instance: SemiGroup _ (op:=BinPos.Pplus).
Instance: SemiGroup _ (op:=BinPos.Pmult).
Instance: Monoid _ (op:=BinPos.Pmult) :=
  { monoid_lunit := fun _ => @refl_equal _ _; monoid_runit := BinPos.Pmult_1_r }.

(* misc: *)
Instance positive_eq_dec: forall (x y: BinPos.positive), Decision (x == y) := BinPos.positive_eq_dec.
