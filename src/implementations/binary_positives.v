Require Import
  Morphisms BinPos
  abstract_algebra.

(* canonical names for relations/operations/constants: *)
Instance pos_equiv: Equiv BinPos.positive := eq.
Instance: SemiGroupOp BinPos.positive := BinPos.Pplus.
Instance: RingMult BinPos.positive := BinPos.Pmult.
Instance: MonoidUnit BinPos.positive := BinPos.xH.

(* propers: *)
Instance: Proper ((=) ==> (=) ==> (=)) BinPos.Pplus.
Proof. unfold equiv, pos_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper ((=) ==> (=) ==> (=)) BinPos.Pmult.
Proof. unfold equiv, pos_equiv. repeat intro. subst. reflexivity. Qed.

(* properties: *)
Instance: Associative BinPos.Pplus := BinPos.Pplus_assoc.
Instance: Associative BinPos.Pmult := BinPos.Pmult_assoc.
Instance: Commutative BinPos.Pplus := BinPos.Pplus_comm.
Instance: Commutative BinPos.Pmult := BinPos.Pmult_comm.
Instance: Distribute BinPos.Pmult BinPos.Pplus :=
  { distribute_l := BinPos.Pmult_plus_distr_l; distribute_r := BinPos.Pmult_plus_distr_r }.

(* structures: *)
Instance: Setoid BinPos.positive.
Instance: SemiGroup _ (op:=BinPos.Pplus).
Instance: SemiGroup _ (op:=BinPos.Pmult).

Instance: LeftIdentity BinPos.Pmult (1%positive).
Proof. repeat intro. reflexivity. Qed.

Instance: RightIdentity BinPos.Pmult (1%positive) := BinPos.Pmult_1_r.

Instance: Monoid _ (op:=BinPos.Pmult).

(* misc: *)
Instance positive_eq_dec: ∀ x y, Decision (x = y) := BinPos.positive_eq_dec.
  (* silly type-change constant *)
