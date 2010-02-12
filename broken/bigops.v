Require Import
  List Program
  sequences cons_list peano_naturals abstract_algebra.

Definition seq_sum `{Sequence A T} `{RingPlus A} `{z: RingZero A}: T -> A
  := @seq_to_monoid A T _ A ring_plus z id.
Definition seq_product `{Sequence A T} `{RingMult A} `{o: RingOne A}: T -> A
  := @seq_to_monoid A T _ A ring_mult o id.
    (* todo: how come we have to name z/o but not RingPlus/RingMult? *)

(* hardly worth writing down: *)
Definition seq_sum_comp: forall x y: list nat, seq_sum (x ++ y) == seq_sum x + seq_sum y
  := preserves_sg_op.
Definition seq_product_comp: forall x y: list nat, seq_product (x ++ y) == seq_product x * seq_product y
  := preserves_sg_op.

(* Test: *)

Require Import peano_naturals Peano.

Eval compute in seq_sum [3; 2].
Eval compute in seq_product [3; 2].
