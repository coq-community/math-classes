Require Import 
  fast_integers positive_integers_naturals
  fast_rationals
  abstract_algebra interfaces.integers interfaces.rationals interfaces.additional_operations
  BigZ ZArith.

Program Definition X : { z : fastZ | z ≠ 0 } := (1441)%bigZ.
Next Obligation. Admitted.
Program Definition Y : ZPos fastZ := (2333)%bigZ.
Next Obligation. Admitted.

Time Eval vm_compute in (mod_euclid ((12312%bigZ) ^ Y) X).

Time Eval vm_compute in ((Zmod (12312 ^ 2333) 1441)%Z).
(* 
Definition x: Z := (3^5382)%Z.
Definition y: Z := (5^3751)%Z.

Time Eval vm_compute in (x * y).

Definition x2: fastZ := (3^5382)%bigZ.
Definition y2: fastZ := (5^3751)%bigZ.

Time Eval vm_compute in (x2 * y2).
*)