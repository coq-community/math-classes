Require Import 
  fast_integers
  fast_rationals
  canonical_names
  BigZ ZArith.
Require Export 
  interfaces.integers 
  interfaces.rationals.

Definition x: Z := (3^5382)%Z.
Definition y: Z := (5^3751)%Z.

Time Eval vm_compute in (x * y).

Definition x2: fastZ := (3^5382)%bigZ.
Definition y2: fastZ := (5^3751)%bigZ.

Time Eval vm_compute in (x2 * y2).