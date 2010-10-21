Require Import BigZ ZType_integers signed_binary_positive_integers canonical_names.
Require Export interfaces.integers.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ: Type := BigZ.t.

Instance: Integers fastZ := _.

Definition x: Z := (3^5382)%Z.
Definition y: Z := (5^3751)%Z.

Time Eval vm_compute in (x * y).

Definition x2: fastZ := (3^5382)%bigZ.
Definition y2: fastZ := (5^3751)%bigZ.

Time Eval vm_compute in (x2 * y2).