Require Import 
  BigZ interfaces.integers.
Require Export
  ZType_integers.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ : Type := BigZ.t.

