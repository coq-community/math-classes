Require Import 
  BigZ Program
  abstract_algebra positive_integers_naturals
  ZType_integers interfaces.integers interfaces.additional_operations.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ: Type := BigZ.t.

