Require Import 
  BigZ Program ZType_integers interfaces.integers.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ: Type := BigZ.t.

