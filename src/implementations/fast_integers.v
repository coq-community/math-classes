Require Import 
  BigZ ZType_integers interfaces.integers.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ: Type := BigZ.t.

Instance: Integers fastZ := _.

Opaque fastZ.
(* This doesn't actually do much; see Coq bug # 2074. *)
(* Print Assumptions fastQ. *)
