Require Import
  BigQ QType_rationals interfaces.rationals.

Module BigQ_Rationals := QType_Rationals BigQ.

Definition fastQ: Type := BigQ.t.

Opaque fastQ.
(* This doesn't actually do much; see Coq bug # 2074. *)
(* Print Assumptions fastQ. *)


