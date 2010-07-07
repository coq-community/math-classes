Require Import
  BigQ QType_rationals.
Require Export
  interfaces.rationals.

Module BigQ_Rationals := QType_Rationals BigQ.

Definition fastQ: Type := BigQ.t.

Instance: Rationals fastQ := _.

Opaque fastQ.
  (* This doesn't actually do much; see Coq bug # 2074. *)

(* Test: *)

Print Assumptions fastQ.

Require Import canonical_names.

Definition x: fastQ := 1323165839068539058238947317846319874689127346289734455%bigQ.
Definition y: fastQ := 7513809371247375904098574279845236875724897648927556454%bigQ.

Eval vm_compute in (x * y).
