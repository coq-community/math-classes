Require Import canonical_names.
Require Import Equivalence Morphisms RelationClasses.

(* Remove some duplicate / obsolete instances *)
Remove Hints Equivalence_Reflexive
  equiv_reflexive
  Equivalence_Symmetric
  equiv_symmetric
  Equivalence_Transitive
  equiv_transitive : typeclass_instances.

(* And re-insert the required ones with a low cost *)
Hint Extern 0 (Reflexive _) => apply @Equivalence_Reflexive : typeclass_instances.
Hint Extern 0 (Symmetric _) => apply @Equivalence_Symmetric : typeclass_instances.
Hint Extern 0 (Transitive _) => apply @Equivalence_Transitive : typeclass_instances.

(*
(* We don't want Coq trying to prove e.g. transitivity of an arbitrary relation R
  by proving that R is a StrictOrder. Therefore we ensure that Coq only attempts
  so if R is actually an instance of Lt. *)
Remove Hints
  StrictOrder_Transitive
  PreOrder_Reflexive
  PreOrder_Transitive
  PER_Symmetric
  PER_Transitive : typeclass_instances.

Hint Extern 0 (Transitive (<)) => apply @StrictOrder_Transitive : typeclass_instances.
Hint Extern 0 (Reflexive (≤)) => apply @PreOrder_Reflexive : typeclass_instances.
Hint Extern 0 (Transitive (≤)) => apply @PreOrder_Transitive : typeclass_instances.
*)

(* It seems that Coq takes an insane number of steps to prove that an equivalence
  relation is Proper. This instance should decrease the number of performed steps. *)
Instance equivalence_proper `{Equivalence A R} : Proper (R ==> R ==> iff) R | 0 := _.
