Require Ring.
Require Field.

(*
Since r13842 an "Add Setoid" that is located in a section adds global instances 
of Reflexive, Symmetric, Transitive and Equivalence. Due to these unused instances
setoid rewriting becomes incredibly slow. 

Matthieu confirmed this problem and will fix it soon. However, for the time being 
we remove these instances manually.
*)

Remove Hints Ring_theory.R_setoid1_Reflexive
  Ring_theory.R_setoid2_Reflexive
  InitialRing.R_setoid3_Reflexive
  InitialRing.R_setoid5_Reflexive 
  InitialRing.R_setoid4_Reflexive 
  InitialRing.R_set1_Reflexive 
  Ring_theory.C_setoid_Reflexive
  Ring_theory.R_set_Power_Reflexive
  Ring_polynom.R_set1_Reflexive 
  Field_theory.R_setoid3_Reflexive
  Field_theory.R_set1_Reflexive : typeclass_instances.

Remove Hints Ring_theory.R_setoid1_Symmetric
  Ring_theory.R_setoid2_Symmetric
  InitialRing.R_setoid3_Symmetric
  InitialRing.R_setoid5_Symmetric 
  InitialRing.R_setoid4_Symmetric 
  InitialRing.R_set1_Symmetric 
  Ring_theory.C_setoid_Symmetric
  Ring_theory.R_set_Power_Symmetric
  Ring_polynom.R_set1_Symmetric
  Field_theory.R_setoid3_Symmetric
  Field_theory.R_set1_Symmetric : typeclass_instances.

Remove Hints Ring_theory.R_setoid1_Transitive
  Ring_theory.R_setoid2_Transitive
  InitialRing.R_setoid3_Transitive
  InitialRing.R_setoid5_Transitive 
  InitialRing.R_setoid4_Transitive 
  InitialRing.R_set1_Transitive 
  Ring_theory.C_setoid_Transitive
  Ring_theory.R_set_Power_Transitive
  Ring_polynom.R_set1_Transitive
  Field_theory.R_setoid3_Transitive
  Field_theory.R_set1_Transitive : typeclass_instances.

Remove Hints Ring_theory.R_setoid1
  Ring_theory.R_setoid2
  InitialRing.R_setoid3
  InitialRing.R_setoid5 
  InitialRing.R_setoid4 
  InitialRing.R_set1 
  Ring_theory.C_setoid
  Ring_theory.R_set_Power
  Ring_polynom.R_set1
  Field_theory.R_setoid3
  Field_theory.R_set1 : typeclass_instances.

(* Other duplicates *)
Remove Hints RelationClasses.Equivalence_Reflexive 
  Equivalence.equiv_reflexive
  RelationClasses.Equivalence_Symmetric 
  Equivalence.equiv_symmetric
  RelationClasses.Equivalence_Transitive 
  Equivalence.equiv_transitive : typeclass_instances.

Hint Extern 0 (RelationClasses.Reflexive _) => apply RelationClasses.Equivalence_Reflexive : typeclass_instances.
Hint Extern 0 (RelationClasses.Symmetric _) => apply RelationClasses.Equivalence_Symmetric : typeclass_instances.
Hint Extern 0 (RelationClasses.Transitive _) => apply RelationClasses.Equivalence_Transitive : typeclass_instances.
