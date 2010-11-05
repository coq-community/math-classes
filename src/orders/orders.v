Require Import Morphisms Setoid Program abstract_algebra.

Section precedes_neq.
  Context `{Setoid A} `{Order A}.

  Context `{!Proper ((=) ==> (=) ==> iff) precedes}.

  Global Instance: Proper ((=) ==> (=) ==> iff) precedes_neq.
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    unfold "<". rewrite E1, E2. tauto.
  Qed.

  Context {trans : Transitive precedes} {antisym : AntiSymmetric precedes}.
     
  Global Instance precedes_neq_trans : Transitive precedes_neq.
  Proof with auto.
    intros x y z E1 E2.
    destruct E1 as [E1a E1b]. destruct E2 as [E2a E2b].
    split. transitivity y...
    intro E. rewrite E in E1a. eapply E2b.  
    apply (antisymmetry precedes)...
  Qed.
End precedes_neq.