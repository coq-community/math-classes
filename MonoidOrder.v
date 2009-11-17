Require Import Relation_Definitions Morphisms Structures.

Section contents.

  Context `{Monoid M}.

  Definition m_le: relation M := fun x y: M =>
   exists z: M, x & z == y.

  Global Instance: Proper (equiv ==> equiv ==> iff) m_le.
  Proof with assumption.
   intros x x' E y y' E'.
   unfold m_le.
   split; intros [z p]; exists z.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance: Reflexive m_le.
  Proof.
   unfold m_le.
   exists mon_unit. 
   apply runit.
  Qed.

  Global Instance: Transitive m_le.
  Proof.
   unfold m_le.
   intros x y z [d p] [d' p'].
   exists (d & d'). 
   rewrite <- p', <- p.
   apply associativity.
  Qed.

  Global Instance: PreOrder m_le.

End contents.
