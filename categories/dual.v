Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Section contents.

  Context `{c: @Category Object A Aeq Aid Acomp}.

  Let Arrow := flip A.

  Global Instance: CatId Object Arrow := Aid.
  Global Instance comp: CatComp Object Arrow := fun _ _ _ => flip (Acomp _ _ _).
  Global Instance e: forall x y, Equiv (Arrow x y) := fun x y => Aeq y x.

  Global Instance: forall x y, Equivalence (e x y).
  Proof. intros. unfold e, Arrow, flip. apply _. Qed.

  Instance: forall x y z, Proper (equiv ==> equiv ==> equiv) (@comp x y z).
  Proof.
   intros x y z ? ? E ? ? F.
   unfold comp, Arrow, flip.
   destruct c. rewrite E, F. reflexivity.
  Qed.
  
  Global Instance cat: Category Object Arrow.
  Proof with auto.
   destruct c.
   constructor; try apply _; auto.
   unfold comp, Arrow, flip.
   intros. symmetry. apply comp_assoc.
  Qed.

End contents.
