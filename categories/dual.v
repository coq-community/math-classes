Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Section contents.

  Context `{c: @Category Object A Aeq Aid Acomp}.

  Instance flipA: Arrows Object := flip A.

  Global Instance: @CatId Object flipA := Aid.
  Global Instance: @CatComp Object flipA := λ _ _ _ => flip (Acomp _ _ _).
  Global Instance e: Π x y, Equiv (flipA x y) := λ x y => Aeq y x. 

  Global Instance: Π (x y: Object), Equivalence (e x y).
  Proof. intros. change (Equivalence (equiv: Equiv (A y x))). apply _. Qed.

  Instance: Π (x y z: Object), Proper (equiv ==> equiv ==> equiv) (@comp Object flipA _ x y z).
  Proof.
   intros x y z ? ? E ? ? F.
   change (Acomp z y x x1 x0 = Acomp z y x y1 y0).
   unfold equiv, e.
   destruct c. rewrite E, F. reflexivity.
  Qed.
  
  Global Instance cat: @Category Object flipA _ _ _.
  Proof with auto.
   destruct c.
   constructor; try apply _; auto.
      unfold Setoid, equiv, e.
      intros.
      apply arrow_equiv.
     unfold comp, Arrow, flip.
     intros. symmetry. apply comp_assoc.
    intros. apply (id_r y x a).
   intros. apply (id_l y x a).
  Qed.

End contents.
