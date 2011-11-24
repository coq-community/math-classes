Require Import
  canonical_names abstract_algebra
  interfaces.functors.
Require
  categories.setoids.

Section setoid_functor_as_posh_functor.

  Context `{SFunctor F}.

  Program Definition map_setoid: setoids.Object → setoids.Object :=
    λ o, setoids.object (F (setoids.T o)) (map_eq (setoids.T o) (setoids.e o)) _.

  Next Obligation. Proof.
   destruct o.
   apply (@sfunctor_makes_setoids F _ _ _).
   assumption.
  Qed.

  Program Instance: Fmap map_setoid := λ v w X, @sfmap F H _ _ (proj1_sig X).

  Next Obligation. Proof.
   destruct v, w, X. simpl in *.
   apply sfunctor_makes_morphisms; apply _.
  Qed.

  Instance: Functor map_setoid _.
  Proof with auto; intuition.
   pose proof (@sfunctor_makes_setoids F _ _ _).
   constructor; try apply _.
     intros [???] [???].
     constructor; try apply _.
     intros [x ?] [y ?] U ?? E. simpl in *.
     rewrite E.
     cut (sfmap F x = sfmap F y)...
     assert (x = y) as E'. intro...
     rewrite E'...
     apply (sfunctor_makes_morphisms F)...
    intros [???] x ??. simpl in *.
    rewrite (sfunctor_id F x x)...
   intros [???] [???] [??] [???] [??] ?? E. simpl in *.
   unfold compose at 2.
   rewrite <- E.
   apply (sfunctor_comp F)...
  Qed.

End setoid_functor_as_posh_functor.

(** Note that we cannot prove the reverse (i.e. that an endo-Functor on
 setoid.Object gives rise to an SFunctor, because an SFunctor requires a
 Type→Type map, which we cannot get from a setoid.Object→setoid.Object map. *)
