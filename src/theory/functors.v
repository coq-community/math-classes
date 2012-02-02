Require Import
  canonical_names abstract_algebra
  interfaces.functors.
Require
  categories.setoids.

Section setoid_functor_as_posh_functor.
Context `{Pfunctor : @SFunctor F map_eq map}.

Global Instance sfmap_mor `{Setoid_Morphism A B f} :
  Setoid_Morphism (sfmap f).
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; try apply _.
Qed.

Lemma sfmap_id_applied `{Setoid A} (x : F A) :
  sfmap id x = x.
Proof. 
  change (sfmap id x = id x). 
  apply setoids.ext_equiv_applied, sfmap_id.
Qed.

Lemma sfmap_comp_applied `{Equiv A} `{Equiv B} `{Equiv C} 
     `{!Setoid_Morphism (f : B → C)} `{!Setoid_Morphism (g : A → B)} (x : F A) :
  sfmap (f ∘ g) x = sfmap f (sfmap g x).
Proof. 
  change (sfmap (f ∘ g) x = (sfmap f ∘ sfmap g) x).
  pose proof (setoidmor_a g).
  apply setoids.ext_equiv_applied. now apply sfmap_comp.
Qed.

Program Definition map_setoid: setoids.Object → setoids.Object :=
  λ o, @setoids.object (F (setoids.T o)) (map_eq (setoids.T o) (setoids.e o)) _.

Program Instance: Fmap map_setoid := λ v w x, @sfmap F map _ _ (`x).

Instance: Functor map_setoid _.
Proof.
  split; try apply _.
    intros [???] [???].
    split; try apply _.
    intros [x ?] [y ?] ??? E1. simpl in *.
    assert (x = y) as E2 by intuition.
    now rewrite E1, E2.
   intros [???] x y E. simpl in *. now rewrite sfmap_id_applied.  
  intros [???] [???] [??] [???] [??] ?? E. simpl in *.
  now rewrite sfmap_comp_applied, E.
Qed.
End setoid_functor_as_posh_functor.

(** Note that we cannot prove the reverse (i.e. that an endo-Functor on
 setoid.Object gives rise to an SFunctor, because an SFunctor requires a
 Type→Type map, which we cannot get from a setoid.Object→setoid.Object map. *)
