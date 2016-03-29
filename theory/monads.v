Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.monads MathClasses.theory.functors.

Instance default_mon_join `{MonadBind M} : MonadJoin M | 20 := λ _, bind id.
Instance default_mon_map `{MonadReturn M} `{MonadBind M} : SFmap M | 20 := λ _ _ f, bind (ret ∘ f).
Instance default_mon_bind `{SFmap M} `{MonadJoin M} : MonadBind M | 20 := λ _ _ f, join ∘ (sfmap f).

Hint Extern 0 (ProperProxy (@respectful _ _ _ _) _) =>
  class_apply @proper_proper_proxy : typeclass_instances.

Instance equiv_ext_equiv `{Equiv A} `{Equiv B} :
  Setoid A -> Setoid B ->
  Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> flip impl)
         (@equiv _ (@ext_equiv A _ B _)).
Proof.
  unfold ext_equiv. repeat (red; intros).
  assert ((equiv ==> equiv)%signature x x0).
  eapply transitivity. eauto.
  eapply transitivity. eauto.
  eapply symmetry. eauto.
  eapply H7. eapply H6.
Qed.

Instance equiv_ext_equiv_partial `{Equiv A} `{Equiv B} (f : A -> B) :
  Setoid A -> Setoid B ->
  Proper (equiv ==> equiv) f ->
  Proper ((equiv ==> equiv) ==> flip impl)
         (@equiv _ (@ext_equiv A _ B _) f).
Proof. intros. partial_application_tactic; eauto. apply equiv_ext_equiv; eauto. Qed.

Section monad.
  Context `{Monad M}.

  Lemma bind_lunit_applied `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} (x : A) : 
    ret x ≫= f = f x.
  Proof. pose proof (setoidmor_a f). now apply bind_lunit. Qed.

  Lemma bind_runit_applied `{Setoid A} (m : M A) : 
    m ≫= ret = m.
  Proof. now apply bind_runit. Qed.

  Lemma bind_assoc_applied `{Equiv A} `{Equiv B} `{Setoid C} 
       `{!Setoid_Morphism (f : A → M B)} `{!Setoid_Morphism (g : B → M C)} (m : M A) :
    (m ≫= f) ≫= g = x ← m ; f x ≫= g.
  Proof. pose proof (setoidmor_a f). now apply bind_assoc. Qed.

  Global Instance ret_mor `{Setoid A} : Setoid_Morphism (@ret _ _ A) := {}.
  Global Instance bind_mor `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} :
    Setoid_Morphism (bind f).
  Proof. pose proof (setoidmor_a f). split; try apply _. Qed.

  Definition liftM2 `(f: A → B → C) (m : M A) (n : M B) : M C :=
    x ← m ; y ← n ; ret (f x y).

  Section to_strong_monad.
  Context `{MonadJoin M} `{SFmap M}
    (map_proper : ∀ `{Setoid A} `{Setoid B}, Proper (((=) ==> (=)) ==> ((=) ==> (=))) (@sfmap M _ A B))
    (map_correct : ∀ `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)}, sfmap f = bind (ret ∘ f))
    (join_correct : ∀ `{Setoid A}, join = bind id).
  Existing Instance map_proper.

  Let bind_correct `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} : 
    bind f = join ∘ sfmap f.
  Proof.
    pose proof (setoidmor_a f). pose proof (setoidmor_b f).
    rewrite join_correct, map_correct by apply _.
    rewrite bind_assoc.
    change (bind f = bind ((bind id ∘ ret) ∘ f)).
    rewrite bind_lunit.
    now apply setoids.ext_equiv_refl.
  Qed.

  Instance: SFunctor M.
  Proof.
    split; try apply _.
     intros A ? ?.
     rewrite map_correct by apply _. 
     now apply bind_runit.
    intros A ? B ? C ? f ? g ?.
    pose proof (setoidmor_a g). pose proof (setoidmor_b g). pose proof (setoidmor_b f).
    rewrite !map_correct by apply _.
    rewrite bind_assoc.
    change (bind (ret ∘ (f ∘ g)) = bind ((bind (ret ∘ f) ∘ ret) ∘ g)).
    rewrite bind_lunit.
    now apply setoids.ext_equiv_refl.
  Qed.

  Instance: ∀ `{Setoid A}, Setoid_Morphism (@join _ _ A).
  Proof.
    split; try apply _. intros x y E1. 
    assert (∀ z, join z = bind id z) as E2 by (intros; now apply join_correct).
    now rewrite !E2, E1.
  Qed.

  Instance monad_strong_monad: StrongMonad M.
  Proof.
    split; try apply _.
        intros A ? B ? f ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
        rewrite map_correct by apply _.
        rewrite bind_lunit.
        now apply setoids.ext_equiv_refl.
       intros A ? B ? f ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
       rewrite <-bind_correct.
       rewrite !join_correct by apply _.
       rewrite map_correct by apply _.
       rewrite bind_assoc.
       now apply setoids.ext_equiv_refl.
      intros A ??. rewrite join_correct by apply _. 
      rewrite bind_lunit.
      now apply setoids.ext_equiv_refl.
     intros A ??.
     rewrite <-bind_correct.
     rewrite bind_runit.
     now apply setoids.ext_equiv_refl.
    intros A ??. rewrite <-bind_correct.
    rewrite !join_correct by apply _.
    rewrite bind_assoc.
    now apply setoids.ext_equiv_refl.
  Qed.

  Instance monad_full_monad: FullMonad M.
  Proof. split; try apply _; auto. Qed.
  End to_strong_monad.

  Instance monad_default_full_monad: FullMonad M.
  Proof.
    apply monad_full_monad; unfold sfmap, default_mon_map.
      intros A ?? B ?? f g E1 m n E2.
      apply mon_bind_proper.
       intros x y E3. now apply mon_ret_proper, E1.
      easy.
     intros A ? B ? f ??? E. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
     now rewrite E.
    intros A ?? ?? E. unfold join, default_mon_join.
    now rewrite E.
  Qed.
End monad.

Section strong_monad.
  Context `{StrongMonad M}.

  Global Instance sret_mor `{Setoid A} : Setoid_Morphism (@ret _ _ A) := {}.
  Global Instance join_mor `{Setoid A} : Setoid_Morphism (@join _ _ A) := {}.

  Hint Immediate setoidmor_a : typeclass_instances.
  Hint Immediate setoidmor_b : typeclass_instances.

  Lemma sfmap_ret_applied `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} (x : A) : 
    sfmap f (ret x) = ret (f x).
  Proof. now apply sfmap_ret. Qed.

  Lemma sfmap_join_applied `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} (m : M (M A)) : 
    sfmap f (join m) = join (sfmap (sfmap f) m).
  Proof. now apply sfmap_join. Qed.

  Lemma join_ret_applied `{Setoid A} (m : M A) :
    join (ret m) = m.
  Proof. now apply join_ret. Qed.

  Lemma join_sfmap_ret_applied `{Setoid A} (m : M A):
    join (sfmap ret m) = m.
  Proof. now apply join_sfmap_ret. Qed.

  Lemma join_sfmap_join_applied `{Setoid A} (m : M (M (M A))) : 
    join (sfmap join m) = join (join m).
  Proof. now apply join_sfmap_join. Qed.

  Section to_monad.
  Context `{MonadBind M}
    (bind_proper : ∀ `{Setoid A} `{Setoid B}, Proper (((=) ==> (=)) ==> ((=) ==> (=))) (@bind M _ A B))
    (bind_correct : ∀ `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)}, bind f = join ∘ sfmap f).

  Instance: ∀ `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)},
    Setoid_Morphism (bind f).
  Proof. intros. split; try apply _. Qed.

  Let bind_correct_applied `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} m :
    bind f m = join (sfmap f m).
  Proof. now eapply bind_correct; try apply _. Qed.

  Instance strong_monad_monad: Monad M.
  Proof.
    split; try apply _.
      intros A ? B ?? f ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
      rewrite bind_correct by apply _.
      rewrite compose_assoc, sfmap_ret.
      rewrite <-compose_assoc, join_ret.
      now apply setoids.ext_equiv_refl.
     intros A ? ?.
     rewrite bind_correct by apply _.
     now apply join_sfmap_ret.
    intros A ? B ? C ?? f ? g ? m n E. pose proof (setoidmor_a f). pose proof (setoidmor_a g).
    unfold compose at 1. rewrite !bind_correct_applied.
    rewrite bind_correct by apply _.
    rewrite sfmap_join_applied.
    rewrite !sfmap_comp_applied.
    rewrite join_sfmap_join_applied.
    now rewrite E.
  Qed.

  Instance strong_monad_full_monad: FullMonad M.
  Proof. split; try apply _; auto. Qed.
  End to_monad.

  Instance strong_monad_default_full_monad: FullMonad M.
  Proof.
    apply strong_monad_full_monad; unfold bind, default_mon_bind.
     intros A ?? B ?? f g E1 m n E2.
     apply smon_join_proper. apply sfmap_proper; intuition.
    intros A ? B ?? f ? ?? E.
    now rewrite E.
  Qed.
End strong_monad.

Section full_monad.
  Context `{FullMonad M}.

  Lemma bind_as_join_sfmap_applied `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} (m : M A) : 
    m ≫= f = join (sfmap f m).
  Proof. pose proof (setoidmor_a f). now  apply bind_as_join_sfmap. Qed.

  Lemma sfmap_as_bind_ret `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} : 
     sfmap f = bind (ret ∘ f).
  Proof.
    pose proof (setoidmor_a f). pose proof (setoidmor_b f).
    rewrite bind_as_join_sfmap.
    rewrite sfmap_comp.
    rewrite <-compose_assoc.
    rewrite join_sfmap_ret.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma sfmap_as_bind_ret_applied `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} (m : M A) : 
    sfmap f m = x ← m ; ret (f x).
  Proof. pose proof (setoidmor_a f). now apply sfmap_as_bind_ret. Qed.

  Lemma join_as_bind `{Setoid A} : 
    join = bind id.
  Proof.
    rewrite bind_as_join_sfmap.
    rewrite sfmap_id.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma join_as_bind_applied `{Setoid A} (m : M (M A)) : 
    join m = m ≫= id.
  Proof. now apply join_as_bind. Qed.

  Lemma join_spec_applied_alt `{Setoid A} (m : M (M A)) : 
    join m = x ← m ; x.
  Proof. now apply join_as_bind. Qed.

  Lemma bind_twice `{Equiv A} `{Equiv B} `{Setoid C} 
       `{!Setoid_Morphism (f : B → M C)} `{!Setoid_Morphism (g : A → M B)} :
    bind (bind f) = bind f ∘ join.
  Proof.
    pose proof (setoidmor_a f). pose proof (setoidmor_b f).
    pose proof (setoidmor_b g).
    rewrite join_as_bind.
    rewrite bind_assoc.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma bind_twice_applied `{Equiv A} `{Equiv B} `{Setoid C} 
       `{!Setoid_Morphism (f : B → M C)} `{!Setoid_Morphism (g : A → M B)} (m : M (M B)) :
    m ≫= bind f = join m ≫= f.
  Proof. pose proof (setoidmor_a f). now apply bind_twice. Qed. 

  Lemma bind_join `{Setoid A} : 
    bind join = join ∘ join.
  Proof.
    rewrite !join_as_bind.
    rewrite bind_assoc.
    now apply setoids.ext_equiv_refl.
  Qed.

  Lemma bind_join_applied `{Setoid A} (m : M (M (M A))) : 
    m ≫= join = join (join m).
  Proof. now apply bind_join. Qed.
End full_monad.
