Require Import
  abstract_algebra
  interfaces.monads
  interfaces.functors.

Section contents.
  Context `{Monad M}.

  Instance liftM: SFmap M := λ {A B} (f: A → B) (ma: M A), ma >>= ret ∘ f.

  Instance: SFunctor M.
  Proof with intuition.
   pose proof (@mon_setoid M _ _ _ _).
   constructor; intros; try apply _; unfold sfmap, liftM.
      pose proof (setoidmor_a f).
      pose proof (setoidmor_b f).
      constructor; try apply _.
     intros ?? E. repeat intro.
     apply (@bind_proper M _ _ _ _ v _ _ w _ _)...
     intros c d. intros.
     unfold compose.
     rewrite (E c d)...
    intros x y E.
    unfold id at 2.
    rewrite <- E.
    rewrite compose_id_right.
    apply mon_runit; apply _.
   intros x y E.
   unfold compose at 3.
   pose proof (setoidmor_a g).
   pose proof (setoidmor_b g).
   pose proof (setoidmor_b f).
   rewrite mon_assoc; try apply _.
   apply (bind_proper M x y E).
   intros v w U.
   unfold compose.
   rewrite mon_lunit; try apply _.
   rewrite U.
   reflexivity.
  Qed.

  Definition liftM2 {A B C} (f: A → B → C) (x: M A) (y: M B): M C :=
    xv ← x; yv ← y; ret (f xv yv).
End contents.
