Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra Basics.

Section alt_injective.
  Context `{Setoid A} `{Setoid B} `{f: A → B} `{!Inv f}.
   (* Experimental Notation. If successful, then move *)
  Notation "f ⁻¹" := (@inv _ _ f _) (at level 30).
  Global Instance: Bijective f → Setoid_Morphism (f⁻¹: B → A).
  Proof with try tauto.
   repeat intro.
   constructor...
   repeat intro.
   apply (injective f).
   change ((f ∘ f ⁻¹) x = (f ∘ f ⁻¹) y).
   do 2 rewrite (surjective f _)...
  Qed.

  Lemma back: Bijective f → f ⁻¹ ∘ f = id. (* a.k.a. "split-mono" *)
  Proof. repeat intro. apply (injective f). exact (surjective f (f x)). Qed.

  Lemma forth: Setoid_Morphism f → Setoid_Morphism (f ⁻¹: B → A) → f ⁻¹ ∘ f = id → Injective f.
  Proof with try tauto.
   intros ?? E.
   constructor...
   intros ?? E'.
   rewrite <- (E x).
   rewrite <- (E y).
   unfold compose.
   rewrite E'...
   intuition.
  Qed.

  Global Instance invBij: Bijective f -> Bijective (f ⁻¹) (Inv0:=f).
  Proof with intuition.
   repeat (constructor; try apply _).
    intros x y E.
    rewrite <- (surjective f x), <- (surjective f y).
    unfold compose. (* f_equal ?*)
    rewrite E...
   intro. apply (injective f), (surjective f).
  Qed.

End alt_injective.

Section more_bijective.
  Context `{Setoid A} `{Setoid B} `{f: A → B} `{!Inv f}.
  Notation "f ⁻¹" := (@inv _ _ f _) (at level 30).
  Lemma back': Bijective f → f ∘ f ⁻¹ = id.
  intro bij.
  set (back (invBij bij)). admit. (* TODO *)
  Qed.

   Lemma cancel_left: forall t1 t2, f t1 = t2 -> t1 = f ⁻¹ t2.
   Admitted.

   Lemma cancel_left': forall t1 t2, f ⁻¹ t1 = t2 -> t1 = f t2.
   Admitted.

End more_bijective.
