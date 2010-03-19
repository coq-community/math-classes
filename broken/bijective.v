Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program abstract_algebra Basics.

Section alt_injective.

  Context `{Setoid A} `{Setoid B} `{f: A → B} `{!Inv f}.

  Global Instance: Bijective f → Setoid_Morphism (inv: B → A).
  Proof with try tauto.
   repeat intro.
   constructor...
   repeat intro.
   apply (injective f).
   change ((f ∘ inv) x = (f ∘ inv) y).
   do 2 rewrite (surjective f _)...
  Qed.

  Lemma back: Bijective f → inv ∘ f = id. (* a.k.a. "split-mono" *)
  Proof. repeat intro. apply (injective f). exact (surjective f (f x)). Qed.

  Lemma forth: Setoid_Morphism f → Setoid_Morphism (inv: B → A) → inv ∘ f = id → Injective f.
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

End alt_injective.
