Require Import
  MathClasses.theory.categories
  MathClasses.interfaces.functors
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.sequences.

Section contents.
  Context `{Sequence sq}.

  (* Some derived properties about inject, extend, and fmap: *)
  Lemma inject_epi `{Setoid A} `{Equiv B} `{SgOp B} `{MonUnit B}
    (f g: sq A → B) `{!Monoid_Morphism f} `{!Monoid_Morphism g} :
      f ∘ inject A = g ∘ inject A → f = g.
  Proof with intuition.
   intros.
   pose proof (setoidmor_a f).
   pose proof (monmor_b (f:=g)).
   pose proof (sequence_only_extend_commutes sq (f ∘ inject A) _) as E.
   pose proof (_ : Setoid_Morphism (f ∘ inject A)) as cm.
   rewrite (E f), (E g)...
    apply (sequence_extend_morphism sq)...
    apply cm.
   apply cm.
  Qed.

  Lemma extend_comp
    `{Equiv A}
    `{Equiv B} `{SgOp B} `{MonUnit B}
    `{Equiv C} `{SgOp C} `{MonUnit C}
     (f: B → C) (g: A → B) `{!Monoid_Morphism f} `{!Setoid_Morphism g} :
    extend (f ∘ g) (free:=sq) = f ∘ extend g (free:=sq).
  Proof with try apply _.
   intros.
   pose proof (setoidmor_a g).
   pose proof (monmor_a (f:=f)).
   pose proof (monmor_b (f:=f)).
   symmetry.
   apply (sequence_only_extend_commutes sq (f ∘ g))...
   symmetry.
   rewrite <- (sequence_extend_commutes sq g _) at 1.
   apply sm_proper.
  Qed.

  Lemma extend_inject `{Setoid A}: extend (inject A) = @id (sq A).
  Proof.
   symmetry. apply (sequence_only_extend_commutes sq); try apply _.
   apply sm_proper.
  Qed.

(*
  Lemma fmap_alt `{Equiv A} `{Equiv B} (f: A → B) `{!Setoid_Morphism f} :
    extend (inject B ∘ f) = (fmap (v:=A) (w:=B) sq f: sq A → sq B). (* Remove (v:=A) (w:=B) *)
  Proof with try apply _.
   intros.
   pose proof (setoidmor_a f).
   pose proof (setoidmor_b f).
   symmetry.
   apply (sequence_only_extend_commutes sq (inject B ∘ f))...

   symmetry.
   apply (sequence_inject_natural sq)...
  Qed.
*)

  Lemma fold_inject `{Monoid A}: fold sq ∘ inject A = id.
  Proof. apply (sequence_extend_commutes sq id). apply _. Qed.

(*
  Lemma fold_map `{Setoid A} `{Monoid B} (f: A → B) `{!Setoid_Morphism f} :
    extend f (free:=sq) = fold sq ∘ fmap (v:=A) (w:=B) sq f. (* Remove (v:=A) (w:=B) *)
  Proof with try apply _.
   intros.
   symmetry.
   apply (sequence_only_extend_commutes sq _)...
   symmetry.
   change (f = extend id ∘ ((fmap sq f: sq A → sq B) ∘ inject A)).
   rewrite <- (sequence_inject_natural sq f _).
   change (f = fold sq ∘ inject B ∘ f).
   pose proof (_ : Morphisms.ProperProxy equiv f).
   rewrite fold_inject.
   rewrite compose_id_left.
   apply sm_proper.
  Qed.
*)
End contents.

(* In the context of a SemiRing, we have two particularly useful folds: sum and product. *)
Section semiring_folds.
  Context `{SemiRing R} `{Sequence sq}.

  Definition sum: sq R → R := @fold sq _ _ (0:R) (+).
  Definition product: sq R → R := @fold sq _ _ (1:R) mult.

  (* These are implicitly Monoid_Morphisms, and we also easily have: *)
(*
  Lemma distribute_sum (a: R): (a *.) ∘ sum = sum ∘ fmap (v:=R) (w:=R) sq (a *.).
  Proof.
   unfold sum, fold.
   pose proof (_ : Monoid_Morphism (a *.)).
   rewrite <-(extend_comp (a *.) id).
   rewrite compose_id_right.
   rewrite (fold_map (a *.)).
   intros x y E. now rewrite E.
  Qed.
*)
End semiring_folds.
