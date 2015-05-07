Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.universal_algebra.

Section contents.
  Variable σ: Signature.

  Notation OpType := (OpType (sorts σ)).

  Section homo.
  Context (A B: sorts σ → Type)
    `{A_equiv : ∀ a, Equiv (A a)} `{B_equiv : ∀ a, Equiv (B a)}
    `{A_ops : AlgebraOps σ A} `{B_ops : AlgebraOps σ B}.

  Section with_f.
    Context (f : ∀ a, A a → B a).

    Arguments f {a} _.

    Fixpoint Preservation {n : OpType}: op_type A n → op_type B n → Prop :=
      match n with
      | ne_list.one d => λ oA oB, f oA = oB
      | ne_list.cons x y => λ oA oB, ∀ x, Preservation (oA x) (oB (f x))
      end.

    Class HomoMorphism: Prop :=
      { homo_proper:> ∀ a, Setoid_Morphism (@f a)
      ; preserves: ∀ (o: σ), Preservation (A_ops o) (B_ops o)
      ; homo_source_algebra: Algebra σ A
      ; homo_target_algebra: Algebra σ B }.

    Context `{∀ a, Setoid (A a)} `{∀ b, Setoid (B b)} `{∀ a, Setoid_Morphism (@f a)}.

    Global Instance Preservation_proper n:
      Proper (op_type_equiv _ _ _ ==> op_type_equiv _ B n ==> iff) (@Preservation n).
        (* todo: use (=) in the signature and see why things break *)
    Proof with auto.
     induction n; simpl; intros x y E x' y' E'.
      split; intro F. rewrite <- E, <- E'... rewrite E, E'...
     split; simpl; intros.
      eapply IHn; eauto; symmetry; [now apply E | now apply E'].
     eapply IHn; eauto; [now apply E | now apply E'].
   Qed.

    Global Instance Preservation_proper'' n:
      Proper (eq ==> (=) ==> iff) (@Preservation n).
    Proof with auto.
     induction n; simpl; intros x y E x' y' E'.
      split; intro F. rewrite <- E, <- E'... rewrite E, E'...
     split; simpl; intros.
      subst.
      apply (IHn (y x0) (y x0) eq_refl (y' (f x0)) (x' (f x0)) ).
       symmetry.
       apply E'.
       reflexivity.
      apply H2.
     subst.
     apply (IHn (y x0) (y x0) eq_refl (y' (f x0)) (x' (f x0)) ).
      symmetry.
      apply E'.
      reflexivity.
     apply H2.
    Qed. (* todo: evil, get rid of *)
  End with_f.

  Lemma Preservation_proper' (f g: ∀ a, A a → B a)
   `{∀ a, Setoid (A a)} `{∀ b, Setoid (B b)} `{∀ a, Setoid_Morphism (@f a)}:
    (∀ a (x: A a), f a x = g a x) → ∀ (n: OpType) x y, Proper (=) x → Proper (=) y →
      @Preservation f n x y →
      @Preservation g n x y.
  Proof.
     induction n.
      simpl.
      intros ? ? ? ? E.
      rewrite <-E.
      symmetry.
      intuition.
     simpl.
     intros a b E1 E2 E3 z.
     apply IHn.
       apply E1. reflexivity.
      apply E2. reflexivity.
     assert (b (g _ z) = b (f _ z)) as E4.
      apply E2.
      symmetry.
      apply H2.
     now apply (Preservation_proper'' f n (a z) (a z) eq_refl _ _ E4).
    Qed.

    Lemma HomoMorphism_Proper: Proper ((λ f g, ∀ a x, f a x = g a x) ==> iff) HomoMorphism.
      (* todo: use pointwise_thingy *)
    Proof with try apply _; intuition.
     intros x y E1. constructor; intros [? ? ? ?]; simpl in *.
      repeat constructor...
       intros ? ? E2.
       rewrite <-2!E1.
       rewrite E2...
      apply (Preservation_proper' x y E1 (σ o) (A_ops o) (B_ops o))...
     repeat constructor...
      intros ? ? E2.
      rewrite 2!E1.
      rewrite E2...
     assert (∀ (a : sorts σ) (x0 : A a), y a x0 = x a x0) as E2. symmetry. apply E1.
     apply (Preservation_proper' y x E2 (σ o) (A_ops o) (B_ops o))...
    Qed.
  End homo.

  Global Instance id_homomorphism A
    `{∀ a, Equiv (A a)} {ao: AlgebraOps σ A} `{!Algebra σ A}: HomoMorphism _ _ (λ _, id).
  Proof with try apply _; intuition.
   constructor; intros...
   generalize (ao o).
   induction (σ o); simpl...
   reflexivity.
  Qed.

  Global Instance compose_homomorphisms A B C f g
    `{∀ a, Equiv (A a)} `{∀ a, Equiv (B a)} `{∀ a, Equiv (C a)}
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B} {co: AlgebraOps σ C}
    {gh: HomoMorphism A B g} {fh: HomoMorphism B C f}: HomoMorphism A C (λ a, f a ∘ g a).
  Proof with try apply _; auto.
   pose proof (homo_source_algebra _ _ g).
   pose proof (homo_target_algebra _ _ g).
   pose proof (homo_target_algebra _ _ f).
   constructor; intros...
   generalize (ao o) (bo o) (co o) (preserves _ _ g o) (preserves _ _ f o).
   induction (σ o); simpl; intros; unfold compose.
    rewrite H5...
   apply (IHo0 _ (o2 (g _ x)))...
  Qed.

  Lemma invert_homomorphism A B f
    `{∀ a, Equiv (A a)} `{∀ a, Equiv (B a)}
    {ao: AlgebraOps σ A} {bo: AlgebraOps σ B}
    {fh: HomoMorphism A B f}
    `{inv: ∀ a, Inverse (f a)}:
    (∀ a, Bijective (f a)) →
    HomoMorphism A B f → HomoMorphism B A inv.
  Proof with try assumption; try apply _.
   intros ? [? ? ? ?].
   constructor...
   intro.
   generalize (ao o) (bo o) (preserves _ _ f o)
     (algebra_propers o: Proper (=) (ao o)) (algebra_propers o: Proper (=) (bo o)).
   induction (σ o); simpl.
    intros.
    apply (injective (f t)).
    pose proof (surjective (f t) o1 o1 (reflexivity o1)).
    transitivity o1...
    symmetry...
   intros P Q R S T x.
   apply IHo0.
     eapply Preservation_proper''; eauto; intros; try apply _.
     symmetry. now apply T, (surjective (f t) x x).
    apply S. reflexivity.
   apply T. reflexivity.
  Qed.

(*
    Instance eval_morphism `{Algebra σ}  A {V} (v: Vars σ A V):
      HomoMorphism (Term0 σ V) A (λ _ => eval σ v).
    Proof.
     constructor; repeat intro; try apply _.
     unfold AlgebraOps_instance_0.
     generalize (algebra_propers o: eval v (Op V o) = H o).
     generalize (Op V o) (H o).
     induction (operation_type σ o); simpl; repeat intro.
      assumption.
     apply IHo0. simpl.
     apply H1.
     destruct H0. reflexivity.
    Qed.
*)

End contents.
