Require Import
  Coq.Lists.List Coq.Lists.SetoidList MathClasses.interfaces.abstract_algebra MathClasses.interfaces.monads MathClasses.theory.monads.

(* The below belongs in the stdlib *)
Section equivlistA_misc.
  Context `{Equivalence A eqA}.

  Lemma NoDupA_singleton x : NoDupA eqA [x].
  Proof. apply NoDupA_cons. intros E. inversion E. auto. Qed.

  Global Instance equivlistA_cons_proper: Proper (eqA ==> equivlistA eqA ==> equivlistA eqA) cons.
  Proof.
    assert (∀ x₁ x₂ l₁ l₂ x, eqA x₁ x₂ → equivlistA eqA l₁ l₂ → InA eqA x (x₁ :: l₁) → InA eqA x (x₂ :: l₂)) as aux.
     intros ? ? ? ? ? E1 E2 E3. inversion_clear E3.
      apply InA_cons_hd. now rewrite <-E1.
     apply InA_cons_tl. now rewrite <-E2.
    split; eapply aux; auto; now symmetry.
  Qed.

  Lemma InA_singleton x y : InA eqA x [y] ↔ eqA x y.
  Proof.
    split; intros E.
     inversion_clear E; auto. now destruct (proj1 (InA_nil eqA x)).
    rewrite E. intuition.
  Qed.

  Lemma equivlistA_cons_nil x l : ¬equivlistA eqA (x :: l) [].
  Proof. intros E. now eapply InA_nil, E, InA_cons_hd. Qed.

  Lemma equivlistA_nil_eq l : equivlistA eqA l [] → l ≡ [].
  Proof. induction l. easy. intros E. edestruct equivlistA_cons_nil; eauto. Qed.

  Lemma InA_double_head z x l : InA eqA z (x :: x :: l) ↔ InA eqA z (x :: l).
  Proof. split; intros E1; auto. inversion_clear E1; auto. Qed.
  Lemma InA_permute_heads z x y l : InA eqA z (x :: y :: l) → InA eqA z (y :: x :: l).
  Proof. intros E1. inversion_clear E1 as [|?? E2]; auto. inversion_clear E2; auto. Qed.

  Lemma equivlistA_double_head x l : equivlistA eqA (x :: x :: l) (x :: l).
  Proof. split; apply InA_double_head. Qed.
  Lemma equivlistA_permute_heads x y l : equivlistA eqA (x :: y :: l) (y :: x :: l).
  Proof. split; apply InA_permute_heads. Qed.

  Lemma InA_app_ass z l₁ l₂ l₃ : InA eqA z (l₁ ++ (l₂ ++ l₃)) ↔ InA eqA z ((l₁ ++ l₂) ++ l₃).
  Proof. now rewrite app_ass. Qed.
  Lemma InA_app_nil_l z l : InA eqA z ([] ++ l) ↔ InA eqA z l.
  Proof. firstorder. Qed.
  Lemma InA_app_nil_r z l : InA eqA z (l ++ []) ↔ InA eqA z l.
  Proof. now rewrite app_nil_r. Qed.

  Lemma equivlistA_app_ass l₁ l₂ l₃ : equivlistA eqA (l₁ ++ (l₂ ++ l₃)) ((l₁ ++ l₂) ++ l₃).
  Proof. now rewrite app_ass. Qed.
  Lemma equivlistA_app_nil_l l : equivlistA eqA ([] ++ l) l.
  Proof. reflexivity. Qed.
  Lemma equivlistA_app_nil_r l : equivlistA eqA (l ++ []) l.
  Proof. now rewrite app_nil_r. Qed.

  Lemma InA_comm z l₁ l₂ : InA eqA z (l₁ ++ l₂) → InA eqA z (l₂ ++ l₁).
  Proof. rewrite !(InA_app_iff _). tauto. Qed.

  Lemma equivlistA_app_comm l₁ l₂ : equivlistA eqA (l₁ ++ l₂) (l₂ ++ l₁).
  Proof. split; apply InA_comm. Qed.

  Lemma InA_app_idem z l : InA eqA z (l ++ l) ↔ InA eqA z l.
  Proof. rewrite (InA_app_iff _). tauto. Qed.

  Lemma equivlistA_app_idem l : equivlistA eqA (l ++ l) l.
  Proof. split; apply InA_app_idem. Qed.

  Global Instance: Proper (equivlistA eqA ==> equivlistA eqA ==> equivlistA eqA) (@app A).
  Proof. intros ?? E1 ?? E2 ?. rewrite !(InA_app_iff _), E1, E2. tauto. Qed.

  Inductive PermutationA : list A → list A → Prop :=
    | permA_nil: PermutationA [] []
    | permA_skip x₁ x₂ l₁ l₂ : eqA x₁ x₂ → PermutationA l₁ l₂ → PermutationA (x₁ :: l₁) (x₂ :: l₂)
    | permA_swap x y l : PermutationA (y :: x :: l) (x :: y :: l)
    | permA_trans l₁ l₂ l₃ : PermutationA l₁ l₂ → PermutationA l₂ l₃ -> PermutationA l₁ l₃.
  Hint Constructors PermutationA.

  Global Instance: Equivalence PermutationA.
  Proof.
    split.
      intros l. induction l; intuition.
     intros l₁ l₂. induction 1; eauto. apply permA_skip; intuition.
    intros ???. now apply permA_trans.
  Qed.

  Global Instance PermutationA_cons :
    Proper (eqA ==> PermutationA ==> PermutationA) (@cons A).
  Proof. repeat intro. now apply permA_skip. Qed.

  Lemma PermutationA_app_head l₁ l₂ k :
    PermutationA l₁ l₂ → PermutationA (k ++ l₁) (k ++ l₂).
  Proof. intros. induction k. easy. apply permA_skip; intuition. Qed.

  Global Instance PermutationA_app :
    Proper (PermutationA ==> PermutationA ==> PermutationA) (@app A).
  Proof.
    intros  l₁ l₂ Pl k₁ k₂ Pk.
    induction Pl.
       easy.
      now apply permA_skip.
     etransitivity.
      rewrite <-!app_comm_cons. now apply permA_swap.
     rewrite !app_comm_cons. now apply PermutationA_app_head.
    do 2 (etransitivity; try eassumption).
    apply PermutationA_app_head. now symmetry.
  Qed.

  Lemma PermutationA_app_tail l₁ l₂ k :
    PermutationA l₁ l₂ → PermutationA (l₁ ++ k) (l₂ ++ k).
  Proof. intros E. now rewrite E. Qed.

  Lemma PermutationA_cons_append l x :
    PermutationA (x :: l) (l ++ x :: nil).
  Proof. induction l. easy. simpl. rewrite <-IHl. intuition. Qed.

  Lemma PermutationA_app_comm l₁ l₂ :
    PermutationA (l₁ ++ l₂) (l₂ ++ l₁).
  Proof.
    induction l₁.
     now rewrite app_nil_r.
    rewrite <-app_comm_cons, IHl₁.
    now rewrite app_comm_cons, PermutationA_cons_append, <-app_assoc.
  Qed.

  Lemma PermutationA_cons_app l l₁ l₂ x :
    PermutationA l (l₁ ++ l₂) → PermutationA (x :: l) (l₁ ++ x :: l₂).
  Proof.
    intros E. rewrite E.
    now rewrite app_comm_cons, PermutationA_cons_append, <-app_assoc.
  Qed.

  Lemma PermutationA_middle l₁ l₂ x :
    PermutationA (x :: l₁ ++ l₂) (l₁ ++ x :: l₂).
  Proof. now apply PermutationA_cons_app. Qed.

  Lemma PermutationA_equivlistA l₁ l₂ :
    PermutationA l₁ l₂ → equivlistA eqA l₁ l₂.
  Proof.
    induction 1.
       reflexivity.
      now apply equivlistA_cons_proper.
     now apply equivlistA_permute_heads.
    etransitivity; eassumption.
  Qed.

  Lemma NoDupA_equivlistA_PermutationA l₁ l₂ :
    NoDupA eqA l₁ → NoDupA eqA l₂ → equivlistA eqA l₁ l₂ → PermutationA l₁ l₂.
  Proof.
    intros Pl₁. revert l₂. induction Pl₁ as [|x l₁ E1].
     intros. now rewrite equivlistA_nil_eq by now symmetry.
    intros l₂ Pl₂ E2.
    destruct (@InA_split _ eqA l₂ x) as [l₂h [y [l₂t [E3 ?]]]].
     rewrite <-E2. intuition.
    subst. transitivity (y :: l₁); [intuition |].
    apply PermutationA_cons_app, IHPl₁.
     now apply NoDupA_split with y.
    apply equivlistA_NoDupA_split with x y; intuition.
  Qed.
End equivlistA_misc.

Arguments PermutationA {A} _ _ _.

Notation "( x ::)" := (cons x) (only parsing) : mc_scope.
Notation "(:: l )" := (λ x, cons x l) (only parsing) : mc_scope.
Arguments app {A} _ _.

Section contents.
  Context `{Setoid A}.

  Global Instance list_equiv: Equiv (list A) := eqlistA (=).
  Global Instance list_nil: MonUnit (list A) := [].
  Global Instance list_app: SgOp (list A) := app.

  Global Instance cons_proper: Proper (=) (@cons A).
  Proof. repeat intro. now apply eqlistA_cons. Qed.

  Instance: Setoid (list A).
  Proof. constructor; apply _. Qed.

  Instance app_proper: Proper ((=) ==> (=) ==> (=)) (@app A).
  Proof. apply _. Qed. 

  Global Instance: Monoid (list A).
  Proof.
    repeat (split; try apply _).
      intros x y z. unfold sg_op, list_app. now rewrite app_ass.
     now repeat intro.
    intros x. change (x ++ [] = x).
    now rewrite app_nil_end.
  Qed.
End contents.

Lemma list_equiv_eq {A} (x y : list A) : 
  @list_equiv A (≡) x y ↔ x ≡ y.
Proof. split. induction 1. reflexivity. now f_equal. intros. now subst. Qed.

Instance list_join: MonadJoin list := λ _, fix list_join ll :=
  match ll with
  | [] => []
  | l :: ll => l & list_join ll
  end.
Instance list_map: SFmap list := map.
Instance list_ret: MonadReturn list := λ _ x, [x].

Instance list_join_proper `{Setoid A} : Proper (=) (@list_join A).
Proof.
  intros l. induction l; intros k E; inversion_clear E; try reflexivity.
  simpl. apply app_proper; auto.
Qed.

Instance list_ret_proper `{Equiv A}: Proper (=) (list_ret A).
Proof. compute. firstorder. Qed.

Instance list_map_proper `{Setoid A} `{Setoid B} : 
  Proper (((=) ==> (=)) ==> ((=) ==> (=))) (list_map A B).
Proof.
  intros f g E1 l. induction l; intros k E2; inversion_clear E2.
   reflexivity.
  simpl. apply cons_proper; auto.
Qed.

Lemma list_join_app `{Setoid A} (l k : list (list A)) : 
  join (l & k) = join l & join k.
Proof.
  unfold join, list_join, sg_op, list_app.
  induction l; simpl; try reflexivity.
  now rewrite IHl, app_assoc.
Qed.

Lemma list_map_app `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} (l k : list A) : 
  sfmap f (l & k) = sfmap f l & sfmap f k.
Proof. pose proof (setoidmor_b f). now setoid_rewrite map_app. Qed.

Local Instance: SFunctor list.
Proof.
  split; try apply _; unfold sfmap, list_map, compose.
   intros. intros ???. now rewrite map_id.
  intros A ? B ? C ? f ? g ? ?? E.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  pose proof (setoidmor_a g). now rewrite <-E, map_map.
Qed.

Instance: StrongMonad list.
Proof.
  split; try apply _; unfold compose, id, sfmap, join, ret.
      intros A ? B ? f [???].
      intros ?? E. now rewrite <-E.
     intros A ? B ? f ? l k E. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
     rewrite <-E. clear E. induction l; try reflexivity.
     simpl. setoid_rewrite <-IHl. now apply list_map_app.
    intros A ?? [|?] k E; inversion_clear E; try reflexivity.
    simpl. rewrite right_identity. now apply cons_proper.
   intros A ? ? l k E. rewrite <-E. clear E. induction l; try reflexivity.
   simpl. now rewrite IHl.
  intros A ?? l k E. rewrite <-E. clear E. induction l; try reflexivity.
  simpl. now rewrite IHl, list_join_app.
Qed.

Instance: FullMonad list.
Proof. apply strong_monad_default_full_monad. Qed.

(*
  (* so far so good, but now: *)

  Global Instance inj: InjectToSeq list := λ _ x, x :: nil.
    (* universe inconsistency... *)

  Global Instance sm: SeqToMonoid A (list A) := λ _ _ _ f, fold_right ((&) ∘ f) mon_unit.

  Instance: Equiv A := eq.

  Instance inj_mor: Setoid_Morphism inj.

  Section sm_mor.

    Context `{Monoid M} (f: A -> M).

    Lemma sm_app (a a': list A):
      sm M _ _ f (a ++ a') = sm M _ _ f a & sm M _ _ f a'.
    Proof with reflexivity.
     induction a; simpl; intros.
      rewrite monoid_lunit...
     unfold compose. rewrite IHa, associativity...
    Qed.

    Global Instance: Setoid_Morphism f → Monoid_Morphism (sm M _ _ f).
    Proof.
     intros.
     repeat (constructor; try apply _). intros. apply sm_app.
     reflexivity.
    Qed.

  End sm_mor.

  Global Instance: @Sequence A (list A) eq _ _ _ _ _.
  Proof with try reflexivity.
   apply (Build_Sequence A (list A) eq _ _ _ _ _ _ _ inj_mor _).
   unfold proves_free.
   simpl.
   split; repeat intro.
    destruct i.
    repeat (simpl in *; unfold compose).
    rewrite H.
    apply monoid_runit.
   destruct b.
   pose proof (H tt).
   clear H. rename H0 into H.
   simpl in *.
   change (∀ x y1 : A, x = y1 → ua.variety_equiv varieties.monoid.theory y tt (proj1_sig y0 tt (inj x)) (setoidcat.f _ _ (f tt) y1)) in H.
   revert a.
   destruct y0.
   simpl in *.
   pose proof (varieties.monoid.from_object y).
   assert (universal_algebra.Implementation varieties.monoid.sig
    (λ _ : universal_algebra.sorts varieties.monoid.sig, list A)).
    exact (ua.variety_op _ (varieties.monoid.object (list A))).
   pose proof (@varieties.monoid.morphism_from_ua (list A) _ y _ (ua.variety_op _ (varieties.monoid.object (list A))) (ua.variety_op _ y) x h _ _ tt).
   induction a.
    change (x tt mon_unit = mon_unit).
    apply preserves_mon_unit.
   replace (a :: a0) with ((a :: nil) & a0)...
   rewrite preserves_sg_op, IHa.
   rewrite (H a a)...
  Qed. (* todo: clean up *)
*)
