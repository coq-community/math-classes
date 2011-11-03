Require Import
  List SetoidList abstract_algebra interfaces.monads.

Notation "( x ::)" := (cons x) (only parsing).
Notation "(:: l )" := (λ x, cons x l) (only parsing).
Implicit Arguments app [[A]].

Section contents.
  Context `{Setoid A}.

  Global Instance list_equiv: Equiv (list A) := eqlistA (=).

  Global Instance: Proper (=) (@cons A).
  Proof. repeat intro. now apply eqlistA_cons. Qed.

  Global Instance: Setoid (list A).
  Proof. constructor; apply _. Qed.

  Global Instance: SgOp (list A) := app.

  Global Instance app_proper: Proper (=) (@app A).
  Proof. apply _. Qed.

  Global Instance app_assoc_inst: Associative (@app A).
  Proof. repeat intro. symmetry. now rewrite (app_ass x y z). Qed.

  Global Instance: SemiGroup (list A) := {}.

  Global Instance: MonUnit (list A) := nil.

  Global Instance: Monoid (list A).
  Proof.
   constructor. apply _.
    repeat intro. reflexivity.
   intro x. change (x ++ [] = x).
   now rewrite <-(app_nil_end x).
  Qed.

  Definition concat: list (list A) → list A := fold_right app nil.

  Lemma concat_app (a b: list (list A)): concat (a ++ b) = concat a ++ concat b.
  Proof with intuition. induction a; simpl... now rewrite IHa, app_assoc. Qed.
End contents.

Implicit Arguments concat [[A]].

Instance concat_proper `{Equiv A}: Proper (=) (@concat A).
Proof.
  intros l. induction l.
   intros k E. inversion_clear E. now apply eqlistA_nil.
  intros k E. inversion_clear E. apply app_proper; firstorder.
Qed.

Instance list_ret: MonadReturn list := λ _ x, [x].
Instance list_bind: MonadBind list := λ _ _ l f, concat (List.map f l).

Instance ret_proper `{Equiv A}: Proper (=) (list_ret A).
Proof. compute. firstorder. Qed.

Instance bind_proper `{Equiv A} `{Equiv B}: Proper (=) (list_bind A B).
Proof.
  intros x₁ x₂. induction 1.
   intros f₁ f₂ E₂. compute. firstorder.
  intros f₁ f₂ E₂. unfold list_bind. simpl.
  apply app_proper; firstorder.
Qed.

(* Can't [Qed] due to universe inconsistency:

Instance: Monad list.
Proof with intuition.
 constructor; intros; try apply _.
   change (f x ++ [] = f x).
   rewrite app_nil_r...
  change (concat (map ret m) = m).
  induction m. reflexivity.
  simpl. rewrite IHm...
 change (concat (map g (concat (map f n))) = concat (map (λ x, concat (map g (f x))) n)).
 induction n. reflexivity. simpl.
 rewrite map_app, concat_app.
  rewrite IHn...
 apply _.
Qed. *)

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
