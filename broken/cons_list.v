Set Automatic Introduction.

Require Import
 Morphisms List Program
 abstract_algebra theory.categories interfaces.sequences.
Require
 categories.setoid categories.product varieties.monoid.

Implicit Arguments app [[A]].

Section contents.

  Context A `{Setoid A}.

  Fixpoint leq (a b: list A): Prop :=
    match a, b with
    | nil, nil => True
    | h :: t, h' :: t' => h = h' ∧ leq t t'
    | _, _ => False
    end.

  Hint Extern 4 (Equiv (list A)) => exact leq: typeclass_instances.

  Instance: Proper ((=) ==> (=) ==> (=)) (@cons A).
  Proof. repeat intro. split; assumption. Qed.

  Instance: Reflexive (_: Equiv (list A)).
  Proof. intro x. induction x. reflexivity. split. reflexivity. assumption. Qed.

  Instance: Symmetric (_: Equiv (list A)).
  Proof with trivial.
   unfold equiv. intro x. induction x; destruct y...
   simpl. intros [P Q].
   split. symmetry...
   apply IHx...
  Qed.

  Instance: Transitive (_: Equiv (list A)).
  Proof with simpl; intuition.
   unfold equiv. intro x. induction x; destruct y...
   destruct z... transitivity a0...
   firstorder.
  Qed.

  Instance: Setoid (list A).
  Proof. constructor; apply _. Qed.

  Global Instance: SemiGroupOp (list A) := app.

  Global Instance: Proper ((=) ==> (=) ==> (=))%signature (@app A).
  Proof with intuition.
   unfold equiv.
   intro x. induction x; destruct y; simpl in *; repeat intro...
   split...
   apply IHx...
  Qed.

  Global Instance app_assoc_inst: Associative (@app A).
  Proof. repeat intro. symmetry. rewrite (app_ass x y z). reflexivity. Qed.

  Global Instance: SemiGroup (list A).

  Global Instance: MonoidUnit (list A) := nil.

  Global Instance: Monoid (list A).
  Proof.
   constructor.
     apply _.
    repeat intro. reflexivity.
   intro x. change (x ++ [] = x).
   rewrite <- (app_nil_end x). reflexivity.
  Qed.

  (* so far so good, but now: *)

  Global Instance inj: InjectToSeq list := fun _ x => x :: nil.
    (* universe inconsistency... *)

  Global Instance sm: SeqToMonoid A (list A) := fun _ _ _ f => fold_right (sg_op ∘ f) mon_unit.

  Instance: Equiv A := eq.

  Instance inj_mor: Setoid_Morphism inj.

  Section sm_mor.

    Context `{Monoid M} (f: A -> M).

    Lemma sm_app (a a': list A):
      sm M _ _ f (a ++ a') == sm M _ _ f a & sm M _ _ f a'.
    Proof with reflexivity.
     induction a; simpl; intros. 
      rewrite monoid_lunit...
     unfold compose. rewrite IHa, associativity...
    Qed.

    Global Instance: Setoid_Morphism f -> Monoid_Morphism (sm M _ _ f).
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
   change (forall x y1 : A, x = y1 -> ua.variety_equiv varieties.monoid.theory y tt (proj1_sig y0 tt (inj x)) (setoidcat.f _ _ (f tt) y1)) in H.
   revert a.
   destruct y0.
   simpl in *.
   pose proof (varieties.monoid.from_object y).
   assert (universal_algebra.Implementation varieties.monoid.sig
    (fun _ : universal_algebra.sorts varieties.monoid.sig => list A)).
    exact (ua.variety_op _ (varieties.monoid.object (list A))).
   pose proof (@varieties.monoid.morphism_from_ua (list A) _ y _ (ua.variety_op _ (varieties.monoid.object (list A))) (ua.variety_op _ y) x h _ _ tt).
   induction a.
    change (x tt mon_unit == mon_unit).
    apply preserves_mon_unit.
   replace (a :: a0) with ((a :: nil) & a0)...
   rewrite preserves_sg_op, IHa.
   rewrite (H a a)...
  Qed. (* todo: clean up *)

End contents.
