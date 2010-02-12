Set Automatic Introduction.

Require Import
 Morphisms List Program
 abstract_algebra theory.categories sequences.
Require
 ua_forget categories.setoid categories.product varieties.monoid.

Implicit Arguments app [[A]].

Section contents.

  Context (A: Type).

  Global Instance list_setoid: Equiv (list A) := eq. (* todo: use setoid equality over A *)

  Global Instance: SemiGroupOp (list A) := app.

  Global Instance: Proper (equiv ==> equiv ==> equiv)%signature app.
  Proof. unfold equiv, list_setoid. repeat intro. subst. reflexivity. Qed.

  Global Instance app_assoc_inst: Associative app.
  Proof. repeat intro. symmetry. apply (app_ass x y z). Qed.

  Global Instance: SemiGroup (list A).

  Global Instance: MonoidUnit (list A) := nil.

  Global Instance: Monoid (list A) := { monoid_lunit := @refl_equal _ }.
  Proof. symmetry. apply (app_nil_end x). Qed.

  Global Instance inj: SeqInject A (list A) := fun x => x :: nil.
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
