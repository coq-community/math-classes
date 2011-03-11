Require Import
 Morphisms List Program
 abstract_algebra interfaces.monads.

Implicit Arguments app [[A]].

Section contents.
  Context A `{Setoid A}.

  Global Instance list_eq: Equiv (list A) :=
    fix F (a b: list A) :=
      match a, b with
      | nil, nil => True
      | x::y, x'::y' => x = x' ∧ @equiv _ F y y'
      | _, _ => False
      end.

  Global Instance: Proper (=) (@cons A).
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

  Global Instance: Setoid (list A).
  Proof. constructor; apply _. Qed.

  Global Instance: SemiGroupOp (list A) := app.

  Global Instance app_proper: Proper (=) (@app A).
  Proof. clear H. intro x. induction x; destruct y; firstorder. Qed.

  Global Instance app_assoc_inst: Associative (@app A).
  Proof. repeat intro. symmetry. rewrite (app_ass x y z). reflexivity. Qed.

  Global Instance: SemiGroup (list A).

  Global Instance: MonoidUnit (list A) := nil.

  Global Instance: Monoid (list A).
  Proof.
   constructor. apply _.
    repeat intro. reflexivity.
   intro x. change (x ++ [] = x).
   rewrite <- (app_nil_end x). reflexivity.
  Qed.

  Definition concat: list (list A) → list A := fold_right app nil.

  Lemma concat_app (a b: list (list A)): concat (a ++ b) = concat a ++ concat b.
  Proof with intuition. induction a; simpl... rewrite IHa, app_assoc... Qed.
End contents.

Implicit Arguments concat [[A]].

Instance concat_proper `{Equiv A}: Proper (=) (@concat A).
Proof with intuition.
 intro x. induction x; destruct y...
 simpl. apply app_proper; firstorder.
Qed.

Instance: MonadReturn list := λ _ x, [x].
Instance: MonadBind list := λ _ _ l f, concat (map f l).

Instance ret_proper `{Equiv A}: Proper (=) ((_: MonadReturn list) A).
Proof. firstorder. Qed.

Instance bind_proper `{Equiv A} `{Equiv B}: Proper (=) ((_: MonadBind list) A B).
Proof.
 intro x. induction x; destruct y; intuition.
  intro. intuition.
 intros v w E.
 change (v a ++ concat (map v x) = w a0 ++ concat (map w y)).
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
*)
