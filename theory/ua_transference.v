Require Import
  Morphisms Setoid Program
  abstract_algebra universal_algebra theory.categories.

Section contents.

  Context (et: EquationalTheory) (A B: Variety et) (ab: Arrow et A B) (ba: Arrow et B A) (i: iso_arrows ab ba).

  Let ab_proper a: Proper (equiv ==> equiv) (proj1_sig ab a).
  Proof. destruct ab. intro. apply _. Qed.
  Let ba_proper a: Proper (equiv ==> equiv) (proj1_sig ba a).
  Proof. destruct ba. intro. apply _. Qed.

  Let epA := @eval_proper et A _ _ _.
  Let epB := @eval_proper et B _ _ _.

  Lemma transfer_eval n (t: Term et n) (v: Vars et B):
    eval et (A:=A) (fun _ i => proj1_sig ba _ (v _ i)) t == map_op _ (proj1_sig ba) (proj1_sig ab) (eval et v t).
  Proof with auto.
   destruct i as [iso_r iso_l].
   unfold equiv, a_equiv, pointwise_relation in iso_l, iso_r. simpl in *. unfold id in iso_l, iso_r.
   induction t; simpl in *; intros.
     reflexivity.
    set (eval et (fun (a : sign_atomics et) (i : nat) => proj1_sig ba _ (v a i)) t2).
    pose proof (@epA  (function (sign_atomics et) y t1) (fun a i => proj1_sig ba _ (v a i))
         (fun a i => proj1_sig ba _ (v a i)) (reflexivity _) t2 t2 (reflexivity _)
         : Proper (equiv ==> op_type_equiv (sign_atomics et) A t1)%signature o).
    rewrite (IHt2 v).
    subst o.
    pose proof (IHt1 v (proj1_sig ba _ (eval et v t3)) (proj1_sig ba _ (eval et v t3))).
    rewrite H0.
     pose proof (@map_op_proper (sign_atomics et) B A _ _ _ _ _ _). apply H1.
     pose proof (epB _ v v (reflexivity _) t2 t2 (reflexivity _)). apply H2.
      (* can't apply these directly because of Coq bug *)
     rewrite iso_r. reflexivity.
    reflexivity.
   pose proof (@propers et A _ _ _ o).
   pose proof (@propers et B _ _ _ o).
   pose proof (@preserves et A B _ _ _ _ (proj1_sig ab) (proj2_sig ab) o).
   revert H H0 H1.
   generalize (@op et A _ o) (@op et B _ o).
   induction (et o); simpl; repeat intro.
    rewrite <- H1, iso_l. reflexivity.
   apply IHo0. apply H. reflexivity.
    apply H0. reflexivity.
   assert (op_type_equiv (sign_atomics et) A o0 (o1 x) (o1 y)). apply H. assumption.
   apply (@Preservation_proper et A B _ _ _ _ (proj1_sig ab) (proj2_sig ab) _ _ o0 (o1 x) (o1 y) H3 (o2 (proj1_sig ab _ y)) (o2 (proj1_sig ab _ y)))...
   change (o2 (proj1_sig ab _ y) == o2 (proj1_sig ab _ y)).
   apply H0. reflexivity.
  Qed. (* todo: make [reflexivity] work as a hint. further cleanup. *)

  Lemma iso_vars (v: Vars et A): v == (fun _ i => proj1_sig ba _ (proj1_sig ab _ (v _ i))).
  Proof.
   intros v0 a0 a1.
   destruct i as [_ iso_l]. unfold equiv, a_equiv, pointwise_relation in iso_l. simpl in iso_l.
   rewrite iso_l. reflexivity.
  Qed.
 
  Lemma transfer_statement_and_vars (s: Statement et) (v: Vars et A):
    eval_stmt et v s <-> eval_stmt et (A:=B) (fun _ i => proj1_sig ab _ (v _ i)) s.
  Proof with reflexivity.
   intros.
   destruct i as [iso_r _].
   unfold equiv, a_equiv, pointwise_relation in iso_r. simpl in iso_r. unfold id in iso_r.
   induction s; simpl; intuition.
    rewrite <- (iso_r _ (eval et (fun a0 i => proj1_sig ab _ (v a0 i)) a)).
    rewrite <- (iso_r _ (eval et (fun a0 i => proj1_sig ab _ (v a0 i)) b)).
    rewrite <- (transfer_eval _ a (fun d i => proj1_sig ab _ (v d i))).
    rewrite <- (transfer_eval _ b (fun d i => proj1_sig ab _ (v d i))).
    rewrite <- iso_vars.
    rewrite H...
   rewrite iso_vars, transfer_eval, transfer_eval, H...
  Qed.

  Theorem transfer_statement (s: Statement et): (forall v, eval_stmt et (A:=A) v s) -> (forall v, eval_stmt et (A:=B) v s).
  Proof. intros. 
   assert (v == (fun _ i => proj1_sig ab _ (proj1_sig ba _ (v _ i)))).
    destruct i. intros a a0. symmetry. apply (H0 a (v a a0)).
   rewrite H0.
   rewrite <- transfer_statement_and_vars. apply H.
  Qed.

End contents.
