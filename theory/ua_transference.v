Require Import
  Morphisms Setoid Program
  abstract_algebra universal_algebra
  theory.categories categories.ua_variety.

Section contents.

  Context (et: EquationalTheory) (A B: Variety et) (ab: Arrow et A B) (ba: Arrow et B A) (i: iso_arrows ab ba).

  Let ab_proper a: Proper (equiv ==> equiv) (proj1_sig ab a).
  Proof. destruct ab as [? []]. intro. apply _. Qed.
  Let ba_proper a: Proper (equiv ==> equiv) (proj1_sig ba a).
  Proof. destruct ba as [? []]. intro. apply _. Qed.

  Let epA: forall V n, Proper (equiv ==> eq ==> equiv) (@eval _ A _ V n) := _.
  Let epB: forall V n, Proper (equiv ==> eq ==> equiv) (@eval _ B _ V n) := _.
    (* hints. shouldn't be necessary *)

  Program Lemma transfer_eval n (t: Term et nat n) (v: Vars et B nat):
    eval et (A:=A) (fun _ i => ba _ (v _ i)) t == map_op _ ba ab (eval et v t).
  Proof with auto; try reflexivity.
   destruct i as [iso_r iso_l].
   unfold equiv, e, pointwise_relation in iso_l, iso_r. simpl in *. unfold id in iso_l, iso_r.
   induction t; simpl in *; intros...
    set (eval et (fun (a : sign_atomics et) (i : nat) => proj1_sig ba _ (v a i)) t2).
    pose proof (@epA nat (function (sign_atomics et) y t1) (fun a i => proj1_sig ba _ (v a i))
         (fun a i => proj1_sig ba _ (v a i)) (reflexivity _) t2 t2 (reflexivity _)
         : Proper (equiv ==> op_type_equiv (sign_atomics et) A t1)%signature o).
    rewrite (IHt2 v).
    subst o.
    pose proof (IHt1 v (proj1_sig ba _ (eval et v t3)) (proj1_sig ba _ (eval et v t3))).
    rewrite H0...
    pose proof (@map_op_proper (sign_atomics et) B A _ _ _ _ _ _). apply H1.
    unfold compose in *.
    pose proof (epB _ _ v v (reflexivity _) t2 t2 (reflexivity _)). apply H2.
     (* can't apply these directly because of Coq bug *)
    rewrite iso_r...
   generalize
     (@op _ A _ o), (@op _ B _ o),
     (@propers _ A _ _ _ o),
     (@propers _ B _ _ _ o),
     (@preserves _ A B _ _ _ _ (proj1_sig ab) (proj2_sig ab) o).
   induction (et o); simpl; repeat intro.
    unfold compose in *.
    rewrite <- H1, iso_l...
   apply IHo0. apply H...
    apply H0...
   assert (op_type_equiv (sign_atomics et) A o0 (o1 x) (o1 y)). apply H...
   apply (@Preservation_proper et A B _ _ _ _ (proj1_sig ab) (proj2_sig ab) _ _ o0 (o1 x) (o1 y) H3 (o2 (proj1_sig ab _ y)) (o2 (proj1_sig ab _ y)))...
   apply H0...
  Qed. (* todo: make [reflexivity] work as a hint. further cleanup. *)

  Program Lemma iso_vars (v: Vars et A nat): v == fun _ i => ba _ ( ab _ (v _ i)).
  Proof.
   do 3 intro.
   destruct i as [_ iso_l]. unfold equiv, e, pointwise_relation in iso_l. simpl in iso_l.
   unfold compose in *. rewrite iso_l. reflexivity.
  Qed.
 
  Program Lemma transfer_eval' n (t: Term et nat n) (v: Vars et B nat):
    map_op _ ab ba (eval et (A:=A) (fun _ i => ba _ (v _ i)) t) == eval et v t.
  Proof with auto.
   intros.
   pose proof (@map_op_proper (sign_atomics et) A B _ _ _ _ _ _).
   rewrite (transfer_eval t v).
   assert (iso_arrows ba ab). apply hetero_symmetric...
   apply (@map_iso _ A B _ _ (`ab) (`ba) (proj2 H0) _ _ _).
  Qed.

  Program Lemma transfer_statement_and_vars (s: Statement et) (v: Vars et B nat):
    eval_stmt et v s <-> eval_stmt et (A:=A) (fun _ i => ba _ (v _ i)) s.
  Proof with auto; reflexivity.
   intros.
   induction s; simpl; intuition.
    rewrite transfer_eval. symmetry.
    rewrite transfer_eval. symmetry.
    apply (map_op_proper _ _ _)...
   rewrite <- transfer_eval'. symmetry.
   rewrite <- transfer_eval'. symmetry.
   apply (map_op_proper _ _ _)...
  Qed.

  Theorem transfer_statement (s: Statement et): (forall v, eval_stmt et (A:=A) v s) -> (forall v, eval_stmt et (A:=B) v s).
  Proof.
   intros s H v.
   assert (v == (fun _ i => proj1_sig ab _ (proj1_sig ba _ (v _ i)))).
    destruct i. intros a a0. symmetry. apply (H0 a (v a a0)).
   rewrite H0, transfer_statement_and_vars. apply H.
  Qed.

End contents.
