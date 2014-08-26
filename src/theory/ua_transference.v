Require Import
  abstract_algebra universal_algebra ua_homomorphisms
  canonical_names theory.categories ua_mapped_operations.

Require categories.varieties.

Section contents.

  Context (et: EquationalTheory) `{InVariety et A} `{InVariety et B}
    `{!HomoMorphism et A B ab} `{!HomoMorphism et B A ba}
    (i: iso_arrows (varieties.arrow et ab) (varieties.arrow et ba)).

  Arguments ab {a} _.
  Arguments ba {a} _.

  Let ab_proper a: Proper ((=) ==> (=)) (@ab a).
  Proof. apply _. Qed.

  Let ba_proper a: Proper ((=) ==> (=)) (@ba a).
  Proof. apply _. Qed.

  Let epA: ∀ V n, Proper ((=) ==> eq ==> (=)) (@eval _ A _ V n) := _.
  Let epB: ∀ V n, Proper ((=) ==> eq ==> (=)) (@eval _ B _ V n) := _.
    (* hints. shouldn't be necessary *)

  Let ab_ba: ∀ b (a: B b), ab (ba a) = a := proj1 i.
  Let ba_ab: ∀ b (a: A b), ba (ab a) = a := proj2 i.

  Program Lemma transfer_eval n (t: Term et nat n) (v: Vars et B nat):
    eval et (A:=A) (λ _ i, ba (v _ i)) t = map_op _ (@ba) (@ab) (eval et v t).
  Proof with auto; try reflexivity.
   induction t; simpl in *; intros...
    set (eval et (λ (a: sorts et) (i : nat), ba (v a i)) t2).
    eapply transitivity.
     apply (@epA nat (ne_list.cons y t1) (λ a i, ba (v a i))
         (λ a i, ba (v a i)) (reflexivity _) t2 t2 (reflexivity _)
         : Proper ((=) ==> op_type_equiv (sorts et) A t1)%signature o).
     now apply IHt2.
    subst o.
    rewrite (IHt1 (ba (eval et v t3)) (ba (eval et v t3)))...
    apply (@map_op_proper (sorts et) B A _ _ _ _ _ _).
    unfold compose in *.
    rapply (epB _ _ v v (reflexivity _) t2 t2 (reflexivity _)).
    apply ab_ba.
   generalize
     (@algebra_propers _ A _ _ _ o)
     (@algebra_propers _ B _ _ _ o).
   generalize (@preserves et A B _ _ _ _ (@ab) _ o).
   fold (@algebra_op et A _ o) (@algebra_op et B _ o).
   generalize (@algebra_op et A _ o), (@algebra_op et B _ o).
   induction (et o); simpl; repeat intro.
    rewrite <- ba_ab, H1...
   apply IHo0.
     eapply Preservation_proper''; eauto; intros; try apply _.
     symmetry. apply H3, ab_proper, H4.
    apply H2...
   apply H3...
  Qed. (* todo: make [reflexivity] work as a hint. further cleanup. *)

  Program Lemma transfer_eval' n (t: Term et nat n) (v: Vars et B nat):
    map_op _ (@ab) (@ba) (eval et (A:=A) (λ _ i, ba (v _ i)) t) = eval et v t.
  Proof with auto.
   intros.
   pose proof (@map_op_proper (sorts et) A B _ _ _ _ _ _).
   rewrite transfer_eval.
   apply (@map_iso _ A B _ _ (@ab) (@ba) ab_ba).
   apply _.
  Qed.

  Program Lemma transfer_statement_and_vars (s: Statement et) (v: Vars et B nat):
    eval_stmt et v s ↔ eval_stmt et (A:=A) (λ _ i, ba (v _ i)) s.
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

  Theorem transfer_statement (s: Statement et): (∀ v, eval_stmt et (A:=A) v s) → (∀ v, eval_stmt et (A:=B) v s).
  Proof with intuition auto.
   intros ? v.
   assert (v = (λ _ i, ab (ba (v _ i)))) as P.
    destruct i. intros a a0. symmetry...
   rewrite P, transfer_statement_and_vars...
  Qed.

End contents.
