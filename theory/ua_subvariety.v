Require Import
  RelationClasses Morphisms Program
  universal_algebra canonical_names ua_subalgebra.

(* In theory/ua_subalgebra.v we defined closed proper subsets and showed that
they yield subalgebras. We now expand on this result and show that they
also yield subvarieties (by showing that the laws still hold in the subalgebra). *)

Section contents.
  Context `{InVariety et A} `{@ClosedSubset et A _ _ P}. (* todo: why so ugly? *)

  Definition Pvars (vars: Vars et (carrier P) nat): Vars et A nat
    := λ s n, ` (vars s n).

  (* To prove that the laws still hold in the subalgebra, we first prove that evaluation in it
   is the same as evaluation in the original: *)

  Program Fixpoint heq {o}: op_type (carrier P) o → op_type A o → Prop :=
    match o with
    | ne_list.one _ => λ a b, `a = b
    | ne_list.cons _ _ => λ a b, ∀ u, heq (a u) (b u)
    end.

  Instance heq_proper: Proper ((=) ==> (=) ==> iff) (@heq o).
  Proof with intuition.
   intros o x y U x0 y0 K.
   induction o; simpl in *.
    destruct x, y.
    change (x = x1) in U.
    simpl in *.
    split; intro.
     transitivity x...
     transitivity x0...
    transitivity x1...
    transitivity y0...
   assert (∀ u, x u = y u). intros. apply U...
   split; repeat intro.
    apply -> (IHo (x u) (y u) (H1 u) (x0 (proj1_sig u)))...
    apply K...
   apply <- (IHo (x u) (y u) (H1 u) (x0 (proj1_sig u)))...
   apply K...
  Qed.

  Lemma heq_eval vars {o} (t: T et o): heq (eval et vars t) (eval et (Pvars vars) t).
  Proof with intuition.
   induction t; simpl...
     unfold Pvars...
    simpl in IHt1.
    generalize (IHt1 (eval et vars t3)). clear IHt1.
    apply heq_proper.
     pose proof (@eval_proper et (carrier P) _ _ _ nat (ne_list.cons y t1)).
     apply H1; try intro...
    pose proof (@eval_proper et A _ _ _ nat (ne_list.cons y t1)).
    apply H1...
    unfold heq in IHt2. (* todo: this wasn't needed in a previous Coq version *)
    rewrite IHt2.
    apply (@eval_proper et A _ _ _ nat (ne_list.one y))...
   unfold impl, algebra_op.
   generalize (subset_closed P o).
   unfold algebra_op.
   generalize (AlgebraOps0 o).
   intros.
   induction (et o); simpl in *...
  Qed.

  Lemma heq_eval_const vars {o} (t: T et (ne_list.one o)): ` (eval et vars t) = eval et (Pvars vars) t.
  Proof. apply (heq_eval vars t). Qed.
    (* todo: this specialization wasn't needed in a previous Coq version *)

  Lemma laws s: et_laws et s → ∀ vars: ∀ a, nat → carrier P a, eval_stmt et vars s.
  Proof with intuition.
   intros.
   generalize (@variety_laws et A _ _ _ s H1 (Pvars vars)). clear H1.
   destruct s as [x [? [t t0]]].
   induction x as [A| [x1 [t1 t2]]]; simpl in *; intros.
    unfold equiv, sig_equiv.
    rewrite (heq_eval_const vars t).
    rewrite (heq_eval_const vars t0)...
   apply IHx, H1.
   rewrite <- (heq_eval_const vars t1).
   rewrite <- (heq_eval_const vars t2)...
  Qed.

  (* Which gives us our variety: *)

  Global Instance: InVariety et (carrier P) := { variety_laws := laws }.

End contents.
