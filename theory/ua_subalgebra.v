Set Automatic Introduction.

Require Import
  RelationClasses Morphisms Program
  universal_algebra canonical_names util.

Section contents.

  Variables
    (et: EquationalTheory)
    (v: Variety et)
    (P: forall s: sorts et, v s -> Prop). (* P defines the "subset". *)

  Let op_type := op_type (sorts et).

  Let carrier s := sig (P s). (* Our elements are just those for which P holds *)

  Instance e: Equiv (carrier s) := fun a => sig_equiv (P a). (* ... with the existing equality. *)

  (* The obvious (and useful, in a moment) heterogenous equality between plain
   things and things in the subset: *)

  Fixpoint heq {o}: op_type carrier o -> op_type v o -> Prop :=
    match o with
    | constant x => fun a b => `a == b
    | function x y => fun a b => forall u, heq (a u) (b (`u))
    end.

  Instance heq_proper: Proper (equiv ==> equiv ==> iff) (@heq o).
  Proof with intuition.
   intros o x y H x0 y0 H0.
   induction o; simpl in *.
    destruct x, y.
    unfold equiv, e, sig_equiv, sig_relation in H.
    simpl in *.
    split; intro.
     transitivity x...
     transitivity x0...
    transitivity x1...
    transitivity y0...
   assert (forall u, x u == y u). intros. apply H. unfold e, sig_equiv, sig_relation. reflexivity.
   split; repeat intro.
    apply -> (IHo (x u) (y u) (H1 u) (x0 (proj1_sig u)))...
    apply H0...
   apply <- (IHo (x u) (y u) (H1 u) (x0 (proj1_sig u)))...
   apply H0...
  Qed.

  (* To construct a subalgebra, we require that P is closed under the operations: *)

  Fixpoint closed {o: OpType (sorts et)}: op_type v o -> Prop :=
    match o with
    | constant x => P x 
    | function x y => fun d => forall z: v x, P _ z -> closed (d z)
    end.

  Variable cl: forall o, closed (variety_op et v o).

  (* We can implement closed operations in the new algebra: *)

  Fixpoint close_op {d}: forall (o: op_type v d), closed o -> op_type carrier d :=
    match d with
    | constant _ => fun o c => exist _ o (c)
    | function x y => fun o c X => close_op (o (proj1_sig X)) (c (proj1_sig X) (proj2_sig X))
    end.

  (* And since we just required that all operations were closed, we have: *)

  Instance impl: Implementation et carrier := fun o => close_op (variety_op et v o) (cl o).

  (* It is not hard to show that this implementation is proper: *)

  Definition close_op_proper d (o0 o1: op_type v d)
    (P: closed o0) (Q: closed o1): o0 == o1 -> close_op o0 P == close_op o1 Q.
  Proof with intuition.
   induction d; simpl in *...
   intros [x p] [y q] H0.
   apply (IHd _ _ (P0 x p) (Q y q)), H...
  Qed.

  Lemma propers: @Propers et carrier (fun s => sig_equiv (P s)) impl.
  Proof. intro. apply close_op_proper, variety_propers. Qed.

  Definition Pvars (vars: Vars et carrier nat) := fun s1 n => ` (vars s1 n).

  (* To prove that the laws still hold in the subalgebra, we first prove that evaluation in it
   is the same as evaluation in the original: *)

  Lemma heq_eval vars {o} (t: T et o): heq (eval et vars t) (eval et (Pvars vars) t).
  Proof with intuition.
   induction t; simpl...
     unfold Pvars...
    simpl in *.
    pose proof (IHt1 (eval et vars t3)). clear IHt1.
    revert H.
    apply heq_proper.
     apply (@eval_proper et carrier _ _ propers nat (function (sorts et) y t1))...
     repeat intro. unfold equiv, sig_equiv, sig_relation...
    pose proof (@eval_proper et v _ _ _ nat (function (sorts et) y t1)).
    apply H...
   unfold op, impl.
   generalize (variety_op et v o) (cl o).
   intros.
   induction (et o); simpl in *...
  Qed.

  (* The laws hold: *)

  Lemma laws s: et_laws et s -> forall vars, eval_stmt et vars s.
  Proof with intuition.
   intros.
   generalize (variety_laws et v s H (Pvars vars)). clear H.
   destruct s as [x [? [t t0]]].
   induction x as [A| [x1 [t1 t2]]]; simpl in *; intros.
    unfold e, equiv, sig_equiv, sig_relation.
    rewrite (heq_eval vars t).
    rewrite (heq_eval vars t0)...
   apply IHx, H.
   rewrite <- (heq_eval vars t1).
   rewrite <- (heq_eval vars t2)...
  Qed.

  (* Which gives us our subalgebra: *)

  Definition subalgebra: Variety et :=
    MkVariety et carrier (fun s => sig_equiv (P s)) _ (fun _ => sig_equivalence _) propers laws.

  (* ... with proj1_sig as a homomorphism back to the original: *)

  Global Instance: HomoMorphism et subalgebra v (fun _ => @proj1_sig _ _).
  Proof with intuition.
   constructor.
    constructor...
    repeat intro.
    assumption.
   intro.
   unfold op, impl.
   generalize (cl o).
   generalize (variety_op et v o).
   induction (et o); simpl...
  Qed.

End contents.
