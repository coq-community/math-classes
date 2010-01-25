Set Automatic Introduction.

Require Import
  RelationClasses Relation_Definitions List Morphisms
  universal_algebra canonical_names ua_subalgebra.
Require ua_products.

Section contents. Variable et: EquationalTheory.

  Let op_type := op_type (sorts et).

  Variable v: Variety et.

  Let vv := ua_products.product et (fun _: bool => v).

  (* Given an equivalence on the algebra's carrier that respects its setoid equality... *)

  Context
    (e: forall s, relation (v s)).

  Section for_nice_e.

  Context
    (e_e: forall s, Equivalence (e s))
    (e_proper: forall s, Proper (equiv ==> equiv ==> iff) (e s)).

  (* We can show that that equivalence lifted to arbitrary operation types still respects the setoid equality: *)

  Let Q s x := e s (x true) (x false).
  Let lifted_e := @op_type_equiv (sorts et) v e.
  Let lifted_normal := @op_type_equiv (sorts et) v (variety_equiv et v).

  Instance lifted_e_proper o: Proper (equiv ==> equiv ==> iff) (lifted_e o).
  Proof with intuition.
   induction o; simpl. intuition.
   repeat intro.
   unfold respectful.
   split; intros.
    assert (x x1 == y x1). apply H...
    assert (x0 y1 == y0 y1). apply H0...
    apply (IHo (x x1) (y x1) H3 (x0 y1) (y0 y1) H4)...
   assert (x x1 == y x1). apply H...
   assert (x0 y1 == y0 y1). apply H0...
   apply (IHo (x x1) (y x1) H3 (x0 y1) (y0 y1) H4)...
  Qed. (* todo: clean up *)

  (* With that out of the way, we show that there are two equivalent ways of stating compatibility with the
   algebra's operations: *)

    (* 1: the direct way with Propers; *)
  Let ePropers := @Propers et v e _. 

    (* 2: the indirect way of saying that the relation as a set of pairs is a subalgebra in the product algebra: *)
  Let eSub := ua_subalgebra.ops_closed et vv Q.

  Lemma forth: ePropers -> eSub.
  Proof with intuition.
   intros P o.
   simpl.
   unfold ua_products.Implementation_instance_0.
   set (f := fun _: bool => variety_op et v o).
   assert (lifted_e _ (f true) (f false)). unfold f. apply P.
   assert (forall b, Proper (lifted_e (et o)) (f b))...
   clearbody f.
   induction (et o)...
   simpl in *...
  Qed.

  Lemma back: eSub -> ePropers.
  Proof with intuition.
   intros ops_closed o.
   generalize (ops_closed o). clear ops_closed. (* todo: must be a cleaner way *)
   simpl.
   unfold ua_products.Implementation_instance_0.
   intro.
   change (lifted_e _ (variety_op et v o) (variety_op et v o)).
   set (f := fun _: bool => variety_op et v o) in *.
   assert (forall b, lifted_normal _ (f b) (f b)). intros. apply variety_propers.
   change (lifted_e (et o) (f true) (f false)).
   clearbody f.
   induction (et o)...
   simpl in *.
   repeat intro.
   unfold respectful in H0.
   apply (IHo0 (fun b => f b (if b then x else y)))...
  Qed.

  Lemma back_and_forth: eSub <-> ePropers.
  Proof. split; intro; [apply back | apply forth]; assumption. Qed.

  End for_nice_e.

  (* This justifies the following definition of a congruence: *)

  Class Congruence: Prop :=
    { congruence_proper:> forall s, Proper (equiv ==> equiv ==> iff) (e s)
    ; congruence_equiv:> forall s, Equivalence (e s)
    ; congruence_propers:> @Propers et v e _
    }.

End contents.
