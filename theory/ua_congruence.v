Set Automatic Introduction.

Require Import
  RelationClasses Relation_Definitions List Morphisms
  universal_algebra canonical_names ua_subalgebraT util.
Require Import Program.
Require ua_products.

Require categories.

Section contents. Variable et: Signature.

  Notation op_type := (op_type (sorts et)).

  Context `{!@Algebra et v ve vo}.

  Notation vv := (ua_products.carrier et bool (λ _: bool => v)).

  Let hint := @ua_products.product_algebra et bool (λ _ => v) _ _ _.

  (* Given an equivalence on the algebra's carrier that respects its setoid equality... *)

  Context (e: Π s, relation (v s)).

  Section for_nice_e.

  Context
    (e_e: Π s, Equivalence (e s))
    (e_proper: Π s, Proper (equiv ==> equiv ==> iff) (e s)).

  (* We can show that that equivalence lifted to arbitrary operation types still respects the setoid equality: *)

  Let Q s x := e s (x true) (x false).
  Let lifted_e := @op_type_equiv (sorts et) v e.
  Let lifted_normal := @op_type_equiv (sorts et) v ve.

  Instance lifted_e_proper o: Proper (equiv ==> equiv ==> iff) (lifted_e o).
  Proof with intuition.
   induction o; simpl. intuition.
   repeat intro.
   unfold respectful.
   split; intros.
    assert (x x1 = y x1). apply H0...
    assert (x0 y1 = y0 y1). apply H1...
    apply (IHo (x x1) (y x1) H4 (x0 y1) (y0 y1) H5)...
   assert (x x1 = y x1). apply H0...
   assert (x0 y1 = y0 y1). apply H1...
   apply (IHo (x x1) (y x1) H4 (x0 y1) (y0 y1) H5)...
  Qed. (* todo: clean up *)

  (* With that out of the way, we show that there are two equivalent ways of stating compatibility with the
   algebra's operations: *)

    (* 1: the direct way with Algebra; *)
  Let eAlgebra := @Algebra et v e _.

    (* 2: the indirect way of saying that the relation as a set of pairs is a subalgebra in the product algebra: *)
  Let eSub := @ua_subalgebraT.ClosedSubset et vv _ _ Q.

  Lemma eAlgebra_eSub: eAlgebra → eSub.
  Proof with intuition.
   intros.
   constructor.
    unfold Q.
    repeat intro.
    constructor; intro.
     rewrite <- (H1 true), <- (H1 false)...
    rewrite (H1 true), (H1 false)...
   intro o.
   simpl.
   unfold algebra_op, ua_products.product_ops, algebra_op.
   set (f := λ _: bool => vo o).
   assert (Π b, Proper equiv (f b)).
    intro.
    unfold f.
    apply algebra_propers.
    apply _.
   assert (lifted_e _ (f true) (f false)). unfold f.
    unfold lifted_e.
    destruct H0.
    apply algebra_propers.
   assert (Π b, Proper (lifted_e (et o)) (f b))...
   clearbody f.
   induction (et o)...
   simpl in *...
   apply IHo0...
   apply H1...
  Qed. (* todo: clean up *)

  Lemma eSub_eAlgebra: eSub → eAlgebra.
  Proof with intuition.
   intros [proper closed].
   constructor. unfold abstract_algebra.Setoid. apply _.
   intro o.
   generalize (closed o). clear closed. (* todo: must be a cleaner way *)
   unfold algebra_op.
   simpl.
   unfold ua_products.product_ops.
   intro.
   change (lifted_e _ (algebra_op et o) (algebra_op et o)).
   set (f := λ _: bool => algebra_op et o) in *.
   assert (Π b, lifted_normal _ (f b) (f b)). intros.
    subst f. simpl.
    apply algebra_propers...
   change (lifted_e (et o) (f true) (f false)).
   clearbody f.
   induction (et o)...
   simpl in *.
   repeat intro.
   unfold respectful in H0.
   apply (IHo0 (λ b => f b (if b then x else y)))...
  Qed. (* todo: clean up *)

  Lemma back_and_forth: iffT eSub eAlgebra.
  Proof. split; intro; [apply eSub_eAlgebra | apply eAlgebra_eSub]; assumption. Qed.

  End for_nice_e.

  (* This justifies the following definition of a congruence: *)

  Class Congruence: Prop :=
    { congruence_proper:> Π s, Proper (equiv ==> equiv ==> iff) (e s)
    ; congruence_quotient:> @Algebra et v e _
    }.

  (* Todo: Show that congruences yield varieties, too. *)

End contents.

Section in_domain.

  Context {A B} {R: Equiv B} (f: A → B).

  Definition in_domain: Equiv A := λ x y => f x = f y. (* todo: use pointwise thingy *)

  Global Instance in_domain_equivalence: Equivalence R → Equivalence in_domain.
  Proof with intuition.
   constructor; repeat intro; unfold equiv, in_domain in *...
   transitivity (f y)...
  Qed.

End in_domain.

Section first_iso.

(* "If A and B are algebras, and f is a homomorphism from A to B, then
 the equivalence relation Φ on A defined by a~b if and only if f(a)=f(b) is
 a congruence on A, and the algebra A/Φ is isomorphic to the image
 of f, which is a subalgebra of B." *)

  Context `{Algebra sign A} `{Algebra sign B} `{!HomoMorphism sign A B f}.

  Notation phi := (λ s => in_domain (f s)).

  Lemma square o0 x x' y y':
    Preservation sign A B f x x' →
    Preservation sign A B f y y' →
    op_type_equiv (sorts sign) B o0 x' y' →
    @op_type_equiv (sorts sign) A (λ s: sorts sign => @in_domain (A s) (B s) (e0 s) (f s)) o0 x y.
  Proof.
   induction o0.
    simpl.
    intros.
    unfold in_domain.
    rewrite H3, H4.
    assumption.
   simpl in *.
   repeat intro.
   unfold in_domain in H6.
   unfold respectful in H5.
   simpl in *.
   pose proof (H3 x0).
   pose proof (H3 y0). clear H3.
   pose proof (H4 x0).
   pose proof (H4 y0). clear H4.
   apply (IHo0 (x x0) (x' (f a x0)) (y y0) (y' (f a y0)) H7 H9).
   apply H5.
   assumption.
  Qed.

  Instance co: Congruence sign phi.
  Proof with intuition.
   constructor.
    repeat intro.
    unfold in_domain.
    rewrite H3, H4...
   constructor; intro.
    unfold abstract_algebra.Setoid. apply _.
   unfold algebra_op.
   generalize (preserves sign A B f o).
   generalize (@algebra_propers sign B _ _ _ o).
   unfold algebra_op.
   generalize (H o), (H1 o).
   induction (sign o); simpl in *; repeat intro.
    apply _.
   apply (square _ _ _ _ _ (H4 x) (H4 y))...
  Qed.

  Definition image s (b: B s): Type := sigT (λ a => f s a = b).

  Lemma image_proper: Π s (x0 x' : B s), x0 = x' → iffT (image s x0) (image s x').
  Proof. intros ??? E. split; intros [v ?]; exists v; rewrite E in *; assumption. Qed.

  Instance: ClosedSubset image.
  Proof with intuition.
   constructor; repeat intro.
    split; intros [q p]; exists q; rewrite p...
   generalize (preserves sign A B f o).
   generalize (@algebra_propers sign B _ _ _ o).
   unfold algebra_op.
   generalize (H1 o), (H o).
   induction (sign o); simpl; intros.
    exists o1...
   destruct X.
   apply (@op_closed_proper sign B _ _ _ image image_proper _ (o1 z) (o1 (f a x))).
    apply H3...
   apply IHo0 with (o2 x)...
   apply _.
  Qed.

  Definition quot_obj := algebra.object sign A (algebra_equiv:=phi). (* A/Φ *)
  Definition subobject := algebra.object sign (ua_subalgebraT.carrier image).

  Program Definition back: subobject ⟶ quot_obj := λ _ X => projT1 (projT2 X).

  Next Obligation. Proof with try apply _; intuition.
   repeat constructor...
    intros [x [i E']] [y [j E'']] E.
    change (x = y) in E.
    change (f a i = f a j).
    rewrite E', E''...
   unfold ua_subalgebraT.impl.
   generalize (subset_closed image o).
   unfold algebra_op.
   generalize (H o) (H1 o) (preserves sign A B f o)
     (_: Proper equiv (H o)) (_: Proper equiv (H1 o)).
   induction (sign o); simpl; intros ? ? ? ? ?.
    intros [? E]. change (f a x = f a o0). rewrite E...
   intros ? [x [? E]]. apply IHo0... simpl in *. rewrite <- E...
  Defined.

  Program Definition forth: quot_obj ⟶ subobject := 
    λ a X => existT _ (f a X) (existT _ X (reflexivity _)).

  Next Obligation. Proof with try apply _; intuition.
   repeat constructor... intro...
   unfold ua_subalgebraT.impl.
   generalize (subset_closed image o).
   unfold algebra_op.
   generalize (H o) (H1 o) (preserves sign A B f o)
     (_: Proper equiv (H o)) (_: Proper equiv (H1 o)).
   induction (sign o); simpl...
   apply IHo0...
  Qed.

  Theorem first_iso: categories.iso_arrows back forth.
  Proof.
   split. intro. reflexivity.
   intros ? [? [? ?]]. assumption.
  Qed.

End first_iso.
