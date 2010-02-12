(* Show that algebras with homomorphisms between them form a category. *)

Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program universal_algebra theory.categories.

Require
  categories.cat categories.setoid categories.product.


Inductive Propified (A: Type): Prop := propify: A -> Propified A.

Class Functional {A B: Type} (R: A -> B -> Prop): Prop :=
  functional: forall a, exists b, R a b /\ forall b', R a b' -> b' = b.

(*
Section test.

  Context {A B: Type}.

  Class Functional (R: A -> B -> Prop): Prop :=
    functional: forall a, exists b, R a b /\ forall b', R a b' -> b' = b.

  Definition make_func (R: A -> B -> Prop): Functional R -> (A -> Propified B).
   intro.
   intro.
   destruct (H X).
   destruct H0.
   apply propify.
   exact x.
  Defined.

  Variable (f: A -> Propified B).

  Definition R (a: A) (b: B): Prop := f a = propify _ b.

  Goal Functional R.
   intro.
   case_eq (f a).
   intros.
   exists b.
   unfold R.
   split.
    assumption.
   intros.
   rewrite H in H0.
   clear H.
   simple inversion H0.
   inversion H.

   exists X.

   intro.
   intro.
   destruct (H X).
   destruct H0.
   apply propify.
   exact x.
  Defined.
   
*)
Section contents.

  Variable sign: Signature.

  Record Object: Type := object
    { algebra_carriers:> sorts sign -> Type
    ; algebra_equiv: forall a, Equiv (algebra_carriers a)
    ; algebra_ops: AlgebraOps sign algebra_carriers
    ; algebra_proof: Algebra sign algebra_carriers
    }.

  Global Implicit Arguments object [[algebra_equiv] [algebra_ops] [algebra_proof]].

  Global Existing Instance algebra_equiv.
  Global Existing Instance algebra_ops.
  Global Existing Instance algebra_proof.

  Definition Arrow (X Y: Object): Type := sig (HomoMorphism sign X Y).

  Definition RelArrow (X Y: Object): Type :=
   sig (fun R: forall x0: sorts sign, X x0 -> Y x0 -> Prop => (forall i, Functional (R i)) /\
     forall f, (forall i x, R _ x (f i x)) -> HomoMorphism sign X Y f).

  Program Definition arrow `{Algebra sign A} `{Algebra sign B}
    f `{!HomoMorphism sign A B f}: Arrow (object A) (object B) := f.

  Global Program Instance: CatId Object Arrow := fun _ _ => id.

  Program Instance: CatId Object RelArrow := fun _ _ => eq.
  Next Obligation.
   split.
   repeat intro.
   exists a.
   split.
   intuition.
   intuition.
   intros.
   apply (HomoMorphism_Proper sign H H f (fun _ => id)).
    intros.
    unfold id.
    symmetry.
    rewrite (H0 a x) at 1.
    reflexivity.
   apply _.
  Qed.

  Global Program Instance comp: CatComp Object Arrow := fun _ _ _ f g v => (`f) v ∘ (`g) v.
  Next Obligation. destruct f, g. apply _. Qed.

  Definition comprels {A B C} (R: A -> B -> Prop) (R': B -> C -> Prop) (a: A) (c: C): Prop :=
   exists b, R a b /\ R' b c.
(*
  Instance rel_comp: CatComp Object RelArrow.
   unfold CatComp.
   intros.
   unfold RelArrow.
   destruct X.
   destruct X0.
   exists (fun (s: sorts sign) => comprels (x1 s) (x0 s)).
   split.
    admit.
   intros.
   unfold comprels in H.
   constructor.
     intro.
     
     admit.
    admit.
   apply _.
  apply _.
   

   simpl in *.

   simpl in *.
   intros.

 := fun _ _ _ f g v => (`f) v ∘ (`g) v.
  Next Obligation. destruct f, g. apply _. Qed.
*)

  Global Program Instance e x y: Equiv (Arrow x y)
    := fun x y => forall b, pointwise_relation _ equiv (x b) (y b).

  Global Instance: forall x y, Equivalence (e x y).
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ? ? E ? ?. symmetry. apply E.
   intros ? ? ? E F ? ?. rewrite (E _ _). apply F.
  Qed.

  Instance: Proper (equiv ==> equiv ==> equiv) (comp x y z).
  Proof.
   intros ? ? ? x0 ? E ? ? F ? ?.
   simpl. unfold compose. unfold equiv, e, pointwise_relation in E, F.
   destruct (proj2_sig x0). unfold equiv. rewrite F, E. reflexivity.
  Qed.

  Global Instance cat: Category Object Arrow.
  Proof. constructor; try apply _; repeat intro; unfold equiv; reflexivity. Qed.

  (* Definition obj: cat.Object := cat.Build_Object Object Arrow e _ _ _.
    Risks universe inconsistencies.. *)

  Definition BaseObject := product.Object (sorts sign) (fun _ => setoid.Object).
  Definition BaseArrow: BaseObject -> BaseObject -> Type
    := product.Arrow (sorts sign) _ (fun _ => setoid.Arrow).

  Coercion base_object (X: Object): BaseObject := fun z => setoid.object (X z) equiv _.

  Definition base_arrow {X Y} (a: Arrow X Y): BaseArrow X Y.
   intro.
   destruct a.
   apply (@setoid.arrow (setoid.object _ _ _) (setoid.object _ _ _) (x i)).
   destruct h.
   apply _.
  Defined.

  Global Instance mono: forall (a: Arrow X Y), Mono (base_arrow a) -> Mono a.
  Proof with simpl in *.
   repeat intro.
   assert (base_arrow f == base_arrow g).
    apply (H z (base_arrow f) (base_arrow g)). clear H.
    intro.
    pose proof (H0 i). clear H0.
    destruct a, f, g.
    repeat intro...
    unfold pointwise_relation, compose in *.
    destruct X, Y, z...
    change (x2 == y) in H0.
    change (x i (x0 i x2) == x i (x1 i y)).
    destruct h, h0, h1.
    rewrite H0.
    apply H.
   clear H0.
   destruct a, f, g, X, Y, z.
   destruct h, h0, h1...
   pose proof (H1 b a0 a0). clear H.
   apply H0.
   change (a0 == a0).
   reflexivity.
  Qed. (* todo: clean up (the [change]s shouldn't be necessary *)

End contents.
