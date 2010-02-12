Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program
  abstract_algebra theory.categories.

Section contents.

  Inductive Object := object { T:> Type; e: T -> T -> Prop; setoid_proof: Equivalence e }.
    (* We don't use the type [Equiv T] for e because it leads to universe consistency
     problems in theory/ua_forget. Hopefully when Coq gets universe polymorphism for
     definitions (like Equiv), we can use the proper type again. *)

  Global Instance: forall o, Equiv (T o) := e.
  Existing Instance setoid_proof.

  Inductive Arrow (A B: Object) := arrow { f:> A -> B; mor: Setoid_Morphism f }.

  Global Existing Instance mor.

  Global Instance arr_eq A B: Equiv (Arrow A B)
    := fun m n => forall x y, x == y -> m x == n y.

  Global Instance: forall A B, Equivalence (arr_eq A B).
  Proof with try reflexivity.
   constructor.
     intros ? ? ? E. rewrite E...
    intros ? ? E ? ? ?. symmetry. apply E. symmetry. assumption.
   intros ? x ? H H0 ? v H1.
   rewrite H1.
   transitivity (x v). apply H... apply H0...
  Qed.

  Global Program Instance: CatId Object Arrow
    := fun _ => arrow _ _ id _.

  Global Program Instance cc: CatComp Object Arrow
    := fun _ _ _ a b => arrow _ _ (compose a b) _.

  Global Instance: forall x y z, Proper (equiv ==> equiv ==> equiv) (cc x y z).
  Proof. repeat intro. simpl. firstorder. Qed.

  Let cc_assoc w x y z (a: Arrow w x) (b: Arrow x y) (c: Arrow y z): comp c (comp b a) == comp (comp c b) a.
  Proof. intros ? ? E. simpl. unfold compose. rewrite E. reflexivity. Qed.

  Let id_l x y (a : Arrow y x): comp cat_id a == a.
  Proof. intros ? ? E. simpl. unfold compose, id. rewrite E. reflexivity. Qed.

  Let id_r x y (a : Arrow x y): comp a cat_id == a.
  Proof. intros ? ? E. simpl. unfold compose, id. rewrite E. reflexivity. Qed.

  Global Instance: Category Object Arrow := { comp_assoc := cc_assoc; id_l := id_l; id_r := id_r }.

  Section product. Context {Index: Type} (c: Index -> Object).

    Definition product_obj: Object := object (forall i, c i) (fun x y => forall i, x i == y i) _.

    Program Definition project (i: Index): Arrow product_obj (c i) := arrow _ _ (fun x => x i) _.
    Next Obligation. constructor; try apply _. firstorder. Qed.

    Program Definition factor (d: Object) (df: forall i, Arrow d (c i)): Arrow d product_obj :=
     arrow d product_obj (fun x y => df y x) _.
    Next Obligation. constructor; try apply _. intros x y E i. rewrite E. reflexivity. Qed.

  End product.

  Instance: Producer Object Arrow := fun I c => mkProduct c (product_obj c) (project c) (factor c).

  Instance: Produces Object Arrow.
  Proof.
   split.
    intros ? ? ? E. rewrite E. reflexivity.
   intros ? E' ? x E. rewrite E.
   intro i. simpl. symmetry.
   apply (E' i x x). reflexivity.
  Qed.

  Global Instance mono: forall (a: Arrow X Y), Injective a -> Mono a.
  Proof.
   intros ? ? ? ? ? ? ? E ? ? U.
   pose proof (E _ _ U).
   firstorder.
  Qed.

End contents.
