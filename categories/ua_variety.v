(* Show that Varieties with homomorphisms between them form a category. *)

Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program universal_algebra.
Require
  categories.cat.

Section contents.

  Variable et: EquationalTheory.

  Let Object := Variety et.

  Definition Arrow (X Y: Object): Type := sig (HomoMorphism et X Y).

  Global Program Instance: CatId Object Arrow := fun _ _ => id.

  Next Obligation.
   constructor. intro. apply _.
   unfold id. intro.
   generalize (@op et (variety_atomics _ H) _ o). intro.
   induction (sign_sig et o); simpl; intuition.
  Qed.

  Global Program Instance comp: CatComp Object Arrow := fun _ _ _ f g v => (`f) v ∘ (`g) v.

  Next Obligation. Proof with try reflexivity; try apply _; auto.
   constructor; intros.
    destruct f, g. apply (compose_setoid_morphisms _ _ _)...
   generalize (@op _ H _ o), (@op _ H0 _ o), (@op _ H1 _ o),
    (@preserves et _ _ _ _ _ _ _ (proj2_sig g) o),
    (@preserves et _ _ _ _ _ _ _ (proj2_sig f) o).
   induction (et o); simpl; intros.
    unfold compose. destruct (proj2_sig f). rewrite H2...
   unfold compose in *.
   apply IHo0 with (o2 ((`g) a x))...
  Qed. (* todo: clean up *)

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
   destruct (proj2_sig x0). rewrite F, E. reflexivity.
  Qed.

  Global Instance cat: Category Object Arrow.
  Proof. constructor; try apply _; repeat intro; reflexivity. Qed.

  (* Definition obj: cat.Object := cat.Build_Object Object Arrow e _ _ _.
    Defining this causes a universe inconsistency when this module
    is imported in theory/ua_forget.. *)

End contents.

(* Also see:
      - theory/ua_products, which shows that this category has products
*)
