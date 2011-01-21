Require Import
  Morphisms RelationClasses Equivalence Setoid
  abstract_algebra interfaces.functors categories.

Section natural_transformations_id_comp.

  Context
    `{Category A} `{Category B} `{!Functor (f: A → B) f'}
    `{!Functor (f: A → B) f'} `{!Functor (g: A → B) g'} `{!Functor (h: A → B) h'}
    `{!NaturalTransformation (m:f⇛g)} `{!NaturalTransformation (n:g⇛h)}.

  Global Instance id_transformation: NaturalTransformation (λ a, cat_id: f a ⟶ f a).
  Proof. intros ???. rewrite id_l, id_r; reflexivity. Qed.

  Global Instance compose_transformation: NaturalTransformation (λ a, n a ◎ m a).
  Proof.
    intros ???.
    rewrite <- comp_assoc, natural, comp_assoc, natural, comp_assoc; reflexivity.
  Qed.

End natural_transformations_id_comp.

Section contents.

  Context `(Category A) `(Category B).

  Record Object: Type := object
    { map_obj:> A → B
    ; Fmap_inst:> Fmap map_obj
    ; Functor_inst: Functor map_obj _ }.

  Implicit Arguments object [[Fmap_inst] [Functor_inst]].

  Global Existing Instance Fmap_inst.
  Global Existing Instance Functor_inst.

  Record Arrow (F G : Object) : Type := arrow
    { eta:> map_obj F ⇛ map_obj G
    ; NaturalTransformation_inst: NaturalTransformation eta }.

  Implicit Arguments arrow [[F] [G]].

  Global Existing Instance NaturalTransformation_inst.

  Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances.

  Section arrow_setoid. Context (F G: Object).

    Global Program Instance e: Equiv (F ⟶ G) :=
      λ m n, ∀ x: A, m x = n x.

    Let e_refl: Reflexive e.
    Proof. intro a; red; reflexivity. Qed.

    Let e_sym: Symmetric e.
    Proof. intros m n Hmn a. red in Hmn. rewrite Hmn. reflexivity. Qed.

    Let e_trans: Transitive e.
    Proof. intros m n o Hmn Hno a. red in Hmn, Hno. rewrite Hmn, Hno. reflexivity. Qed.

    Instance: Equivalence e.
    Global Instance: Setoid (F ⟶ G).

  End arrow_setoid.
 
  Global Instance: CatId Object := λ _, arrow (λ _, cat_id) _.
  Global Instance: CatComp Object := λ _ _ _ m n, arrow (λ a, m a ◎ n a) _.

  Global Instance: ∀ x y z: Object,
    Proper ((=) ==> (=) ==> (=)) ((◎): (y ⟶ z) → (x ⟶ y) → (x ⟶ z)).
  Proof.
    intros ????? Hx ?? Hy a.
    simpl. rewrite (Hx a), (Hy a). reflexivity.
  Qed.

  Let id_l' (x y: Object) (F: x ⟶ y): cat_id ◎ F = F.
  Proof. intro. simpl. apply id_l. Qed.

  Let id_r' (x y: Object) (F: x ⟶ y): F ◎ cat_id = F.
  Proof. intro. simpl. apply id_r. Qed.

  Lemma comp_assoc' (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z): c ◎ (b ◎ a) = (c ◎ b) ◎ a.
  Proof. intro. simpl. apply comp_assoc. Qed.

  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.

End contents.

Implicit Arguments Object [[Arrows0] [H] [CatId0] [CatComp0] [Arrows1] [H1] [CatId1] [CatComp1]].
Implicit Arguments CatComp_instance_0 [[A] [Arrows0] [CatId0] [CatComp0] [B] [Arrows1] [H1] [CatId1] [CatComp1] [H2]].
