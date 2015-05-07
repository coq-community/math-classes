Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.functors MathClasses.theory.categories.

Section natural_transformations_id_comp.
  Context
    `{Category A} `{Category B} `{!Functor (f: A → B) f'}
    `{!Functor (f: A → B) f'} `{!Functor (g: A → B) g'} `{!Functor (h: A → B) h'}
    `{!NaturalTransformation (m:f⇛g)} `{!NaturalTransformation (n:g⇛h)}.

  Global Instance id_transformation: NaturalTransformation (λ a, cat_id: f a ⟶ f a).
  Proof. intros ???. rewrite left_identity, right_identity; reflexivity. Qed.

  Global Instance compose_transformation: NaturalTransformation (λ a, n a ◎ m a).
  Proof.
    intros ???.
    rewrite <- associativity, natural, associativity, natural, associativity; reflexivity.
  Qed.
End natural_transformations_id_comp.

Record Object A `{Arrows A} `{∀ x y : A, Equiv (x ⟶ y)} `{!CatId A} `{!CatComp A}
     B `{Arrows B} `{∀ x y : B, Equiv (x ⟶ y)} `{!CatId B} `{!CatComp B} : Type := object
  { map_obj:> A → B
  ; Fmap_inst:> Fmap map_obj
  ; Functor_inst: Functor map_obj _ }.
Existing Instance Fmap_inst.
Existing Instance Functor_inst.

Arguments Object _ {Aarrows Aeq Aid Acomp} _ {Barrows Beq Bid Bcomp} : rename.
Arguments object {A Aarrows Aeq Aid Acomp B Barrows Beq Bid Bcomp} {Fmap Functor} _ : rename.
Arguments map_obj {A Aarrows Aeq Aid Acomp B Barrows Beq Bid Bcomp} _ _ : rename.

Record Arrow `{Arrows A} `{∀ x y : A, Equiv (x ⟶ y)} `{!CatId A} `{!CatComp A}
     `{Arrows B} `{∀ x y : B, Equiv (x ⟶ y)} `{!CatId B} `{!CatComp B} (F G : Object A B) : Type := arrow
  { eta:> map_obj F ⇛ map_obj G
  ; NaturalTransformation_inst: NaturalTransformation eta }.
Existing Instance NaturalTransformation_inst.

Arguments arrow {A Aarrows Aeq Aid Acomp B Barrows Beq Bid Bcomp F G} _ _ : rename.
Arguments eta {A Aarrows Aeq Aid Acomp B Barrows Beq Bid Bcomp F G} _ _ : rename.

Section contents.
  Context `{Category A} `{Category B}.

  Global Instance: Arrows (Object A B) := Arrow.

  Section arrow_setoid.
    Context (F G : Object A B).

    Global Program Instance e: Equiv (F ⟶ G) :=
      λ m n, ∀ x: A, m x = n x.

    Instance e_refl: Reflexive e.
    Proof. intro a; red; reflexivity. Qed.

    Instance e_sym: Symmetric e.
    Proof. intros m n Hmn a. red in Hmn. rewrite Hmn. reflexivity. Qed.

    Instance e_trans: Transitive e.
    Proof. intros m n o Hmn Hno a. red in Hmn, Hno. rewrite Hmn, Hno. reflexivity. Qed.

    Instance: Equivalence e := {}.
    Global Instance: Setoid (F ⟶ G) := {}.
  End arrow_setoid.

  Global Instance: CatId (Object A B) := λ _, arrow (λ _, cat_id) _.
  Global Instance: CatComp (Object A B) := λ _ _ _ m n, arrow (λ a, m a ◎ n a) _.

  Global Instance: ∀ x y z: Object A B,
    Proper ((=) ==> (=) ==> (=)) ((◎): (y ⟶ z) → (x ⟶ y) → (x ⟶ z)).
  Proof.
    intros ????? Hx ?? Hy a.
    simpl. rewrite (Hx a), (Hy a). reflexivity.
  Qed.

  Instance: ∀ x y: Object A B, LeftIdentity (comp x y y) cat_id.
  Proof. repeat intro. simpl. apply left_identity. Qed.

  Instance: ∀ x y: Object A B, RightIdentity (comp x x y) cat_id.
  Proof. repeat intro. simpl. apply right_identity. Qed.

  Instance: ArrowsAssociative (Object A B).
  Proof. repeat intro. simpl. apply associativity. Qed.

  Global Instance: Category (Object A B) := {}.
End contents.
