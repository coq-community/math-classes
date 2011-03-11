(* To be imported qualified. *)

Set Automatic Coercions Import.
Require
  categories.variety categories.product forget_algebra forget_variety.
Require Import
  Program Morphisms
  abstract_algebra universal_algebra ua_homomorphisms workaround_tactics.

Inductive op := mult.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with mult => 2%nat end).

Section laws.
  Global Instance: SemiGroupOp (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := variety.Object theory.

Definition forget: Object → setoid.Object :=
  @product.project unit
    (λ _, setoid.Object)
    (λ _, _: Arrows setoid.Object) _
    (λ _, _: CatId setoid.Object)
    (λ _, _: CatComp setoid.Object) 
    (λ _, _: Category setoid.Object) tt
     ∘ forget_algebra.object theory ∘ forget_variety.forget theory.
  (* todo: too ugly *)

(* Now follow a series of encoding/decoding functions to convert between the
 specialized Monoid/Monoid_Morphism type classes and the universal
 Algebra/InVariety/HomoMorphism type classes instantiated with the above
 signature and theory. *)

Instance encode_operations A `{!SemiGroupOp A}: AlgebraOps sig (λ _, A) :=
  λ o, match o with mult => sg_op end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: SemiGroupOp (A tt) := algebra_op mult.
End decode_operations.

Section encode_variety_and_ops.
  Context A `{SemiGroup A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor; intros []; simpl; apply _. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (λ _, A).
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
   apply associativity.
  Qed.

  Definition object: Object := variety.object theory (λ _, A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{∀ u, Equiv (A u)} `{!SemiGroup (A tt)}: Algebra theory A .
Proof. constructor; intros []; simpl in *; try apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: SemiGroup (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor; try apply _.
  intro. apply_simplified (laws _ e_mult_assoc).
 apply (algebra_propers mult)...
Qed.

Lemma encode_morphism_only
  `{AlgebraOps theory A} `{∀ u, Equiv (A u)}
  `{AlgebraOps theory B} `{∀ u, Equiv (B u)}
  (f: ∀ u, A u → B u) `{!SemiGroup_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 pose proof (sgmor_a (f:=f tt)).
 pose proof (sgmor_b (f:=f tt)).
 constructor.
    intros []. apply _.
   intros []; simpl.
   apply preserves_sg_op.
  apply (encode_algebra_only).
 apply encode_algebra_only.
Qed.

Lemma encode_morphism_and_ops `{SemiGroup_Morphism A B f}:
  @HomoMorphism sig (λ _, A) (λ _, B) _ _ ( _) ( _) (λ _, f).
Proof. intros. apply encode_morphism_only; assumption. Qed.

Lemma decode_morphism_and_ops
  `{InVariety theory x} `{InVariety theory y} `{!HomoMorphism theory x y f}:
    SemiGroup_Morphism (f tt).
Proof.
 pose proof (homo_proper theory x y f tt).
 constructor; try apply _.
 apply (preserves theory x y f mult).
Qed.

(* Finally, we use these encoding/decoding functions to specialize some universal results: *)
Section specialized.
  Context (A B C: Type)
    `{!SemiGroupOp A} `{!Equiv A}
    `{!SemiGroupOp B} `{!Equiv B}
    `{!SemiGroupOp C} `{!Equiv C}
    (f: A → B) (g: B → C).

  Global Instance id_morphism `{!SemiGroup A}: SemiGroup_Morphism id.
  Proof. repeat (constructor; try apply _); reflexivity. Qed.

  Global Instance compose_morphisms `{!SemiGroup A, !SemiGroup B, !SemiGroup C}
    `{!SemiGroup_Morphism f} `{!SemiGroup_Morphism g}: SemiGroup_Morphism (g ∘ f).
  Proof.
   pose proof (encode_morphism_and_ops (f:=f)) as P.
   pose proof (encode_morphism_and_ops (f:=g)) as Q.
   pose proof (@compose_homomorphisms theory _ _ _ _ _ _ _ _ _ _ _ P Q).
   apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ H).
  Qed.

  Global Instance: ∀ `{H: SemiGroup_Morphism A B f} `{!Inverse f},
    Bijective f → SemiGroup_Morphism (inverse f).
  Proof.
   intros.
   pose proof (encode_morphism_and_ops (f:=f)) as P.
   pose proof (@invert_homomorphism theory _ _ _ _ _ _ _ _ _ _ P) as Q.
   destruct H.
   apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ Q).
  Qed.
End specialized.
