(* To be imported qualified. *)

Set Automatic Coercions Import.
Require
  categories.variety categories.product forget_algebra forget_variety groups.
Require Import
  Program Morphisms
  abstract_algebra universal_algebra ua_homomorphisms workaround_tactics.

Inductive op := mult | inv | one.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with one => O | inv => 1%nat | mult => 2%nat end).

Section laws.
  Global Instance: SemiGroupOp (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).
  Global Instance: MonoidUnit (Term0 sig nat tt) := Op sig nat one.
  Global Instance: GroupInv (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (Op sig nat inv) x.

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z)
    | e_mult_1_l: Laws (mon_unit & x === x)
    | e_mult_1_r: Laws (x & mon_unit === x)
    | e_mult_inv_l: Laws (-x & x === mon_unit)
    | e_mult_inv_r: Laws (x & -x === mon_unit).
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

Instance encode_operations A `{!SemiGroupOp A} `(GroupInv A) `{!MonoidUnit A}: AlgebraOps sig (λ _, A) :=
  λ o, match o with mult => sg_op | inv => group_inv | one => mon_unit: A end.

Section decode_operations.
  Context `{AlgebraOps theory A}.

  Global Instance: MonoidUnit (A tt) := algebra_op one.
  Global Instance: SemiGroupOp (A tt) := algebra_op mult.
  Global Instance: GroupInv (A tt) := algebra_op inv.
End decode_operations.

Section encode_variety_and_ops.
  Context A `{Group A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (λ _, A).
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
       apply associativity.
      apply left_identity.
     apply right_identity.
    eapply ginv_l. 
   eapply ginv_r.
  Qed.

  Definition object: Object := variety.object theory (λ _, A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{∀ u, Equiv (A u)} `{!Group (A tt)}: Algebra theory A .
Proof. constructor; intros []; simpl in *; try apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: Group (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 repeat constructor; try apply _.
       intro. apply_simplified (laws _ e_mult_assoc).
      apply (algebra_propers mult)...
     intro. apply_simplified (laws _ e_mult_1_l)...
    intro. apply_simplified (laws _ e_mult_1_r)...
   apply (algebra_propers inv).
  intro. apply_simplified (laws _ e_mult_inv_l)...
 intro. apply_simplified (laws _ e_mult_inv_r)...
Qed.

Lemma encode_morphism_only
  `{AlgebraOps theory A} `{∀ u, Equiv (A u)}
  `{AlgebraOps theory B} `{∀ u, Equiv (B u)}
  (f: ∀ u, A u → B u) `{!Group (A tt)} `{!Group (B tt)} `{!Monoid_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 pose proof (monmor_a (f tt)).
 pose proof (monmor_b (f tt)).
 constructor.
    intros []. apply _.
   intros []; simpl.
     apply preserves_sg_op.
    apply groups.preserves_inv.
   apply (@preserves_mon_unit (A tt) (B tt) _ _ _ _ _ _ (f tt) _).
  eapply encode_algebra_only.
 eapply encode_algebra_only.
Qed.

Lemma encode_morphism_and_ops `{Group A} `{Group B}  `{!Monoid_Morphism (f: A → B)}:
  @HomoMorphism sig (λ _, A) (λ _, B) _ _ ( _) ( _) (λ _, f).
Proof. intros. apply encode_morphism_only; assumption. Qed.

Lemma decode_morphism_and_ops
  `{InVariety theory x} `{InVariety theory y} `{!HomoMorphism theory x y f}:
    Monoid_Morphism (f tt).
Proof.
 pose proof (homo_proper theory x y f tt).
 constructor; try apply _.
  constructor; try apply _.
  apply (preserves theory x y f mult).
 apply (preserves theory x y f one).
Qed.
