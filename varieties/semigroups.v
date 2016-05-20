(* To be imported qualified. *)
Require
  MathClasses.categories.varieties MathClasses.categories.product MathClasses.theory.forget_algebra MathClasses.theory.forget_variety.
Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.universal_algebra MathClasses.theory.ua_homomorphisms MathClasses.misc.workaround_tactics.

Inductive op := mult.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := varieties.Object theory.

Definition forget: Object → setoids.Object :=
  @product.project unit
    (λ _, setoids.Object)
    (λ _, _: Arrows setoids.Object) _
    (λ _, _: CatId setoids.Object)
    (λ _, _: CatComp setoids.Object)
    (λ _, _: Category setoids.Object) tt
     ∘ forget_algebra.object theory ∘ forget_variety.forget theory.
  (* todo: too ugly *)

(* Now follow a series of encoding/decoding functions to convert between the
 specialized Monoid/Monoid_Morphism type classes and the universal
 Algebra/InVariety/HomoMorphism type classes instantiated with the above
 signature and theory. *)

Instance encode_operations A `{!SgOp A}: AlgebraOps sig (λ _, A) :=
  λ o, match o with mult => (&) end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: SgOp (A tt) := algebra_op mult.
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

  Definition object: Object := varieties.object theory (λ _, A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{∀ u, Equiv (A u)} `{!SemiGroup (A tt)}: Algebra theory A .
Proof. constructor; intros []; simpl in *; try apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: SemiGroup (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor; try apply _.
  intro. apply_simplified (laws _ e_mult_assoc).
 apply_simplified (algebra_propers mult)...
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
 constructor; try apply _.
 apply (preserves theory x y f mult).
Qed.

Instance id_sg_morphism `{SemiGroup A}: SemiGroup_Morphism (@id A).
Proof. repeat (split; try apply _); easy. Qed.

(* Finally, we use these encoding/decoding functions to specialize some universal results: *)
Section specialized.
  Context `{Equiv A} `{SgOp A} `{Equiv B} `{SgOp B} `{Equiv C} `{SgOp C}
    (f : A → B) (g : B → C).

  Instance compose_sg_morphism:
    SemiGroup_Morphism f → SemiGroup_Morphism g → SemiGroup_Morphism (g ∘ f).
  Proof.
    intros. pose proof (encode_morphism_and_ops (f:=f)) as P.
    pose proof (encode_morphism_and_ops (f:=g)) as Q.
    pose proof (@compose_homomorphisms theory _ _ _ _ _ _ _ _ _ _ _ P Q) as PP.
    pose proof (sgmor_a (f:=f)). pose proof (sgmor_b (f:=f)). pose proof (sgmor_b (f:=g)).
    apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ PP).
  Qed.

  Instance invert_sg_morphism:
    ∀ `{!Inverse f}, Bijective f → SemiGroup_Morphism f → SemiGroup_Morphism (f⁻¹).
  Proof.
    intros. pose proof (encode_morphism_and_ops (f:=f)) as P.
    pose proof (@invert_homomorphism theory _ _ _ _ _ _ _ _ _ _ P) as Q.
    pose proof (sgmor_a (f:=f)). pose proof (sgmor_b (f:=f)).
    apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ Q).
  Qed.
End specialized.

Hint Extern 4 (SemiGroup_Morphism (_ ∘ _)) => class_apply @compose_sg_morphism : typeclass_instances.
Hint Extern 4 (SemiGroup_Morphism (_⁻¹)) => class_apply @invert_sg_morphism : typeclass_instances.
