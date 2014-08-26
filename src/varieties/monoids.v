(* To be imported qualified. *)
Require Import
  abstract_algebra universal_algebra ua_homomorphisms workaround_tactics
  categories.categories.
Require
  categories.varieties categories.product forget_algebra forget_variety.

Inductive op := mult | one.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with one => O | mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).
  Global Instance: MonUnit (Term0 sig nat tt) := Op sig nat one.

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z)
    | e_mult_1_l: Laws (mon_unit & x === x)
    | e_mult_1_r: Laws (x & mon_unit === x).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := varieties.Object theory.

Local Hint Extern 3 => progress simpl : typeclass_instances.

Definition forget: Object → setoids.Object :=
  @product.project unit
    (λ _, setoids.Object)
    (λ _, _) _
    (λ _, _) (λ _, _) (λ _, _) tt
     ∘ forget_algebra.object theory ∘ forget_variety.forget theory.
  (* todo: too ugly *)

(* Now follow a series of encoding/decoding functions to convert between the
 specialized Monoid/Monoid_Morphism type classes and the universal
 Algebra/InVariety/HomoMorphism type classes instantiated with the above
 signature and theory. *)

Instance encode_operations A `{!SgOp A} `{!MonUnit A}: AlgebraOps sig (λ _, A) :=
  λ o, match o with mult => (&) | one => mon_unit: A end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: MonUnit (A tt) := algebra_op one.
  Global Instance: SgOp (A tt) := algebra_op mult.
End decode_operations.

Section encode_variety_and_ops.
  Context A `{Monoid A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (λ _, A) | 10.
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
     apply associativity.
    apply left_identity.
   apply right_identity.
  Qed.

  Definition object: Object := varieties.object theory (λ _, A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{∀ u, Equiv (A u)} `{!Monoid (A tt)}: Algebra theory A .
Proof. constructor; intros []; apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: Monoid (A tt) | 10.
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor.
   constructor.
     apply _.
    intro. apply_simplified (laws _ e_mult_assoc).
   apply_simplified (algebra_propers mult)...
  intro. apply_simplified (laws _ e_mult_1_l)...
 intro. apply_simplified (laws _ e_mult_1_r)...
Qed.

Lemma encode_morphism_only
  `{AlgebraOps theory A} `{∀ u, Equiv (A u)}
  `{AlgebraOps theory B} `{∀ u, Equiv (B u)}
  (f: ∀ u, A u → B u) `{!Monoid_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 pose proof (monmor_a (f:=f tt)).
 pose proof (monmor_b (f:=f tt)).
 constructor.
    intros []. apply _.
   intros []; simpl.
    apply preserves_sg_op.
   apply (@preserves_mon_unit (A tt) (B tt) _ _ _ _ _ _ (f tt)).
   apply _.
  apply encode_algebra_only.
 apply encode_algebra_only.
Qed.

Lemma encode_morphism_and_ops `{Monoid_Morphism A B f}:
  @HomoMorphism sig (λ _, A) (λ _, B) _ _ ( _) ( _) (λ _, f).
Proof. intros. apply encode_morphism_only. assumption. Qed.

Lemma decode_morphism_and_ops
  `{InVariety theory x} `{InVariety theory y} `{!HomoMorphism theory x y f}:
    Monoid_Morphism (f tt).
Proof.
 constructor; try apply _.
  constructor; try apply _.
  apply (preserves theory x y f mult).
 apply (preserves theory x y f one).
Qed.

Instance id_monoid_morphism `{Monoid A}: Monoid_Morphism (@id A).
Proof. repeat (split; try apply _); easy. Qed.

(* Finally, we use these encoding/decoding functions to specialize some universal results: *)
Section specialized.
  Context `{Equiv A}`{MonUnit A} `{SgOp A}
     `{Equiv B} `{MonUnit B} `{SgOp B}
     `{Equiv C} `{MonUnit C} `{SgOp C}
    (f : A → B) (g : B → C).

  Instance compose_monoid_morphism:
    Monoid_Morphism f → Monoid_Morphism g → Monoid_Morphism (g ∘ f).
  Proof.
    intros. pose proof (encode_morphism_and_ops (f:=f)) as P.
    pose proof (encode_morphism_and_ops (f:=g)) as Q.
    pose proof (@compose_homomorphisms theory _ _ _ _ _ _ _ _ _ _ _ P Q) as PP.
    pose proof (monmor_a (f:=f)). pose proof (monmor_b (f:=f)). pose proof (monmor_b (f:=g)).
    apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ PP).
  Qed.

  Lemma invert_monoid_morphism:
    ∀ `{!Inverse f}, Bijective f → Monoid_Morphism f → Monoid_Morphism (f⁻¹).
  Proof.
    intros. pose proof (encode_morphism_and_ops (f:=f)) as P.
    pose proof (@invert_homomorphism theory _ _ _ _ _ _ _ _ _ _ P) as Q.
    pose proof (monmor_a (f:=f)). pose proof (monmor_b (f:=f)).
    apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ Q).
  Qed.
End specialized.

Hint Extern 4 (Monoid_Morphism (_ ∘ _)) => class_apply @compose_monoid_morphism : typeclass_instances.
Hint Extern 4 (Monoid_Morphism (_⁻¹)) => class_apply @invert_monoid_morphism : typeclass_instances.
