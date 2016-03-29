(* To be imported qualified. *)
Require
  MathClasses.categories.varieties MathClasses.categories.product MathClasses.theory.forget_algebra MathClasses.theory.forget_variety MathClasses.theory.groups.
Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.universal_algebra MathClasses.theory.ua_homomorphisms MathClasses.misc.workaround_tactics.

Inductive op := mult | inv | one.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with one => O | inv => 1%nat | mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).
  Global Instance: MonUnit (Term0 sig nat tt) := Op sig nat one.
  Global Instance: Negate (Term0 sig nat tt) :=
    fun x => App sig _ _ _ (Op sig nat inv) x.

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z)
    | e_mult_1_l: Laws (mon_unit & x === x)
    | e_mult_1_r: Laws (x & mon_unit === x)
    | e_mult_inv_l: Laws (-x & x === mon_unit)
    | e_mult_inv_r: Laws (x & -x === mon_unit)
    | e_mult_commute: Laws (x & y === y & x).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := varieties.Object theory.

Hint Extern 4 => match goal with [ |- ∀ _:unit, _ ] => intros [] end : typeclass_instances.
Program Definition forget: Object → setoids.Object :=
  product.project (λ _, setoids.Object) tt
     ∘ forget_algebra.object theory ∘ forget_variety.forget theory.
  (* todo: too ugly *)

(* Now follow a series of encoding/decoding functions to convert between the
 specialized Monoid/Monoid_Morphism type classes and the universal
 Algebra/InVariety/HomoMorphism type classes instantiated with the above
 signature and theory. *)

Instance encode_operations A `{!SgOp A} `{Negate A} `{!MonUnit A}: AlgebraOps sig (λ _, A) :=
  λ o, match o with mult => sg_op | inv => negate | one => mon_unit: A end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: MonUnit (A tt) := algebra_op one.
  Global Instance: SgOp (A tt) := algebra_op mult.
  Global Instance: Negate (A tt) := algebra_op inv.
End decode_operations.

Section encode_variety_and_ops.
  Context A `{AbGroup A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor. intro. apply _. intros []; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Hint Resolve associativity left_identity right_identity left_inverse right_inverse commutativity.
  Global Instance encode_variety_and_ops: InVariety theory (λ _, A).
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl; eauto.
        apply associativity.
       apply left_identity.
      apply right_identity.
     eapply left_inverse. 
    apply right_inverse.
   apply commutativity.
  Qed.

  Definition object: Object := varieties.object theory (λ _, A).
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{∀ u, Equiv (A u)} `{!AbGroup (A tt)}: Algebra theory A .
Proof. constructor; intros []; simpl in *; try apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: AbGroup (A tt).
Proof with simpl; auto.
   pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
  repeat constructor; try apply _; hnf; intros.
  - apply_simplified (laws _ e_mult_assoc).
  - apply_simplified (algebra_propers mult)...
  - apply_simplified (laws _ e_mult_1_l)...
  - apply_simplified (laws _ e_mult_1_r)...
  - apply_simplified (algebra_propers inv)...
  - apply_simplified (laws _ e_mult_inv_l)...
  - apply_simplified (laws _ e_mult_inv_r)...
  - apply_simplified (laws _ e_mult_commute)...
Qed.

Lemma encode_morphism_only
  `{AlgebraOps theory A} `{∀ u, Equiv (A u)}
  `{AlgebraOps theory B} `{∀ u, Equiv (B u)}
  (f: ∀ u, A u → B u) `{!AbGroup (A tt)} `{!AbGroup (B tt)} `{!Monoid_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 constructor.
 * intros []. apply _.
 * intros []; simpl.
   + apply preserves_sg_op.
   + apply groups.preserves_negate.
   + apply (@preserves_mon_unit (A tt) (B tt) _ _ _ _ _ _ (f tt) _).
 * eapply encode_algebra_only.
 * eapply encode_algebra_only.
Qed.

Lemma encode_morphism_and_ops `{AbGroup A} `{AbGroup B}  `{!Monoid_Morphism (f: A→B)}:
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

(* Finally, we use these encoding/decoding functions to specialize some universal results: *)
Section specialized.
  Context (A B C: Type)
    `{!MonUnit A} `{!SgOp A} `{!Negate A} `{!Equiv A}
    `{!MonUnit B} `{!SgOp B} `{!Negate B} `{!Equiv B}
    `{!MonUnit C} `{!SgOp C} `{!Negate C} `{!Equiv C}
    (f: A → B) (g: B → C).

  Global Instance id_morphism `{!AbGroup A}: Monoid_Morphism (id:A->A).
  Proof. repeat (constructor; try apply _); reflexivity. Qed.

  Global Instance compose_morphisms `{!AbGroup A, !AbGroup B, !AbGroup C}
    `{!Monoid_Morphism f} `{!Monoid_Morphism g}: Monoid_Morphism (g ∘ f).
  Proof.
   pose proof (encode_morphism_and_ops (f:=f)) as P.
   pose proof (encode_morphism_and_ops (f:=g)) as Q.
   pose proof (@compose_homomorphisms theory _ _ _ _ _ _ _ _ _ _ _ P Q).
   apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ H).
  Qed.

  Global Instance: ∀ `{!AbGroup A, !AbGroup B} `{H: !Monoid_Morphism (f: A->B)} `{!Inverse f},
    Bijective f → Monoid_Morphism (inverse f).
  Proof.
   intros.
   pose proof (encode_morphism_and_ops (f:=f)) as P.
   pose proof (@invert_homomorphism theory _ _ _ _ _ _ _ _ _ _ P) as Q.
   destruct H.
   apply (@decode_morphism_and_ops _ _ _ _ _ _ _ _ _ Q).
  Qed.
End specialized.
