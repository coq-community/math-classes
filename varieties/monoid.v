Set Automatic Introduction.

Require Import
  Program Morphisms
  abstract_algebra universal_algebra.
Require categories.variety.

Inductive op := mult | one.

Section sig.

  Import op_type_notations.

  Definition sig: Signature := Build_Signature unit op
    (fun o => match o with
      | mult => tt -=> tt -=> constant _ tt
      | one => constant _ tt
      end)%nat.

End sig.

Section theory.

  Global Instance: SemiGroupOp (Term sig nat (constant _ tt)) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).
  Global Instance: MonoidUnit (Term sig nat (constant _ tt)) := Op sig nat one.

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2 tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z)
    | e_mult_1_l: Laws (mon_unit & x === x)
    | e_mult_1_r: Laws (x & mon_unit === x).

End theory.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := variety.Object theory.

(* Given a Monoid, we can make the corresponding Implementation, prove the laws, and
 construct the categorical object: *)

Section from_instance.

  Context A `{Monoid A}.

  Instance implementation: AlgebraOps sig (λ _ => A) :=
    fun o => match o with mult => sg_op | one => mon_unit end.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Lemma laws e (l: Laws e) vars: eval_stmt sig vars e.
  Proof.
   inversion_clear l; simpl.
     apply associativity.
    apply left_identity.
   apply right_identity.
  Qed.

  Global Instance: InVariety theory (λ _ => A).
  Proof. constructor. apply _. exact laws. Qed.

  Definition object: Object := variety.object theory (λ _ => A).

End from_instance.

Section decode_operations. Context `{AlgebraOps theory A}.
  Global Instance: MonoidUnit (A tt) := algebra_op _ one.
  Global Instance: SemiGroupOp (A tt) := algebra_op _ mult.
End decode_operations.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{Π u, Equiv (A u)} `{!Monoid (A tt)}: Algebra theory A .
Proof.
 constructor; intros []. apply _.
  destruct Monoid0. destruct monoid_semigroup.
  apply sg_mor.
 destruct Monoid0. destruct monoid_semigroup.
 unfold Proper. reflexivity.
Qed. (* todo: clean up *)

Ltac apply_simplified x := generalize x; simpl; intro HHH; apply HHH.
  (* todo: this is another workaround around [apply] weakness *)

Global Instance decode_variety_and_ops `{InVariety theory A}: Monoid (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z => variety_laws law lawgood (λ s n =>
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor.
   constructor.
     apply _.
    intro. apply_simplified (laws _ e_mult_assoc).
   apply (algebra_propers theory mult)...
  intro. apply_simplified (laws _ e_mult_1_l)...
 intro. apply_simplified (laws _ e_mult_1_r)...
Qed.

Lemma encode_morphism_only
    (* not the ops, which we assume are already in encoded form *)
  `{AlgebraOps theory A} `{Π u, Equiv (A u)}
  `{AlgebraOps theory B} `{Π u, Equiv (B u)}
  (f: Π u, A u → B u) `{!Monoid_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 pose proof (monmor_a).
 pose proof (monmor_b).
 constructor.
    intros []. apply _.
   intros []; simpl.
    apply preserves_sg_op.
   apply (@preserves_mon_unit (A tt) (B tt) _ _ _ _ _ _ (f tt)).
   apply _.
  apply encode_algebra_only.
 apply encode_algebra_only.
Qed.

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


Require categories.product forget_algebra forget_variety.

Definition forget: Object → setoid.Object :=
  @product.project unit
    (λ _ => setoid.Object)
    (λ _ => _: Arrows setoid.Object) _
    (λ _ => _: CatId setoid.Object)
    (λ _ => _: CatComp setoid.Object) 
    (λ _ => _: Category setoid.Object) tt
     ∘ forget_algebra.object theory ∘ forget_variety.forget theory.
  (* todo: too ugly *)

