(* To be imported qualified. *)
Require
  categories.variety theory.rings.
Require Import
  Program Morphisms Ring
  abstract_algebra universal_algebra ua_homomorphisms workaround_tactics.

Inductive op := plus | mult | zero | one | opp.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with zero | one => O | opp => 1%nat | plus | mult => 2%nat end).

Section laws.
  Global Instance: RingPlus (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig _ plus) x).
  Global Instance: RingMult (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig _ mult) x).
  Global Instance: RingZero (Term0 sig nat tt) := Op sig _ zero.
  Global Instance: RingOne (Term0 sig nat tt) := Op sig _ one.
  Global Instance: GroupInv (Term0 sig nat tt) := App sig _ _ _ (Op sig _ opp).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    |e_plus_assoc: Laws (x + (y + z) === (x + y) + z)
    |e_plus_comm: Laws (x + y === y + x)
    |e_plus_0_l: Laws (0 + x === x)
    |e_mult_assoc: Laws (x * (y * z) === (x * y) * z)
    |e_mult_comm: Laws (x * y === y * x)
    |e_mult_1_l: Laws (1 * x === x)
    |e_mult_0_l: Laws (0 * x === 0)
    |e_distr: Laws (x * (y + z) === x * y + x * z)
    |e_distr_l: Laws ((x + y) * z === x * z + y * z)
    |e_plus_opp_r: Laws (x + - x === 0)
    |e_plus_opp_l: Laws (- x + x === 0).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.
Definition Object := variety.Object theory.

(* Now follow a series of encoding/decoding functions to convert between the
 specialized Ring/Ring_Morphism type classes and the universal
 Algebra/InVariety/HomoMorphism type classes instantiated with the above
 signature and theory. *)

Section decode_operations. 
  Context `{AlgebraOps theory A}.
  Global Instance: RingPlus (A tt) := algebra_op plus.
  Global Instance: RingMult (A tt) := algebra_op mult.
  Global Instance: RingZero (A tt) := algebra_op zero.
  Global Instance: RingOne (A tt) := algebra_op one.
  Global Instance: GroupInv (A tt) := algebra_op opp.
End decode_operations.

Section encode_with_ops.
  Context A `{Ring A}.

  Global Instance encode_operations: AlgebraOps sig (λ _, A) := λ o,
    match o with plus => (+) | mult => (.*.) | zero => 0:A | one => 1:A | opp => (-) end.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Add Ring A: (rings.stdlib_ring_theory A).

  Global Instance encode_variety_and_ops: InVariety theory (λ _, A).
  Proof. constructor. apply _. intros ? [] ?; simpl; unfold algebra_op; simpl; ring. Qed.

  Definition object: Object := variety.object theory (λ _, A).
End encode_with_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{∀ u, Equiv (A u)} `{!Ring (A tt)}: Algebra sig A .
Proof. constructor; intros []; simpl in *; try apply _. Qed.

Instance decode_variety_and_ops `{InVariety theory A}: Ring (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
  match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 repeat (constructor; try apply _); repeat intro.
               apply_simplified (laws _ e_plus_assoc).
              apply (algebra_propers plus)...
             apply_simplified (laws _ e_plus_0_l)...
            transitivity (algebra_op plus (algebra_op zero) x).
             apply_simplified (laws _ e_plus_comm)...
            apply_simplified (laws _ e_plus_0_l)...
           apply (algebra_propers opp)...
          apply_simplified (laws _ e_plus_opp_l)...
         apply_simplified (laws _ e_plus_opp_r)...
        apply_simplified (laws _ e_plus_comm)...
       apply_simplified (laws _ e_mult_assoc)...
      apply (algebra_propers mult)...
     apply_simplified (laws _ e_mult_1_l)...
    transitivity (algebra_op mult (algebra_op one) x).
     apply_simplified (laws _ e_mult_comm)...
    apply_simplified (laws _ e_mult_1_l)...
   apply_simplified (laws _ e_mult_comm)...
  apply_simplified (laws _ e_distr)...
 apply_simplified (laws _ e_distr_l)...
Qed.

Lemma encode_morphism_only
  `{AlgebraOps theory A} `{∀ u, Equiv (A u)}
  `{AlgebraOps theory B} `{∀ u, Equiv (B u)}
  (f: ∀ u, A u → B u) `{!Ring (A tt)} `{!Ring (B tt)} `{!SemiRing_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 constructor.
    intros []. apply _.
   intros []; simpl.
       apply rings.preserves_plus.
      apply rings.preserves_mult.
     change (f tt 0 = 0). apply rings.preserves_0.
    change (f tt 1 = 1). apply rings.preserves_1.
   apply rings.preserves_opp.
  apply encode_algebra_only.
 apply encode_algebra_only.
Qed.

Lemma encode_morphism_and_ops `{Ring A} `{Ring B} {f : A → B} `{!SemiRing_Morphism f}:
  @HomoMorphism sig (λ _, A) (λ _, B) _ _ _ _ (λ _, f).
Proof. intros. apply (encode_morphism_only _). Qed.

Lemma decode_morphism_and_ops
  `{InVariety theory x} `{InVariety theory y} `{!HomoMorphism theory x y f}:
    SemiRing_Morphism (f tt).
Proof.
 pose proof (homo_proper theory x y f tt).
 pose proof (preserves theory x y f) as P.
 repeat (constructor; try apply _)
 ; [ apply (P plus) | apply (P zero) | apply (P mult) | apply (P one) ].
Qed.
