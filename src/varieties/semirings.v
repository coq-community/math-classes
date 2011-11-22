(* To be imported qualified. *)
Require
  theory.rings categories.varieties.
Require Import
  abstract_algebra universal_algebra ua_homomorphisms workaround_tactics.

Inductive op := plus | mult | zero | one.

Definition sig: Signature := single_sorted_signature
  (λ o, match o with zero | one => O | plus | mult => 2%nat end).

Section laws.
  Global Instance: Plus (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig _ plus) x).
  Global Instance: Mult (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig _ mult) x).
  Global Instance: Zero (Term0 sig nat tt) := Op sig _ zero.
  Global Instance: One (Term0 sig nat tt) := Op sig _ one.

  Local Notation x := (Var sig _ 0%nat tt).
  Local Notation y := (Var sig _ 1%nat tt).
  Local Notation z := (Var sig _ 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Prop :=
    |e_plus_assoc: Laws (x + (y + z) === (x + y) + z)
    |e_plus_comm: Laws (x + y === y + x)
    |e_plus_0_l: Laws (0 + x === x)
    |e_mult_assoc: Laws (x * (y * z) === (x * y) * z)
    |e_mult_comm: Laws (x * y === y * x)
    |e_mult_1_l: Laws (1 * x === x)
    |e_mult_0_l: Laws (0 * x === 0)
    |e_distr_l: Laws (x * (y + z) === x * y + x * z)
    |e_distr_r: Laws ((x + y) * z === x * z + y * z).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.

(* Given a SemiRing, we can make the corresponding Implementation, prove the laws, and
 construct the categorical object: *)

Section from_instance.
  Context A `{SemiRing A}.

  Instance implementation: AlgebraOps sig (λ _, A) := λ o,
    match o with plus => (+) | mult => (.*.) | zero => 0: A | one => 1:A end.

  Global Instance: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; apply reflexivity. Qed.

  Lemma laws en (l: Laws en) vars: eval_stmt sig vars en.
  Proof.
   inversion_clear l; simpl.
           apply associativity.
          apply commutativity.
         apply theory.rings.plus_0_l.
        apply associativity.
       apply commutativity.
      apply theory.rings.mult_1_l.
     unfold algebra_op. simpl.
     apply left_absorb.
    apply distribute_l.
   apply distribute_r.
  Qed.

  Global Instance variety: InVariety theory (λ _, A).
  Proof. constructor. apply _. exact laws. Qed.

  Definition Object := varieties.Object theory.
  Definition object: Object := varieties.object theory (λ _, A).
End from_instance.

(* Similarly, given a categorical object, we can make the corresponding class instances: *)

Section ops_from_alg_to_sr.
  Context `{AlgebraOps theory A}.
  Global Instance: Plus (A tt) := algebra_op plus.
  Global Instance: Mult (A tt) := algebra_op mult.
  Global Instance: Zero (A tt) := algebra_op zero.
  Global Instance: One (A tt) := algebra_op one.
End ops_from_alg_to_sr.

Lemma mor_from_sr_to_alg `{InVariety theory A} `{InVariety theory B}
  (f: ∀ u, A u → B u) `{!SemiRing_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 constructor.
    intros []. apply _.
   intros []; simpl.
      apply rings.preserves_plus.
     apply rings.preserves_mult.
    change (f tt 0 = 0). apply rings.preserves_0.
   change (f tt 1 = 1). apply rings.preserves_1.
  change (Algebra theory A). apply _.
 change (Algebra theory B). apply _.
Qed. (* todo: these [change]s should not be necessary at all. [apply] is too weak. report bug. *)

Instance decode_variety_and_ops `{v: InVariety theory A}: SemiRing (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
   match s with tt => match n with 0 => x | 1 => y | _ => z end end)).
 repeat (constructor; try apply _); repeat intro.
             apply_simplified (H _ e_plus_assoc).
            apply (algebra_propers plus)...
           apply_simplified (H _ e_plus_0_l)...
          transitivity (algebra_op plus (algebra_op zero) x).
           apply_simplified (H _ e_plus_comm)...
          apply_simplified (H _ e_plus_0_l)...
         apply_simplified (H _ e_plus_comm)...
        apply_simplified (H _ e_mult_assoc)...
       apply (algebra_propers mult)...
      apply_simplified (H _ e_mult_1_l)...
     transitivity (algebra_op mult (algebra_op one) x).
      apply_simplified (H _ e_mult_comm)...
     apply_simplified (H _ e_mult_1_l)...
    apply_simplified (H _ e_mult_comm)...
   apply_simplified (H _ e_distr_l)...
  apply_simplified (H _ e_mult_0_l)...
Qed.
  (* todo: clean up ring in the same way *)

Lemma decode_morphism_and_ops
  `{InVariety theory x} `{InVariety theory y} `{!HomoMorphism theory x y f}:
    SemiRing_Morphism (f tt).
Proof.
 pose proof (homo_proper theory x y f tt).
 pose proof (preserves theory x y f) as P.
 repeat (constructor; try apply _)
 ; [ apply (P plus) | apply (P zero) | apply (P mult) | apply (P one) ].
Qed.
