Set Automatic Introduction.

Require
  theory.rings categories.variety.
Require Import
  Program Morphisms
  abstract_algebra universal_algebra.

Inductive op := plus | mult | zero | one.

Section sig.

  Import op_type_notations.

  Definition sig: Signature := Build_Signature unit op (* todo: rename sigma *)
    (λ o => match o with
      | plus => tt -=> tt -=> constant _ tt
      | mult => tt -=> tt -=> constant _ tt
      | zero => constant _ tt
      | one => constant _ tt
      end)%nat.

End sig.

Section laws.

  Global Instance: RingPlus (Term sig nat (constant _ tt)) :=
    λ x => App sig _ _ _ (App sig _ _ _ (Op sig _ plus) x).
  Global Instance: RingMult (Term sig nat (constant _ tt)) :=
    λ x => App sig _ _ _ (App sig _ _ _ (Op sig _ mult) x).
  Global Instance: RingZero (Term sig nat (constant _ tt)) := Op sig _ zero.
  Global Instance: RingOne (Term sig nat (constant _ tt)) := Op sig _ one.

  Local Notation x := (Var sig _ 0%nat tt).
  Local Notation y := (Var sig _ 1%nat tt).
  Local Notation z := (Var sig _ 2 tt).

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

  Instance implementation: AlgebraOps sig (λ _ => A) := λ o =>
    match o with plus => ring_plus | mult => ring_mult | zero => 0 | one => 1 end.

  Global Instance: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Lemma laws e (l: Laws e) vars: eval_stmt sig vars e.
  Proof.
   inversion_clear l; simpl.
           apply associativity.
          apply commutativity.
         apply theory.rings.plus_0_l.
        apply associativity.
       apply commutativity.
      apply theory.rings.mult_1_l.
     apply left_absorb.
    apply distribute_l.
   apply distribute_r.
  Qed.

  Instance variety: InVariety theory (λ _ => A).
  Proof. constructor. apply _. exact laws. Qed.

  Definition Object := variety.Object theory.
  Definition object: Object := variety.object theory (λ _ => A).

End from_instance.

(* Similarly, given a categorical object, we can make the corresponding class instances: *)

Section ops_from_alg_to_sr. Context `{AlgebraOps theory A}.
  Global Instance: RingPlus (A tt) := algebra_op _ plus.
  Global Instance: RingMult (A tt) := algebra_op _ mult.
  Global Instance: RingZero (A tt) := algebra_op _ zero.
  Global Instance: RingOne (A tt) := algebra_op _ one.
End ops_from_alg_to_sr.

Lemma mor_from_sr_to_alg `{InVariety theory A} `{InVariety theory B}
  (f: Π u, A u → B u) `{!SemiRing_Morphism (f tt)}: HomoMorphism sig A B f.
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

Ltac apply_simplified x := generalize x; simpl; intro HHH; apply HHH.
  (* todo: this is another workaround around [apply] weakness *)

Instance struct_from_var_to_class `{v: InVariety theory A}: SemiRing (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z => variety_laws law lawgood (λ s n =>
   match s with tt => match n with 0 => x | 1 => y | _ => z end end)).
 repeat (constructor; try apply _); repeat intro.
             apply_simplified (H _ e_mult_assoc).
            apply (algebra_propers theory mult)...
           apply_simplified (H _ e_mult_1_l)...
          transitivity (algebra_op sig mult (algebra_op sig one) x).
           apply_simplified (H _ e_mult_comm)...
          apply_simplified (H _ e_mult_1_l)...
         apply_simplified (H _ e_mult_comm)...
        apply_simplified (H _ e_plus_assoc)...
       apply (algebra_propers theory plus)...
      apply_simplified (H _ e_plus_0_l)...
     transitivity (algebra_op sig plus (algebra_op sig zero) x).
      apply_simplified (H _ e_plus_comm)...
     apply_simplified (H _ e_plus_0_l)...
    apply_simplified (H _ e_plus_comm)...
   apply_simplified (H _ e_distr_l)...
  apply_simplified (H _ e_distr_r)...
 apply_simplified (H _ e_mult_0_l)...
Qed.
  (* todo: clean up ring in the same way *)
