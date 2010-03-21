Set Automatic Introduction.

Require
  theory.rings categories.variety.
Require Import
  Program Morphisms
  abstract_algebra universal_algebra.

Inductive op := plus | mult | zero | one | opp.

Section sig.

  Import op_type_notations.

  Definition sig: Signature := Build_Signature unit op
    (λ o => match o with
      | plus => tt -=> tt -=> constant _ tt
      | mult => tt -=> tt -=> constant _ tt
      | zero => constant _ tt
      | one => constant _ tt
      | opp => tt -=> constant _ tt
      end)%nat.

End sig.

Section laws.

  Global Instance: RingPlus (Term sig nat (constant _ tt)) :=
    λ x => App sig _ _ _ (App sig _ _ _ (Op sig _ plus) x).
  Global Instance: RingMult (Term sig nat (constant _ tt)) :=
    λ x => App sig _ _ _ (App sig _ _ _ (Op sig _ mult) x).
  Global Instance: RingZero (Term sig nat (constant _ tt)) := Op sig _ zero.
  Global Instance: RingOne (Term sig nat (constant _ tt)) := Op sig _ one.
  Global Instance: GroupInv (Term sig nat (constant _ tt)) := App sig _ _ _ (Op sig _ opp).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2 tt).

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

(* Given a Ring, we can make the corresponding Implementation, prove the laws, and
 construct the categorical object: *)

Section from_instance.

  Context A `{Ring A}.

  Instance implementation: AlgebraOps sig (λ _ => A) := λ o =>
    match o with plus => ring_plus | mult => ring_mult | zero => 0 | one => 1 | opp => group_inv end.

  Global Instance alg: Algebra sig _.
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
    apply theory.rings.plus_opp_r.
   apply theory.rings.plus_opp_l.
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
  Global Instance: GroupInv (A tt) := algebra_op _ opp.
End ops_from_alg_to_sr.

Lemma mor_from_sr_to_alg `{InVariety theory A} `{InVariety theory B}
  (f: Π u, A u → B u) `{!Ring_Morphism (f tt)}: HomoMorphism sig A B f.
Proof.
 constructor.
    intros []. apply _.
   intros []; simpl.
       apply rings.preserves_plus.
      apply rings.preserves_mult.
     change (f tt 0 = 0). apply rings.preserves_0.
    change (f tt 1 = 1). apply rings.preserves_1.
   apply rings.preserves_opp.
  change (Algebra theory A). apply _.
 change (Algebra theory B). apply _.
Qed.

Instance struct_from_var_to_class `{v: InVariety theory A}: Ring (A tt).
Proof with simpl; auto.
 repeat (constructor; try apply _); repeat intro.
               apply (variety_laws _ e_plus_assoc (λ s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end))...
              apply (algebra_propers theory plus)...
             apply (variety_laws _ e_plus_0_l (λ s n => match s with tt => y end))...
            pose proof (variety_laws _ e_plus_comm (λ s n => match s with tt => match n with 0 => x | _ => algebra_op theory zero end end)).
            simpl in H. rewrite H...
            apply (variety_laws _ e_plus_0_l (λ s n => match s with tt => x end))...
           apply (algebra_propers theory opp)...
          apply (variety_laws _ e_plus_opp_l (λ s n => match s with tt => x end))...
         apply (variety_laws _ e_plus_opp_r (λ s n => match s with tt => x end))...
        apply (variety_laws _ e_plus_comm (λ s n => match s with tt => match n with 0 => x | _ => y end end))...
       apply (variety_laws _ e_mult_assoc (λ s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end))...
      apply (algebra_propers theory mult)...
     apply (variety_laws _ e_mult_1_l (λ s n => match s with tt => y end))...
    pose proof (variety_laws _ e_mult_comm (λ s n => match s with tt => match n with 0 => x | _ => algebra_op theory one end end)).
    simpl in H. rewrite H...
    apply (variety_laws _ e_mult_1_l (λ s n => match s with tt => x end))...
   apply (variety_laws _ e_mult_comm (λ s n => match s with tt => match n with 0 => x | _ => y end end))...
  apply (variety_laws _ e_distr (λ s n => match s with tt => match n with 0 => a | 1 => b | _ => c end end))...
 apply (variety_laws _ e_distr_l (λ s n => match s with tt => match n with 0 => a | 1 => b | _ => c end end))...
Qed.

Section morphism_from_ua.

  (* todo: Do we really need this? If so, how come we don't need it for semiring? *)

  Context `{InVariety theory R0} `{InVariety theory R1} f `{!HomoMorphism sig R0 R1 f}.

  Global Instance: RingPlus (R0 tt) := @universal_algebra.algebra_op sig R0 _ plus.
  Global Instance: RingMult (R0 tt) := @universal_algebra.algebra_op sig R0 _ mult.
  Global Instance: RingZero (R0 tt) := @universal_algebra.algebra_op sig R0 _ zero.
  Global Instance: RingOne (R0 tt) := @universal_algebra.algebra_op sig R0 _ one.
  Global Instance: GroupInv (R0 tt) := @universal_algebra.algebra_op sig R0 _ opp.

  Lemma morphism_from_ua: Ring_Morphism (f tt).
   pose proof (@preserves sig R0 R1 _ _ _ _ f _).
   repeat (constructor; try apply _).
       apply (H1 plus).
      apply (H1 zero).
     apply (H1 opp).
    apply (H1 mult).
   apply (H1 one).
  Qed.

End morphism_from_ua.
