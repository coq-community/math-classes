Set Automatic Introduction.

Require
  theory.rings.
Require Import
  Program Morphisms
  abstract_algebra universal_algebra.

Inductive op := plus | mult | zero | one | opp.

Section sig.

  Import op_type_notations.

  Definition sig: Signature := Build_Signature unit op
    (fun o => match o with
      | plus => tt -=> tt -=> constant _ tt
      | mult => tt -=> tt -=> constant _ tt
      | zero => constant _ tt
      | one => constant _ tt
      | opp => tt -=> constant _ tt
      end)%nat.

End sig.

Section laws.

  Global Instance: RingPlus (Term sig nat (constant _ tt)) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig _ plus) x).
  Global Instance: RingMult (Term sig nat (constant _ tt)) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig _ mult) x).
  Global Instance: RingZero (Term sig nat (constant _ tt)) := Op sig _ zero.
  Global Instance: RingOne (Term sig nat (constant _ tt)) := Op sig _ one.
  Global Instance: GroupInv (Term sig nat (constant _ tt)) := App sig _ _ _ (Op sig _ opp).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2 tt).

  Import notations.

  Inductive Laws: EqEntailment sig -> Prop :=
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

  Instance implementation: Implementation sig (fun _ => A) := fun o =>
    match o with plus => ring_plus | mult => ring_mult | zero => 0 | one => 1 | opp => group_inv end.

  Global Instance: @Propers sig _ _ implementation.
  Proof. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Lemma laws e (l: Laws e) vars: eval_stmt sig vars e.
  Proof.
   inversion_clear l; simpl.
             apply associativity.
            apply commutativity.
           apply theory.rings.plus_0_l.
          apply associativity.
         apply commutativity.
        apply theory.rings.mult_1_l.
       apply mult_0_l.
      apply distribute_l.
     apply distribute_r.
    apply theory.rings.plus_opp_r.
   apply theory.rings.plus_opp_l.
  Qed.

  Definition object: Variety theory := MkVariety theory _ _ implementation _ _ laws.

End from_instance.

(* Similarly, given a categorical object, we can make the corresponding class instances: *)

Section from_object. Variable o: Variety theory.

  Global Instance: RingPlus (o tt) := variety_op theory o plus.
  Global Instance: RingMult (o tt) := variety_op theory o mult.
  Global Instance: RingZero (o tt) := variety_op theory o zero.
  Global Instance: RingOne (o tt) := variety_op theory o one.
  Global Instance: GroupInv (o tt) := variety_op theory o opp.

  Definition from_object: Ring (o tt).
  Proof with auto.
   repeat (constructor; try apply _); repeat intro...
                 apply (variety_laws theory _ _ e_plus_assoc (fun s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end))...
                apply (variety_propers theory o plus)...
               apply (variety_laws theory _ _ e_plus_0_l (fun s n => match s with tt => x end))...
              unfold mon_unit.
              pose proof (variety_laws theory _ _ e_plus_comm (fun s n => match s with tt => match n with 0 => x | _ => variety_op theory o zero end end)).
              simpl in H. rewrite H...
              apply (variety_laws theory _ _ e_plus_0_l (fun s n => match s with tt => x end))...
             apply (variety_propers theory o opp)...
            apply (variety_laws theory _ _ e_plus_opp_l (fun s n => match s with tt => x end))...
           apply (variety_laws theory _ _ e_plus_opp_r (fun s n => match s with tt => x end))...
          apply (variety_laws theory _ _ e_plus_comm (fun s n => match s with tt => match n with 0 => x | _ => y end end))...
         apply (variety_laws theory _ _ e_mult_assoc (fun s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end))...
        apply (variety_propers theory o mult)...
       apply (variety_laws theory _ _ e_mult_1_l (fun s n => match s with tt => x end))...
      pose proof (variety_laws theory _ _ e_mult_comm (fun s n => match s with tt => match n with 0 => x | _ => variety_op theory o one end end))...
      simpl in H. rewrite H...
      apply (variety_laws theory _ _ e_mult_1_l (fun s n => match s with tt => x end))...
     apply (variety_laws theory _ _ e_mult_comm (fun s n => match s with tt => match n with 0 => x | _ => y end end))...
    apply (variety_laws theory _ _ e_distr (fun s n => match s with tt => match n with 0 => a | 1 => b | _ => c end end))...
   apply (variety_laws theory _ _ e_distr_l (fun s n => match s with tt => match n with 0 => a | 1 => b | _ => c end end))...
  Qed. (* todo: revert the needless ... here, as well as in th eother _as_ua modules *)

End from_object.

(* Finally, we can also convert morphism instances and categorical arrows: *)

Require Import categories.ua_variety.

Program Definition arrow_from_morphism_from_instance_to_object
  A `{Ring A} (B: Variety theory) (f: A -> B tt) {fmor: Ring_Morphism f}: Arrow theory (object A) B
  := fun u => match u return A -> B u with tt => f end.
Next Obligation.
 constructor. destruct a. apply _.
 destruct o; simpl.
     apply theory.rings.preserves_plus.
    apply theory.rings.preserves_mult.
   change (f 0 == 0). apply theory.rings.preserves_0.
  change (f 1 == 1). apply theory.rings.preserves_1.
 apply preserves_inv.
Qed.

Section morphism_from_ua.

  Context  `{e0: Equiv R0} {R1: unit -> Type} `{e1: forall u, Equiv (R1 u)} `{!Equivalence e0}
    `{forall u, Equivalence (e1 u)}
    `{@Implementation sig (fun _ => R0)} `{@Implementation sig R1}
    (f: forall u, R0 -> R1 u)
      `{!@HomoMorphism sig (fun _ => R0) R1 (fun _ => e0) e1 _ _ f}.

  Global Instance: RingPlus R0 := @universal_algebra.op sig (fun _ => R0) _ plus.
  Global Instance: RingMult R0 := @universal_algebra.op sig (fun _ => R0) _ mult.
  Global Instance: RingZero R0 := @universal_algebra.op sig (fun _ => R0) _ zero.
  Global Instance: RingOne R0 := @universal_algebra.op sig (fun _ => R0) _ one.
  Global Instance: GroupInv R0 := @universal_algebra.op sig (fun _ => R0) _ opp.

  Global Instance: RingPlus (R1 u) := fun u => match u with tt => universal_algebra.op sig plus end.
  Global Instance: RingMult (R1 u) := fun u => match u with tt => universal_algebra.op sig mult end.
  Global Instance: RingZero (R1 u) := fun u => match u with tt => universal_algebra.op sig zero end.
  Global Instance: RingOne (R1 u) := fun u => match u with tt => universal_algebra.op sig one end.
  Global Instance: GroupInv (R1 u) := fun u => match u with tt => universal_algebra.op sig opp end.

  Lemma morphism_from_ua (sr0: Ring R0) (sr1: Ring (R1 tt)): forall u, Ring_Morphism (f u).
  Proof.
   destruct u.
   pose proof (@preserves sig (fun _ => _) R1 (fun _ => e0) e1 _ _ f _).
   destruct H2.
   repeat (constructor; try apply _).
       apply (H3 plus).
      apply (H3 zero).
     apply (H3 opp).
    apply (H3 mult).
   apply (H3 one).
  Qed.

End morphism_from_ua.
