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

  Instance implementation: AlgebraOps sig (fun _ => A) :=
    fun o => match o with mult => sg_op | one => mon_unit end.

  Global Instance: Algebra sig _.
  Proof. constructor. intro. apply _. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  Lemma laws e (l: Laws e) vars: eval_stmt sig vars e.
  Proof.
   inversion_clear l; simpl.
     apply associativity.
    apply monoid_lunit.
   apply monoid_runit.
  Qed.

  Global Instance: Variety theory (fun _ => A).
  Proof. constructor. apply _. exact laws. Qed.

  Definition object: Object := variety.object theory (fun _ => A).

End from_instance.

(* Similarly, given a categorical object, we can make the corresponding class instances: *)

Section from_object. Variable o: variety.Object theory.

  Global Instance: SemiGroupOp (o tt) := algebra_op theory mult.
  Global Instance: MonoidUnit (o tt) := algebra_op theory one.

  Global Instance from_object: Monoid (o tt).
  Proof with simpl; auto.
   repeat (constructor; try apply _); repeat intro; simpl; try auto.
(*
      apply (variety_laws theory _ _ e_mult_assoc (fun s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end))...
     apply (variety_propers theory o mult)...
    apply (variety_laws theory _ _ e_mult_1_l (fun s n => match s with tt => x end))...
   apply (variety_laws theory _ _ e_mult_1_r (fun s n => match s with tt => x end))...
  Qed. *)
  Admitted.

End from_object.

(* Finally, we can also convert morphism instances and categorical arrows: *)
(*
Require Import categories.ua_variety.

Program Definition arrow_from_morphism_from_instance_to_object
  A `{Monoid A} (B: Variety theory) (f: A -> B tt) {fmor: Monoid_Morphism f}: Arrow theory (object A) B
  := fun u => match u return A -> B u with tt => f end.
Next Obligation.
 constructor. destruct a. apply _.
 destruct o; simpl. apply preserves_sg_op.
 change (f mon_unit == mon_unit).
 apply preserves_mon_unit.
Qed.

Section morphism_from_ua.

  Context  `{e0: Equiv R0} {R1: unit -> Type} `{e1: forall u, Equiv (R1 u)} `{!Equivalence e0}
    `{forall u, Equivalence (e1 u)}
    `{@Implementation sig (fun _ => R0)} `{@Implementation sig R1}
    (f: forall u, R0 -> R1 u)
      `{!@HomoMorphism sig (fun _ => R0) R1 (fun _ => e0) e1 _ _ f}.

  Global Instance: SemiGroupOp R0 := @universal_algebra.op sig (fun _ => R0) _ mult.
  Global Instance: MonoidUnit R0 := @universal_algebra.op sig (fun _ => R0) _ one.

  Global Instance: SemiGroupOp (R1 u) := fun u => match u with tt => universal_algebra.op sig mult end.
  Global Instance: MonoidUnit (R1 u) := fun u => match u with tt => universal_algebra.op sig one end.

  Lemma morphism_from_ua (sr0: Monoid R0) (sr1: Monoid (R1 tt)): forall u, Monoid_Morphism (f u).
  Proof.
   destruct u.
   pose proof (@preserves sig (fun _ => _) R1 (fun _ => e0) e1 _ _ f _).
   destruct H2.
   repeat (constructor; try apply _).
    apply (H3 mult).
   apply (H3 one).
  Qed.

End morphism_from_ua.
*)
