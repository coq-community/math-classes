Set Automatic Introduction.

Require Import RingOps Structures util Program Morphisms.
Require UniversalAlgebra. Module UA := UniversalAlgebra. Import UA.notations.

Module ring.
Section contents.

  Inductive op :=
    | ScalarPlus | ScalarMult | ScalarOpp | ScalarZero | ScalarOne
    | ElemPlus | ElemMult | ElemOpp | ElemZero | ElemOne
    | Action.

  Section sig.
    Import UA.op_type_notations.

  Inductive sorts := Scalar | Elem.

  Let binary (t: sorts) := t -=> t -=> UA.constant _ t.
  Let unary (t: sorts) := t -=> UA.constant _ t.

  Definition sig: UA.Signature := UA.Build_Signature op sorts
    (fun o => match o with
      | ScalarPlus => binary Scalar
      | ScalarMult => binary Scalar
      | ScalarOne => UA.constant _ Scalar
      | ScalarZero => UA.constant _ Scalar
      | ScalarOpp => unary Scalar

      | ElemPlus => binary Elem
      | ElemMult => binary Elem
      | ElemOne => UA.constant _ Elem
      | ElemZero => UA.constant _ Elem
      | ElemOpp => unary Elem

      | Action => Scalar -=> Elem -=> UA.constant _ Elem
      end)%nat.

  End sig.

  Section impl.

    Context `{Ring ScalarT} `{Ring ElemT} `{RalgebraAction ScalarT ElemT}.

    Definition impl_from_instance: UA.Implementation sig (fun b => if b then ScalarT else ElemT) := fun o =>
      match o with
      | ScalarPlus => ring_plus
      | ScalarMult => ring_mult
      | ScalarZero => ring_zero
      | ScalarOne => ring_one
      | ScalarOpp => group_inv

      | ElemPlus => ring_plus
      | ElemMult => ring_mult
      | ElemZero => ring_zero
      | ElemOne => ring_one
      | ElemOpp => group_inv

      | Action => ralgebra_action
      end.


(*
    Global Instance: @UA.Propers sig  (fun b => if b then ScalarT else ElemT) (fun b => if b then equiv else equiv) impl_from_instance.
    Proof. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.
*)

  End impl.

  Global Instance: RingPlus (UA.Term sig (UA.constant _ Scalar)) :=
    fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig ScalarPlus) x).
  Global Instance: RingMult (UA.Term sig (UA.constant _ Scalar)) :=
    fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig ScalarMult) x).
  Global Instance: RingZero (UA.Term sig (UA.constant _ Scalar)) := UA.Op sig ScalarZero.
  Global Instance: RingOne (UA.Term sig (UA.constant _ Scalar)) := UA.Op sig ScalarOne.
  Global Instance: GroupInv (UA.Term sig (UA.constant _ Scalar)) := UA.App sig _ _ (UA.Op sig ScalarOpp).

  Global Instance: RingPlus (UA.Term sig (UA.constant _ Elem)) :=
    fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig ElemPlus) x).
  Global Instance: RingMult (UA.Term sig (UA.constant _ Elem)) :=
    fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig ElemMult) x).
  Global Instance: RingZero (UA.Term sig (UA.constant _ Elem)) := UA.Op sig ElemZero.
  Global Instance: RingOne (UA.Term sig (UA.constant _ Elem)) := UA.Op sig ElemOne.
  Global Instance: GroupInv (UA.Term sig (UA.constant _ Elem)) := UA.App sig _ _ (UA.Op sig ElemOpp).

  Local Notation x := (UA.Var sig 0 Elem).
  Local Notation y := (UA.Var sig 1 Elem).
  Local Notation z := (UA.Var sig 2 Elem).

  Local Notation a := (UA.Var sig 0 Scalar).
  Local Notation b := (UA.Var sig 1 Scalar).
  Local Notation c := (UA.Var sig 2 Scalar).

  Global Instance: RalgebraAction  (UA.Term sig (UA.constant _ Scalar)) (UA.Term sig (UA.constant _ Elem)) :=
     fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig Action) x).

  Import UA.notations.

  Inductive E: UA.Statement sig -> Prop :=
    |e_plus_assoc: E (x + (y + z) === (x + y) + z)
    |e_plus_comm: E (x + y === y + x)
    |e_plus_0_l: E (0 + x === x)
    |e_mult_assoc: E (x * (y * z) === (x * y) * z)
    |e_mult_comm: E (x * y === y * x)
    |e_mult_1_l: E (1 * x === x)
    |e_mult_0_l: E (0 * x === 0)
    |e_distr: E (x * (y + z) === x * y + x * z)
    |e_plus_opp: E (x + - x === 0)

    |e_plus_assoc': E (a + (b + c) === (a + b) + c)
    |e_plus_comm': E (a + b === b + a)
    |e_plus_0_l': E (0 + a === a)
    |e_mult_assoc': E (a * (b * c) === (a * b) * c)
    |e_mult_comm': E (a * b === b * a)
    |e_mult_1_l': E (1 * a === a)
    |e_mult_0_l': E (0 * a === 0)
    |e_distr': E (a * (b + c) === a * b + a * c)
    |e_plus_opp': E (a + - a === 0)
 
    | e_plus_distr: E ((a + b) <*> x === a <*> x + b <*> x)
    | e_mult_distr: E ((a * b) <*> x === a <*> (b <*> x))
    | e_distr_3: E (a <*> x + a <*> y === a <*> x + y)
    | e_distr_8: E (a <*> (x * y) === (a <*> x) * y).
      (* todo: prettier ctor names *)
(*
  Lemma laws_from_instance `{Ring ScalarT} `{Ring CarrierT} `{Ralgebra ScalarT CarrierT}: forall e, E e ->
    forall vars, @UA.eval_stmt sig (fun b => if b then ScalarT else CarrierT)
      (fun b => if b then equiv else equiv) impl_from_instance vars e.
  Proof.
   intros.
   inversion_clear H0; simpl.
           apply associativity.
          apply commutativity.
         apply plus_0_l.
        apply associativity.
       apply commutativity.
      apply mult_1_l.
     apply mult_0_l.
    apply distribute_l.
   apply plus_opp_r.
  Qed.
*)

  Definition Object := UA.Variety sig E.
  Definition Arrow := UA.Arrow sig E.

  Definition as_object ScalarT ElemT `{Ralgebra ScalarT ElemT}: Object.
   set (impl_from_instance).
  Admitted. 

 (*
   apply (@UA.MkVariety sig E (fun b => if b then ScalarT else ElemT) (fun b => if b then equiv else equiv) i _).
    apply _.
   apply (@laws_from_instance A), _.
  Defined. *)
(*
  Section ops_from_impl.

    Context `{UA.Implementation sig A}.

    Global Instance: RingPlus (A tt) := UA.op sig plus.
    Global Instance: RingMult (A tt) := UA.op sig mult.
    Global Instance: RingZero (A tt) := UA.op sig zero.
    Global Instance: RingOne (A tt) := UA.op sig one.
    Global Instance: GroupInv (A tt) := UA.op sig opp.

    Definition instance_from_impl `{e: forall s, Equiv (A s)} `{!forall s, Equivalence (e s)} `{!UA.Propers sig A}
      (variety_laws: forall e, E e -> forall vars, @UA.eval_stmt sig A _ _ vars e): @Ring (A tt) _ _ _ _ _ _.
    Proof with auto.
     repeat (constructor; try apply _); repeat intro.
                   apply (variety_laws _ e_plus_assoc (fun s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end)).
                  apply (@UA.propers sig A _ _ _ plus)...
                 apply (variety_laws _ e_plus_0_l (fun s n => match s with tt => x end)).
                pose proof (variety_laws _ e_plus_comm (fun s n => match s with tt => match n with 0 => x | _ => RingZero_instance_1 end end)).
                simpl in H2. rewrite H2.
                apply (variety_laws _ e_plus_0_l (fun s n => match s with tt => x end)).
               apply (@UA.propers sig A _ _ _ opp)...
              admit.
             apply (variety_laws _ e_plus_opp (fun s n => match s with tt => x end)).
            apply (variety_laws _ e_plus_comm (fun s n => match s with tt => match n with 0 => x | _ => y end end)).
           apply (variety_laws _ e_mult_assoc (fun s n => match s with tt => match n with 0 => x | 1 => y | _ => z end end)).
          apply (@UA.propers sig A _ _ _ mult)...
         apply (variety_laws _ e_mult_1_l (fun s n => match s with tt => x end)).
        pose proof (variety_laws _ e_mult_comm (fun s n => match s with tt => match n with 0 => x | _ => mon_unit end end)).
        simpl in H2. rewrite H2.
        apply (variety_laws _ e_mult_1_l (fun s n => match s with tt => x end)).
       apply (variety_laws _ e_mult_comm (fun s n => match s with tt => match n with 0 => x | _ => y end end)).
      apply (variety_laws _ e_distr (fun s n => match s with tt => match n with 0 => a | 1 => b | _ => c end end)).
     admit. (* todo *)
      (*apply (@e_distr_r _ _ _ _ _ variety_laws (fun n => match n with 0 => a | 1 => b | _ => c end)).*)
    Qed.


  End ops_from_impl.
*)

  Definition from_object (o: Object): @Ralgebra (o Scalar) _ (o Elem) _ _ _ _ _ _ _ _ _ _ _ _.
  Proof. apply (instance_from_impl (UA.variety_laws _ _ o)). Qed.
    (* not an instance because we don't want this to be used accidentally *)

  Section arrow_from_morphism_from_instance_to_object.

    Context A `{Ring A} (B: Object) (f: A -> B tt)
      {fmor: @Ring_Morphism A (B tt) _ _ _ _ _ _ _ _ _ _ _ _ f}.

    Program Definition arrow_from_morphism_from_instance_to_object:
      Arrow (as_object A) B := fun u => match u return A -> B u with tt => f end.
    Next Obligation.
     constructor.
      destruct a. apply _.
     destruct o; simpl.
         apply preserves_plus.
        apply preserves_mult.
       apply (@preserves_0 A (B tt) _ _ _ _ _ _ _ _ _ _ _ _). (* weird *)
      apply (@preserves_1 A (B tt) _ _ _ _ _ _ _ _ _ _ _ _).
     apply preserves_inv.
    Qed.

  End arrow_from_morphism_from_instance_to_object.

  Section morphism_from_ua.

    Context  `{e0: Equiv R0} {R1: unit -> Type} `{e1: forall u, Equiv (R1 u)} `{!Equivalence e0}
      `{forall u, Equivalence (e1 u)}
      `{UA.Implementation sig (fun _ => R0)} `{UA.Implementation sig R1}
      (f: forall u, R0 -> R1 u)
        `{!@UA.HomoMorphism sig (fun _ => R0) R1 (fun _ => e0) e1 _ _ f}.

    Global Instance: RingPlus R0 := @UA.op sig (fun _ => R0) _ plus.
    Global Instance: RingMult R0 := @UA.op sig (fun _ => R0) _ mult.
    Global Instance: RingZero R0 := @UA.op sig (fun _ => R0) _ zero.
    Global Instance: RingOne R0 := @UA.op sig (fun _ => R0) _ one.
    Global Instance: GroupInv R0 := @UA.op sig (fun _ => R0) _ opp.

    Global Instance: RingPlus (R1 u) := fun u => match u with tt => @UA.op sig R1 _ plus end.
    Global Instance: RingMult (R1 u) := fun u => match u with tt => @UA.op sig R1 _ mult end.
    Global Instance: RingZero (R1 u) := fun u => match u with tt => @UA.op sig R1 _ zero end.
    Global Instance: RingOne (R1 u) := fun u => match u with tt => @UA.op sig R1 _ one end.
    Global Instance: GroupInv (R1 u) := fun u => match u with tt => @UA.op sig R1 _ opp end.

    Definition morphism_from_ua (sr0: @Ring R0 _ _ _ _ _ _) (sr1: @Ring (R1 tt) _ _ _ _ _ _):
     forall u, Ring_Morphism (f u).
    Proof.
     destruct u.
     pose proof (@UA.preserves sig (fun _ => _) R1 (fun _ => e0) e1 _ _ f _).
     repeat (constructor; try apply _).
           apply (@UA.homo_proper sig (fun _ => _) _ (fun _ => _) _ _ _ f _).
          apply (H3 plus).
         apply (H3 zero).
        apply (H3 opp).
       apply (@UA.homo_proper sig (fun _ => _) _ (fun _ => _) _ _ _ f _).
      apply (H3 mult).
     apply (H3 one).
    Qed.

(*
    Definition homo_preserves_plus: forall a b, f (a + b) == f a + f b.  Proof UA.preserves sig f plus.
    Definition homo_preserves_mult: forall a b, f (a * b) == f a * f b.  Proof UA.preserves sig f mult.
    Definition homo_preserves_0: f 0 == 0.  Proof UA.preserves sig f zero.
    Definition homo_preserves_1: f 1 == 1.  Proof UA.preserves sig f one.
*)
      (* these should go, eventually *)

  End morphism_from_ua.

End contents.

End ring.
