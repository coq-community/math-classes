Set Automatic Introduction.

Require Import RingOps Structures util Program Morphisms.
Require UniversalAlgebra. Module UA := UniversalAlgebra. Import UA.notations.

Module ring.
Section contents.

  Inductive op := plus | mult | zero | one | opp.

  Section sig.
    Import UA.op_type_notations.

  Let sorts := unit.

  Definition sig: UA.Signature := UA.Build_Signature op sorts
    (fun o => match o with
      | plus => tt -=> tt -=> UA.constant _ tt
      | mult => tt -=> tt -=> UA.constant _ tt
      | zero => UA.constant _ tt
      | one => UA.constant _ tt
      | opp => tt -=> UA.constant _ tt
      end)%nat.

  End sig.

  Section impl.

    Context `{Ring A}.

    Definition impl_from_instance: UA.Implementation sig (fun _ => A) := fun o =>
      match o with plus => ring_plus | mult => ring_mult | zero => 0 | one => 1 | opp => group_inv end.

    Global Instance: @UA.Propers sig (fun _ => A) (fun _ => equiv) impl_from_instance.
    Proof. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  End impl.

  Global Instance: RingPlus (UA.Term sig (UA.constant _ tt)) :=
    fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig plus) x).
  Global Instance: RingMult (UA.Term sig (UA.constant _ tt)) :=
    fun x => UA.App sig _ _ (UA.App sig _ _ (UA.Op sig mult) x).
  Global Instance: RingZero (UA.Term sig (UA.constant _ tt)) := UA.Op sig zero.
  Global Instance: RingOne (UA.Term sig (UA.constant _ tt)) := UA.Op sig one.
  Global Instance: GroupInv (UA.Term sig (UA.constant _ tt)) := UA.App sig _ _ (UA.Op sig opp).

  Local Notation x := (UA.Var sig 0 tt).
  Local Notation y := (UA.Var sig 1 tt).
  Local Notation z := (UA.Var sig 2 tt).

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
    |e_plus_opp: E (x + - x === 0).

(*
  Definition e_distr_r `{e: Equiv A} `{!Equivalence e} `{UA.Implementation sig A} `{@UA.Propers sig A _ _}:
    (forall e: UA.Statement sig, E e -> (forall v, UA.eval_stmt sig A v e)) -> forall vars, UA.eval_stmt sig A vars ((x + y) * z === x * z + y * z).
  Proof.
   intros. simpl.
   simpl.
   rewrite_with (H1 _ e_mult_comm (fun v => match v: nat with 0 => UA.op sig plus (vars 0%nat) (vars 1%nat) | _ => vars 2 end)).
   rewrite_with (H1 _ e_distr (fun v => match v: nat with 0 => vars 2 | 1 => vars 0%nat | _ => vars 1%nat end)).
   simpl.
   apply (@UA.propers sig A _ _ _ plus).
    apply (H1 _ e_mult_comm (fun v => match v: nat with 0 => vars 2%nat | _ => vars 0%nat end)).
   apply (H1 _ e_mult_comm (fun v => match v: nat with 0 => vars 2%nat | _ => vars 1%nat end)).
  Qed.
*)

  Lemma laws_from_instance `{Ring}: forall e, E e ->
    forall vars, @UA.eval_stmt sig (fun _ => A) (fun _ => equiv) impl_from_instance vars e.
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

  Definition Object := UA.Variety sig E.
  Definition Arrow := UA.Arrow sig E.

  Definition as_object A `{Ring A}: Object.
   set (impl_from_instance).
   apply (@UA.MkVariety sig E (fun _ => A) (fun _ => equiv) i _).
    apply _.
   apply (@laws_from_instance A), _.
  Defined.

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

  Definition from_object (o: Object): @Ring (o tt) _ _ _ _ _ _.
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
