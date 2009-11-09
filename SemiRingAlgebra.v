Set Automatic Introduction.

Require Import RingOps Structures util Program Morphisms.
Require UniversalAlgebra. Module UA := UniversalAlgebra. Import UA.notations.

Module semiring.
Section contents.

  Inductive op := plus | mult | zero | one.

  Definition sig: UA.Signature := UA.Build_Signature op
    (fun o => match o with plus => 2 | mult => 2 | zero => 0 | one => 0 end)%nat.

  Section impl.

    Context `{SemiRing A}.

    Definition impl_from_instance: UA.Implementation sig A := fun o =>
      match o with plus => ring_plus | mult => ring_mult | zero => 0 | one => 1 end.

    Global Instance: @UA.Propers sig A _ impl_from_instance.
    Proof. intro o. destruct o; simpl; try apply _; unfold Proper; reflexivity. Qed.

  End impl.

  Global Instance: RingPlus (UA.Term sig 0) := fun x => UA.App sig _ (UA.App sig _ (UA.Op sig plus) x).
  Global Instance: RingMult (UA.Term sig 0) := fun x => UA.App sig _ (UA.App sig _ (UA.Op sig mult) x).
  Global Instance: RingZero (UA.Term sig 0) := UA.Op sig zero.
  Global Instance: RingOne (UA.Term sig 0) := UA.Op sig one.

  Local Notation x := (UA.Var sig 0).
  Local Notation y := (UA.Var sig 1).
  Local Notation z := (UA.Var sig 2).

  Inductive E: UA.Statement sig -> Prop :=
    |e_plus_assoc: E (x + (y + z) === (x + y) + z)
    |e_plus_comm: E (x + y === y + x)
    |e_plus_0_l: E (0 + x === x)
    |e_mult_assoc: E (x * (y * z) === (x * y) * z)
    |e_mult_comm: E (x * y === y * x)
    |e_mult_1_l: E (1 * x === x)
    |e_mult_0_l: E (0 * x === 0)
    |e_distr: E (x * (y + z) === x * y + x * z).

  Definition e_distr_r `{e: Equiv A} `{!Equivalence e} `{UA.Implementation sig A} `{@UA.Propers sig A _ _}:
    (forall e: UA.Statement sig, E e -> (forall v, UA.eval_stmt sig A v e)) -> forall vars, UA.eval_stmt sig A vars ((x + y) * z === x * z + y * z).
  Proof. (* todo: this shouldn't be proved in these terms. *)
   intros. simpl.
   simpl.
   rewrite_with (H1 _ e_mult_comm (fun v => match v: nat with 0 => UA.op sig plus (vars 0%nat) (vars 1%nat) | _ => vars 2 end)).
   rewrite_with (H1 _ e_distr (fun v => match v: nat with 0 => vars 2 | 1 => vars 0%nat | _ => vars 1%nat end)).
   simpl.
   apply (@UA.propers sig A _ _ _ plus).
    apply (H1 _ e_mult_comm (fun v => match v: nat with 0 => vars 2%nat | _ => vars 0%nat end)).
   apply (H1 _ e_mult_comm (fun v => match v: nat with 0 => vars 2%nat | _ => vars 1%nat end)).
  Qed.

  Lemma laws_from_semiring `{SemiRing}: forall e, E e -> forall vars, @UA.eval_stmt sig A _ impl_from_instance vars e.
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
  Qed.

  Definition Object := UA.Variety sig E.
  Definition Arrow := UA.Arrow sig E.

  Definition as_object A `{SemiRing A}: Object := @UA.MkVariety sig E A _ _ _ _ laws_from_semiring.

  Section ring_ops_from_semiring_homo.
    Context `{UA.Implementation sig A}.
    Global Instance: RingPlus A := UA.op sig plus.
    Global Instance: RingMult A := UA.op sig mult.
    Global Instance: RingZero A := UA.op sig zero.
    Global Instance: RingOne A := UA.op sig one.

  Definition instance_from_impl `{e: Equiv A} `{!Equivalence e} `{!UA.Propers sig A}
    (variety_laws: forall e, E e -> forall vars, @UA.eval_stmt sig A _ _ vars e): @SemiRing A _ _ _ _ _. (* todo: tweak implicits such that the underscores aren't needed here *)
  Proof with auto.
   repeat (constructor; try apply _); repeat intro.
               apply (variety_laws _ e_mult_assoc (fun n => match n with 0 => x | 1 => y | _ => z end)).
              apply (@UA.propers sig A _ _ _ mult)...
             apply (variety_laws _ e_mult_1_l (fun n => x)).
            rewrite_with (variety_laws _ e_mult_comm (fun n => match n with 0 => x | _ => mon_unit end)).
            apply (variety_laws _ e_mult_1_l (fun n => x)).
           apply (variety_laws _ e_plus_assoc (fun n => match n with 0 => x | 1 => y | _ => z end)).
          apply (@UA.propers sig A _ _ _ plus)...
         apply (variety_laws _ e_plus_0_l (fun n => x)).
        rewrite_with (variety_laws _ e_plus_comm (fun n => match n with 0 => x | _ => RingZero_instance_1 end)).
        apply (variety_laws _ e_plus_0_l (fun n => x)).
       apply (variety_laws _ e_plus_comm (fun n => match n with 0 => x | _ => y end)).
      apply (variety_laws _ e_mult_comm (fun n => match n with 0 => x | _ => y end)).
     apply (variety_laws _ e_distr (fun n => match n with 0 => a | 1 => b | _ => c end)).
    apply (@e_distr_r _ _ _ _ _ variety_laws (fun n => match n with 0 => a | 1 => b | _ => c end)).
   apply (variety_laws _ e_mult_0_l (fun n => x)).
  Qed.

  End ring_ops_from_semiring_homo.

  Definition Variety_as_SemiRing (o: Object): @SemiRing o _ _ _ _ _.
  Proof. apply (instance_from_impl (UA.variety_laws _ _ o)). Qed.
    (* not an instance because we don't want this to be used accidentally *)

End contents.
End semiring.

Section soup. (* todo: I think this whole section should go, eventually *)

  Context  `{e0: Equiv R0} `{e1: Equiv R1} `{!Equivalence e0} `{!Equivalence e1}
    `{UA.Implementation semiring.sig R0} `{UA.Implementation semiring.sig R1}
    (f: R0 -> R1) `{!UA.HomoMorphism semiring.sig f}.

  Definition hmok (sr0: @SemiRing R0 _ _ _ _ _) (sr1: @SemiRing R1 _ _ _ _ _): SemiRing_Morphism f.
   repeat (constructor; try apply _).
      apply (UA.preserves semiring.sig f semiring.plus).
     apply (UA.preserves semiring.sig f semiring.zero).
    apply (UA.preserves semiring.sig f semiring.mult).
   apply (UA.preserves semiring.sig f semiring.one).
  Qed.

  Definition homo_preserves_plus: forall a b, f (a + b) == f a + f b.  Proof UA.preserves semiring.sig f semiring.plus.
  Definition homo_preserves_mult: forall a b, f (a * b) == f a * f b.  Proof UA.preserves semiring.sig f semiring.mult.
  Definition homo_preserves_0: f 0 == 0.  Proof UA.preserves semiring.sig f semiring.zero.
  Definition homo_preserves_1: f 1 == 1.  Proof UA.preserves semiring.sig f semiring.one.

End soup.
