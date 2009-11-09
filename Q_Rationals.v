
Require stdZ_Integers.
Require Import QArith_base.
Require Import
  Ring
  Structures AbstractProperties BoringInstances
  Morphisms Numbers.

Instance: Proper (equiv ==> equiv) inject_Z. Proof. intros x y H. info rewrite H. reflexivity. Qed.
Instance: SemiGroup_Morphism inject_Z (Aop:=Zmult) (Bop:=Qmult) := { preserves_sg_op := fun _ _  => refl_equal _ }.
Instance: SemiGroup_Morphism inject_Z (Aop:=Zplus) (Bop:=Qplus) := { preserves_sg_op := _ }.
Proof. intros. unfold inject_Z, sg_op, Qplus. repeat rewrite Zmult_1_r. reflexivity. Qed.
Instance: Monoid_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) (Amult:=Zplus) (Bmult:=Qplus) := { preserves_mon_unit := refl_equal _ }.
Instance: Monoid_Morphism inject_Z (Aunit:=1%Z) (Bunit:=1%Q) (Amult:=Zmult) (Bmult:=Qmult) := { preserves_mon_unit := refl_equal _ }.
Instance: Group_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) := { preserves_inv := fun _ => refl_equal _ }.
Global Instance: Ring_Morphism inject_Z.

Global Instance Qrat: @Rationals Q _ _ _ _ _ _ _ Qle.
 apply (@Build_Rationals Q _ _ _ _ _ _ _ Qle _ _).
 intros.
 unfold integers_to_ring in t.
 destruct a.
 exists (integers_to_ring Qnum).
 exists (integers_to_ring (Zpos Qden)).
 rewrite Qmake_Qdiv.
 unfold Qdiv.
 unfold FieldOps.dec_mult_inv.
 simpl.
 assert (forall x, inject_Z x == t (integers_to_ring x)).
  intro.
  subst t.
  unfold integers_to_ring.
  set (@integers_initial Z z_equiv RingPlus_instance_1
              RingMult_instance_2 GroupInv_instance_0 RingZero_instance_1
              RingOne_instance_1 stdZ_Integers.Integers_instance_0
              (@RingCat.MkO B e0 plus0 mult0 opp0 zero0 one0
                 (@integers_ring B e0 plus0 mult0 opp0 zero0 one0 i))).
  set ((@integers_initial B e0 plus0 mult0 opp0 zero0 one0 i
           (@RingCat.MkO Q q_equiv RingPlus_instance_2 RingMult_instance_3
              GroupInv_instance_1 RingZero_instance_2 RingOne_instance_2
              (@field_ring Q q_equiv RingPlus_instance_2 RingMult_instance_3
                 GroupInv_instance_1 RingZero_instance_2 RingOne_instance_2
                 MultInv_instance_0
                 (@ordfield_field Q q_equiv RingPlus_instance_2
                    RingMult_instance_3 GroupInv_instance_1
                    RingZero_instance_2 RingOne_instance_2 MultInv_instance_0
                    Qle OrdField_instance_0))))).
  destruct s. destruct s0.
  simpl.
  set (@comp RingCat.O RingCat.A _ (RingCat.MkO Z) (RingCat.MkO B) (RingCat.MkO Q) x1 x0).
  change (inject_Z x == proj1_sig a x).
  destruct a.
  simpl.
  destruct (@integers_initial Z _ _ _ _ _ _ _ (RingCat.MkO Q)).
  destruct x3.
  simpl in *.
  transitivity (x3 x).
   symmetry.
   apply (e2 (exist Ring_Morphism inject_Z _) x).
  apply (e2 (exist Ring_Morphism x2 _) x).
 destruct (@decide Q (@equiv Q q_equiv) Decidable_instance_3
         (t
            (@integers_to_ring Z z_equiv _ _ _ _ _ _ B e0 plus0 mult0 opp0 zero0 one0 _
               (Zpos Qden))) (@ring_zero Q _)).
  elimtype False.
  rewrite <- H in e.
  discriminate.
 unfold mult_inv.
 unfold MultInv_instance_0.
 simpl.
 rewrite H.
 rewrite H.
 reflexivity.
Qed. (* eww, ugly! *)
