(* nasty because Zplus depends on Pminus which is a bucket of FAIL *)

Require
  theory.categories.
Require Import
  BinInt Morphisms Ring
  abstract_algebra theory.rings interfaces.integers.

(* canonical names: *)
Instance z_equiv: Equiv BinInt.Z := eq.
Instance: RingPlus BinInt.Z := BinInt.Zplus.
Instance: RingZero BinInt.Z := BinInt.Z0.
Instance: RingOne BinInt.Z := BinInt.Zpos BinPos.xH.
Instance: RingMult BinInt.Z := BinInt.Zmult.
Instance: GroupInv BinInt.Z := BinInt.Zopp.

(* propers: *)
Instance: Proper (equiv ==> equiv ==> equiv) BinInt.Zplus.
Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper (equiv ==> equiv ==> equiv) BinInt.Zmult.
Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper (equiv ==> equiv) BinInt.Zopp.
Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.

(* properties: *)
Instance: Associative BinInt.Zplus := BinInt.Zplus_assoc.
Instance: Associative BinInt.Zmult := BinInt.Zmult_assoc.
Instance: Commutative BinInt.Zplus := BinInt.Zplus_comm.
Instance: Commutative BinInt.Zmult := BinInt.Zmult_comm.
Instance: Distribute BinInt.Zmult BinInt.Zplus :=
  { distribute_l := BinInt.Zmult_plus_distr_r; distribute_r := BinInt.Zmult_plus_distr_l }.

(* structures: *)
Instance: SemiGroup _ (op:=BinInt.Zplus).
Instance: SemiGroup _ (op:=BinInt.Zmult).
Instance: Monoid _ (op:=BinInt.Zplus) (unit:=BinInt.Z0)
  := { monoid_lunit := BinInt.Zplus_0_l; monoid_runit := BinInt.Zplus_0_r }.
Instance: Monoid _ (op:=BinInt.Zmult) (unit:=BinInt.Zpos BinPos.xH)
  := { monoid_lunit := BinInt.Zmult_1_l; monoid_runit := BinInt.Zmult_1_r }.
Instance: @Group _ _ (BinInt.Zplus) (BinInt.Z0) _
  := { inv_l := BinInt.Zplus_opp_l; inv_r := BinInt.Zplus_opp_r }.
Instance: AbGroup BinInt.Z (op:=BinInt.Zplus) (unit:=BinInt.Z0).
Instance: Ring BinInt.Z.

(* misc: *)
Instance: forall x y: BinInt.Z, Decision (x == y) := ZArith_dec.Z_eq_dec.

Add Ring Z: (stdlib_ring_theory BinInt.Z).

Lemma xO_in_ring_terms p: xO p = (p + p)%positive.
Proof with auto.
 unfold sg_op.
 induction p; simpl...
  rewrite Pplus_carry_spec, <- IHp...
 congruence.
Qed.

Lemma xI_in_ring_terms p: xI p = (p + p + 1)%positive.
Proof. intros. rewrite <- xO_in_ring_terms. reflexivity. Qed.

Section ding.

  Context `{Ring R}.

  (* We first show the map from Z to R: *)

  Fixpoint map_pos (x: positive) {struct x} : R :=
    match x with
    | (p~0)%positive => map_pos p + map_pos p
    | (p~1)%positive => map_pos p + map_pos p + 1
    | 1%positive => 1
    end.

  Definition map_Z (z: Z): R :=
    match z with
    | Z0 => 0
    | Zpos p => map_pos p
    | Zneg p => - map_pos p
    end.

End ding.

Instance inject: IntegersToRing Z := fun B _ _ _ _ _ => @map_Z B _ _ _ _.

Section for_another_ring.

  Context `{Ring R}.

  Add Ring R: (stdlib_ring_theory R).

  Lemma preserves_Psucc x: map_pos (Psucc x) == map_pos x + 1.
  Proof.
   intros.
   induction x; simpl; try reflexivity.
   rewrite IHx. ring.
  Qed.

  Lemma preserves_Pplus x y: map_pos (x + y) == map_pos x + map_pos y.
  Proof with try ring.
   induction x.
     simpl.
     destruct y; simpl.
       simpl.
       rewrite Pplus_carry_spec.
       rewrite preserves_Psucc.
       rewrite IHx...
      rewrite IHx...
     rewrite preserves_Psucc...
    destruct y; simpl; try rewrite IHx...
   intros.
   destruct y; simpl...
   rewrite preserves_Psucc...
  Qed.

  Lemma preserves_opp x: map_Z (- x) == - map_Z x.
  Proof with try reflexivity.
   destruct x; simpl...
    rewrite opp_0...
   rewrite inv_involutive...
  Qed.

  Lemma preserves_Pminus x y: (y < x)%positive -> map_pos (x - y) == map_pos x + - map_pos y.
  Proof with auto.
   intros.
  Admitted. (*
   rewrite <- map_nat_pos.
   rewrite nat_of_P_minus_morphism.
    
    admit.
   unfold Plt in H0.
   apply ZC2...
  Qed. *)
    (* awful bit manipulation mess *)

  Lemma preserves_Zplus x y: map_Z (x + y) == map_Z x + map_Z y.
  Proof with try reflexivity; try assumption.
   destruct x; simpl; intros.
     rewrite plus_0_l...
    destruct y; simpl.
      intros.
      rewrite plus_0_r...
     apply preserves_Pplus.
    case_eq (Pcompare p p0 Eq); intros; simpl.
      rewrite (Pcompare_Eq_eq _ _ H0).
      rewrite inv_r...
     rewrite preserves_Pminus...
     rewrite ring_distr_opp.
     rewrite inv_involutive.
     ring.
    apply preserves_Pminus.
    unfold Plt.
    rewrite (ZC1 _ _ H0)...
   destruct y; simpl.
     rewrite plus_0_r...
    case_eq (Pcompare p p0 Eq); intros; simpl.
      rewrite (Pcompare_Eq_eq _ _ H0).
      rewrite inv_l...
     rewrite preserves_Pminus...
     ring.
    rewrite preserves_Pminus.
     rewrite ring_distr_opp.
     rewrite inv_involutive.
     ring.
    unfold Plt.
    rewrite (ZC1 _ _ H0)...
   rewrite preserves_Pplus.
   rewrite ring_distr_opp.
   ring.
  Qed.

  Lemma preserves_Pmult x y: map_pos (x * y) == map_pos x * map_pos y.
  Proof with try reflexivity; try ring.
   induction x; intros; simpl...
    rewrite preserves_Pplus.
    rewrite distribute_r.
    rewrite xO_in_ring_terms.
    rewrite preserves_Pplus.
    rewrite IHx...
   rewrite distribute_r.
   rewrite IHx...
  Qed.

  Lemma preserves_Zmult x y: map_Z (x * y) == map_Z x * map_Z y.
  Proof with try reflexivity; try ring.
   destruct x; simpl; intros.
     symmetry.
     apply mult_0_l.
    destruct y; simpl...
     apply preserves_Pmult.
    rewrite preserves_Pmult.
    rewrite ring_opp_mult.
    rewrite (ring_opp_mult (map_pos p0))...
   destruct y; simpl...
    rewrite preserves_Pmult.
    rewrite ring_opp_mult.
    rewrite (ring_opp_mult (map_pos p))...
   rewrite preserves_Pmult.
   symmetry.
   apply ring_opp_mult_opp.
  Qed.

  Instance: Proper (equiv ==> equiv)%signature map_Z.
  Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.

  Hint Resolve preserves_Zplus preserves_Zmult preserves_opp.
  Hint Constructors Monoid_Morphism SemiGroup_Morphism Group_Morphism Ring_Morphism.

  Instance map_Z_ring_mor: Ring_Morphism map_Z.
  Proof. repeat (constructor; auto with typeclass_instances; try reflexivity; try apply _). Qed.

  Section with_another_morphism.

    Context (map_Z': Z->R) `{!Ring_Morphism map_Z'}.

    Let agree_on_0: map_Z Z0 == map_Z' Z0.
    Proof. symmetry. apply preserves_0. Qed.

    Let agree_on_1: map_Z 1%Z == map_Z' 1%Z.
    Proof. symmetry. apply preserves_1. Qed.

    Let agree_on_positive p: map_Z (Zpos p) == map_Z' (Zpos p).
    Proof with try reflexivity.
     induction p; simpl.
       rewrite IHp.
       rewrite xI_in_ring_terms.
       rewrite agree_on_1.
       do 2 rewrite <- preserves_sg_op...
      rewrite IHp.
      rewrite xO_in_ring_terms.
      rewrite <- preserves_sg_op...
     apply agree_on_1.
    Qed.

    Let agree_on_negative p: map_Z (Zneg p) == map_Z' (Zneg p).
    Proof with try reflexivity.
     intros.
     replace (Zneg p) with (- (Zpos p))...
     do 2 rewrite preserves_inv.
     rewrite <- agree_on_positive...
    Qed.

    Lemma same_morphism: @equiv _ (pointwise_relation _ equiv) map_Z map_Z'.
    Proof.
     intros [].
       apply agree_on_0.
      apply agree_on_positive.
     apply agree_on_negative.
    Qed.

  End with_another_morphism.

End for_another_ring.

Instance yada `{Ring R}: Ring_Morphism (integers_to_ring Z R).
 unfold integers_to_ring, inject.
 intros. apply map_Z_ring_mor.
Qed.

Lemma initial: categories.proves_initial (fun x =>
   @varieties.ring.arrow_from_morphism_from_instance_to_object Z _ _ _ _ _ _ _ x _
     (@map_Z_ring_mor _ _ _ _ _ _ _ (varieties.ring.from_object x))).
Proof.
  intros y [x h] [].
  unfold varieties.ring.arrow_from_morphism_from_instance_to_object. intro. simpl in *.
  apply (@same_morphism (y tt) _ _ _ _ _ _ (varieties.ring.from_object y) (x tt)).
  apply (@varieties.ring.morphism_from_ua Z _ y _ _ _ x h _ (varieties.ring.from_object y)).
Qed.

Global Instance stdZ_Integers: Integers Z.
Proof Build_Integers Z _ _ _ _ _ _ _ _ _ initial.
