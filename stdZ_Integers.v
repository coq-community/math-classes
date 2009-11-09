Require RingCat CatStuff.
Require Import
  BinInt Morphisms
  Structures AbstractProperties RingOps BoringInstances Numbers.

(* nasty because Zplus depends on Pminus which is a bucket of FAIL *)

Lemma xO_in_ring_terms p: xO p = (p + p)%positive.
Proof with auto.
 unfold sg_op.
 induction p; simpl...
  rewrite Pplus_carry_spec, <- IHp...
 congruence.
Qed.

Lemma xI_in_ring_terms p: xI p = (p + p + 1)%positive.
Proof. intros. rewrite <- xO_in_ring_terms. reflexivity. Qed.

Section for_another_ring.

  Context `{Ring R}.

  Add Ring R: (Ring_ring_theory R).

  (* We first show the map from Z to R: *)

  Fixpoint map_pos (x: positive) {struct x} : R :=
    match x with
    | (p~0)%positive => map_pos p + map_pos p
    | (p~1)%positive => map_pos p + map_pos p + 1
    | 1%positive => 1
    end.

  Fixpoint map_nat (x: nat) {struct x} : R :=
    match x with
    | O => 0
    | S x' => map_nat x' + 1
    end.

  Definition map_Z (z: Z): R :=
    match z with
    | Z0 => 0
    | Zpos p => map_pos p
    | Zneg p => - map_pos p
    end.

(*
  Lemma map_nat_pos: forall p, map_nat (nat_of_P p) = map_pos p.
   induction p.
     simpl.
  Admitted.

  Fixpoint map_pos_mask (x : positive_mask) {struct x} : option R :=
    match x with
    | IsNul => Some 0
    | IsPos p => Some (map_pos p)
    | IsNeg => None
    end.
*)

  (* Next, we show that this map preserves everything: *)

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
     intro z. destruct z.
       apply agree_on_0.
      apply agree_on_positive.
     apply agree_on_negative.
    Qed.

  End with_another_morphism.
(*
  Global Instance: Unique (pointwise_relation _ equiv) Ring_Morphism map_Z.
  Proof.
   constructor. apply _.
   intros. apply same_morphism. assumption.
  Qed.
*)
End for_another_ring.

Lemma Z_initial: @CatStuff.initial RingCat.O RingCat.A _ (RingCat.MkO Z).
Proof with try reflexivity.
 unfold CatStuff.initial.
 simpl.
 destruct y.
 exists (@exist (Z->A) Ring_Morphism map_Z map_Z_ring_mor).
 destruct a'.
 apply (same_morphism _).
Qed.

Global Instance: Integers Z.
Proof Build_Integers Z _ _ _ _ _ _ _ Z_initial _.
