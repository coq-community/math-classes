Require Import
  Structures RingOps BoringInstances AbstractProperties Numbers
  Morphisms.

Require UniversalAlgebra. Module UA := UniversalAlgebra.

Require nat_Naturals.

Require Import Ring.

(* the standard Z uses nasty binary positive crap with
  various horrible horrible operations on it (especially Pminus).
  the following is a much simpler implementation in terms of nat,
  which lets us use nat's initiality to prove this Z's initiality *)
(*
Lemma nat_hm `{Naturals N} `{Ring T} (f f': N -> T) `{!SemiRing_Morphism f} `{!SemiRing_Morphism f'}: forall n: N, f n == f' n.
 intros.
 destruct (naturals_initial (SemiRingCat.MkO T)).
 simpl in e0.
 simpl in x.
 rewrite <- (e1 (exist SemiRing_Morphism f _) n).
 rewrite <- (e1 (exist SemiRing_Morphism f' _) n).
 reflexivity.
Qed. (* todo: move *)
*)
Section contents.

Context `{NN: Naturals N}.

Definition N_semi_ring_theory: @Ring_theory.semi_ring_theory N 0 1 ring_plus ring_mult equiv
  := (RingOps.SemiRing_semi_ring_theory N).
Add Ring N: N_semi_ring_theory.

Inductive Z: Type := C { pos: N; neg: N }.

(* relations/operations/constants: *)
Instance z_equiv: Equiv Z := fun x y => pos x + neg y == pos y + neg x.
Instance z_plus: RingPlus Z := fun (x y: Z) => C (pos x + pos y) (neg x + neg y).
Instance z_inv: GroupInv Z := fun (x: Z) => C (neg x) (pos x).
Instance z_zero: RingZero Z := C 0 0.
Instance z_mult: RingMult Z := fun x y => C (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y).
Instance z_ring_one: RingOne Z := C 1 0.
Instance z_one: MonoidUnit Z := 1.

(* z_equiv is nice: *)

Instance: Reflexive z_equiv. Proof. repeat intro. unfold z_equiv. reflexivity. Qed.
Instance: Symmetric z_equiv. Proof. repeat intro. unfold z_equiv. symmetry. assumption. Qed.
Instance: Transitive z_equiv.
Proof.
 unfold z_equiv. repeat intro.
 rewrite commutativity.
 rewrite (commutativity (pos z)).
 apply nat_Naturals.naturals_plus_reg_l with (pos y).
 do 2 rewrite associativity.
 rewrite <- H. rewrite H0. ring.
Qed.

Instance: Equivalence z_equiv.

(* plus is nice: *)

Instance: Associative z_plus. Proof. repeat intro. unfold z_plus, equiv, z_equiv. simpl. ring. Qed.
Instance: Commutative z_plus. Proof. repeat intro. unfold z_plus, equiv, z_equiv. simpl. ring. Qed.

Instance: Proper (z_equiv ==> z_equiv ==> z_equiv) z_plus.
Proof.
 unfold z_equiv. intros x y E x0 y0 E'. simpl.
 transitivity (pos x + neg y + (pos x0 + neg y0)); [ring|].
 rewrite E, E'. ring.
Qed.

Let z_plus_0_l: forall x: Z, 0 + x == x. Proof. intro. unfold equiv, z_equiv. simpl. ring. Qed.
Let z_plus_0_r: forall x: Z, x + 0 == x. Proof. intro. unfold equiv, z_equiv. simpl. ring. Qed.
Let z_plus_opp_l: forall x: Z, -x + x == 0. Proof. intros. unfold equiv, z_equiv. simpl. ring. Qed.
Let z_plus_opp_r: forall x: Z, x + -x == 0. Proof. intros. unfold equiv, z_equiv. simpl. ring. Qed.

Global Instance: SemiGroup z_equiv z_plus.
Global Instance: Monoid z_equiv z_plus z_zero := { lunit := z_plus_0_l; runit := z_plus_0_r }.

(* inv is nice: *)

Instance: Proper (z_equiv ==> z_equiv) z_inv.
Proof.
 unfold z_equiv, z_inv. repeat intro. simpl.
 symmetry. rewrite (commutativity (neg y)), (commutativity (neg x)). assumption.
Qed.

Global Instance: Group z_equiv z_plus z_zero z_inv := { inv_l := z_plus_opp_l; inv_r := z_plus_opp_r }.
Global Instance: AbGroup z_equiv z_plus z_zero z_inv.

(* mult is nice: *)

Instance: Associative z_mult.
Proof. repeat intro. unfold z_mult, equiv, z_equiv. simpl. ring. Qed.
Instance: Commutative z_mult.
Proof. repeat intro. unfold z_plus, equiv, z_equiv. simpl. ring. Qed.

Global Instance: Distribute z_mult z_plus.
Proof. constructor; repeat intro; unfold z_plus, z_mult, equiv, z_equiv; simpl; ring. Qed.

Let z_mult_equiv_compat_r y y': y == y' -> forall x, z_mult x y == z_mult x y'.
Proof.
 unfold z_mult, equiv, z_equiv. repeat intro. simpl.
 transitivity (pos x * (pos y + neg y') + neg x * (pos y' + neg y)); [ring |].
 transitivity (pos x * (pos y' + neg y) + neg x * (pos y + neg y')); [| ring].
 rewrite H. reflexivity.
Qed.

Instance: Proper (z_equiv ==> z_equiv ==> z_equiv) z_mult.
Proof with auto.
 repeat intro. transitivity (z_mult x y0).
 apply z_mult_equiv_compat_r...
 rewrite commutativity.
 rewrite (commutativity y).
 apply z_mult_equiv_compat_r...
Qed.

Let mult_1_l: forall x: Z, 1 * x == x. 
Proof. repeat intro. unfold ring_mult, z_mult, equiv, z_equiv. simpl. ring. Qed.
Let mult_1_r: forall x: Z, x * 1 == x.
Proof. repeat intro. unfold ring_mult, z_mult, equiv, z_equiv. simpl. ring. Qed.

Instance: SemiGroup z_equiv z_mult.
Instance: Monoid z_equiv z_mult z_one := { lunit := mult_1_l; runit := mult_1_r }.
Global Instance: Ring z_equiv z_plus z_mult z_inv z_zero z_one.

Definition ring_theory: ring_theory (R:=Z) 0 1 ring_plus ring_mult _ group_inv equiv := Ring_ring_theory Z.
Add Ring Z: ring_theory.

(* misc: *)

Definition NtoZ (n: N): Z := C n 0.

Instance: Proper (equiv ==> equiv) NtoZ.
Proof.
 repeat intro. unfold NtoZ, equiv, z_equiv. simpl.
 rewrite H. reflexivity.
Qed.

Global Instance: SemiRing_Morphism NtoZ.
Proof.
 unfold NtoZ.
 repeat (constructor; try apply _; try reflexivity); unfold equiv, z_equiv; simpl; intros.
  change (a + a' + (0 + 0) == a + a' + 0). ring.
 change (a * a' + (a * 0 + 0 * a') == a * a' + 0 * 0 + 0). ring.
Qed.

Instance: Proper (equiv ==> equiv ==> equiv) C.
Proof.
 repeat intro. unfold equiv, z_equiv. simpl.
 rewrite H, H0. reflexivity.
Qed.

Lemma split_into_nats n m: C n m == NtoZ n + - NtoZ m.
Proof.
 intros. unfold group_inv, ring_plus, z_inv, z_plus. simpl.
 rewrite plus_0_r, plus_0_l. reflexivity.
Qed.

Global Instance: Decidable z_equiv := fun x y => @naturals_eqdec N _ _ _ _ _ _ (pos x + neg y) (pos y + neg x).

(* Next, we show that Z is initial, and therefore a model of the integers. *)

Section for_another_ring.

  Context `{Ring R}.

  Add Ring R: (Ring_ring_theory R).

  Definition inject_N: N -> R := @naturals_to_semiring N _ _ _ _ _ _ R _ _ _ _ _ _.
  Let inject_N_mor: SemiRing_Morphism inject_N := @naturals_to_semiring_mor N R _ _ _ _ _ _ _ _ _ _ _ _.

(*
  Let inject_N_uniq: forall f : N -> R, SemiRing_Morphism f -> pointwise_relation _ equiv f inject_N
    := @ding_unique N _ _ _ _ _ _ R _ _ _ _ _ _.
*)

  Definition inject (z: Z): R := inject_N (pos z) + - inject_N (neg z).

  Instance: Proper (equiv ==> equiv) inject.
  Proof.
   unfold equiv, z_equiv, inject. repeat intro.
   apply AbstractProperties.equal_by_zero_sum.
   transitivity (inject_N (pos x) + inject_N (neg y) + - (inject_N (neg x) + inject_N (pos y))); [ring|].
   do 2 rewrite <- preserves_plus.
   rewrite H0. rewrite (commutativity (pos y)). ring.
  Qed.

  Let inject_preserves_plus x y: inject (x + y) == inject x + inject y.
  Proof. intros. unfold inject. simpl. do 2 rewrite preserves_plus. ring. Qed.

  Let preserves_mult x y: inject (x * y) == inject x * inject y.
  Proof.
   intros. unfold inject. simpl.
   repeat (rewrite preserves_plus || rewrite preserves_mult). ring.
  Qed.

  Let preserves_1: inject 1 == 1.
  Proof. unfold inject. simpl. rewrite preserves_0, preserves_1. ring. Qed.

  Let preserves_0: inject 0 == 0. Proof. unfold inject. simpl. ring. Qed.

  Let preserves_inv x: inject (- x) == - inject x.
  Proof. intros. unfold inject. simpl. ring. Qed.

  Instance: SemiGroup_Morphism inject := { preserves_sg_op := inject_preserves_plus }.
  Instance: @SemiGroup_Morphism _ _ _ _ ring_mult ring_mult inject := { preserves_sg_op := preserves_mult }.
  Instance: @Monoid_Morphism _ _ _ _ (0:Z) (0:R) ring_plus ring_plus inject := { preserves_mon_unit := preserves_0 }.
  Instance: @Monoid_Morphism _ _ _ _ (1:Z) (1:R) ring_mult ring_mult inject := { preserves_mon_unit := preserves_1 }.
  Instance: @Group_Morphism _ _ _ _ ring_plus ring_plus (0:Z) (0:R) group_inv group_inv inject := { preserves_inv := preserves_inv }.
  Instance inject_mor: Ring_Morphism inject.

  Section for_another_morphism.

    Context (inject': Z -> R) `{!Ring_Morphism inject'}.

    Definition inject'_N (n: N): R := inject' (C n 0).

    Instance: Proper (equiv ==> equiv) inject'_N.
    Proof. repeat intro. unfold inject'_N. rewrite H0. reflexivity. Qed.

    Instance: SemiRing_Morphism inject'_N.
    Proof with try apply _.
     repeat (constructor; try apply _).
        unfold inject'_N. intros.
        rewrite <- preserves_sg_op.
        unfold sg_op.
        unfold z_plus.
        simpl.
        rewrite plus_0_l.
        reflexivity.
       unfold inject'_N.
       apply RingOps.preserves_0.
      unfold inject'_N. intros.
      rewrite <- preserves_sg_op.
      unfold sg_op at 2.
      unfold z_mult.
      simpl.
      apply sg_mor_op_proper.
      unfold z_equiv.
      simpl.
      change (a * a' + (a * 0 + 0 * a') == a * a' + 0 * 0 + 0).
      ring.
     unfold inject'_N.
     apply RingOps.preserves_1.
    Qed.

    Lemma agree_on_nat: @equiv _ (pointwise_relation _ equiv) inject'_N inject_N.
    Proof. intro. apply (@ding_unique N _ _ _ _ _ _ R _ _ _ _ _ _ inject'_N _ a). Qed.

    Lemma agree: @equiv _ (pointwise_relation _ equiv) inject inject'.
    Proof.
     intros [pos0 neg0].
     rewrite split_into_nats.
     do 2 rewrite preserves_plus.
     rewrite preserves_inv, Structures.preserves_inv.
     fold (inject'_N pos0) (inject'_N neg0).
     rewrite (agree_on_nat pos0), (agree_on_nat neg0).
     unfold inject. simpl. rewrite RingOps.preserves_0. ring.
    Qed.

  End for_another_morphism.

End for_another_ring.

Lemma Z_initial: @CatStuff.initial RingCat.O RingCat.A _ (RingCat.MkO Z).
Proof with try reflexivity.
 unfold CatStuff.initial.
 simpl.
 destruct y.
 exists (@exist (Z -> A) Ring_Morphism inject inject_mor).
 destruct a'.
 intro. simpl. apply (agree x).
Qed.

Global Instance: Integers Z.
Proof Build_Integers Z _ _ _ _ _ _ _ Z_initial _.

(* todo: forall z, z = abs z * sign z (where abs returns a natural) *) 
(*
Lemma int_intermsof_nats `{Integers ZZ}:
  forall z:ZZ, z == naturals_to_semiring (pos (integers_to_ring z)) + - naturals_to_semiring (neg (integers_to_ring z)).
Proof with simpl in *; auto.
 intros.
 unfold integers_to_ring.
 set (@integers_initial ZZ _ _ _ _ _ _ _).
 pose proof (@integers_initial Z _ _ _ _ _ _ _).
 destruct (@CatStuff.initials_unique RingCat.O RingCat.A _ _ _ _ _ (RingCat.MkO Z) (RingCat.MkO ZZ) X i).
 clearbody i.
 simpl in *.
  set (i
                (@RingCat.MkO Z z_equiv z_plus z_mult z_inv z_zero z_ring_one
                   (@integers_ring Z z_equiv z_plus z_mult z_inv z_zero z_ring_one
                      Integers_instance_0))) in H0, H1.
 set (i (RingCat.MkO Z)).
 assert (proj1_sig s == proj1_sig s0).
  intro.
  destruct s. destruct s0. simpl in *.
  apply (e1 x0 a).
 destruct s. destruct s0...
 unfold naturals_to_semiring.
 destruct (naturals_initial (SemiRingCat.MkO ZZ))...
 destruct x0. destruct x1...
 rewrite <- (H0 z) at 1...
 destruct x. destruct X. destruct x2...
 rewrite (H2 z)...
 destruct (x0 z)...
 rewrite split_into_nats.
 rewrite preserves_plus.
 rewrite preserves_inv.
 set (@comp (SemiRingCat.O) SemiRingCat.A _ (SemiRingCat.MkO N) (SemiRingCat.MkO Z) (SemiRingCat.MkO ZZ)
   (exist SemiRing_Morphism x2 _) (exist SemiRing_Morphism NtoZ _)).
 change (proj1_sig a pos0 + - proj1_sig a neg0 == x1 pos0 + - x1 neg0).
 destruct a...
 do 2 rewrite (nat_hm x3 x1). reflexivity.
Qed.
*)
(* todo: also make one that mimics Rationals' rationals_frac (proved in terms of the above) *)
(*
Lemma simpleZ_mult_reg_l: forall p: Z, ~ p == 0 -> forall n m, p * n == p * m -> n == m.
Proof.
 unfold ring_mult.
 unfold z_mult.
 unfold equiv.
 unfold z_equiv.
 intros [pp pn]. simpl.
 intros H [nn nd] [mn md]. simpl.
 intros.
 rewrite plus_0_r in H.
 rewrite plus_0_l in H.


 assert (pn * ((nd + mn) + - (nn + md)) == pp * ((nd + mn) + - (nn + md))).
  


 assert (~ pp == pn).
  rewrite <- plus_0_r.
  rewrite <- (plus_0_l pn).
  assumption.

  intro.

 destruct p. destruct
 destruct
 intros.

End contents.



Lemma integers_mult_reg_l `{Integers ZZ}: forall p: ZZ, ~ p == 0 -> forall n m, p * n == p * m -> n == m.
Proof with auto.
 intros.
*) 

End contents.
