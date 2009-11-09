Set Automatic Introduction.

Require Import Structures Program Morphisms util.

Require UniversalAlgebra.
Module UA := UniversalAlgebra.
Import UA.notations.

Section srm. Context `{SemiRing_Morphism}.
  Lemma preserves_0: f 0 == 0.
  Proof. intros. apply (@preserves_mon_unit _ _ _ _ _ _ _ _ f _). Qed.
  Lemma preserves_1: f 1 == 1.
  Proof. intros. apply (@preserves_mon_unit _ _ _ _ _ _ _ _ f _). Qed.
  Lemma preserves_mult: forall x y, f (x * y) == f x * f y.
  Proof. intros. apply preserves_sg_op. Qed.
  Lemma preserves_plus: forall x y, f (x + y) == f x + f y.
  Proof. intros. apply preserves_sg_op. Qed.
End srm.

Lemma plus_opp_r `{Ring} x: x + -x == 0. Proof. intros. apply (inv_r x). Qed.
Lemma plus_opp_l `{Ring} x: -x + x == 0. Proof. intros. apply (inv_l x). Qed.
Lemma plus_0_r `{SemiRing} x: x + 0 == x. Proof. intros. apply (runit x). Qed.
Lemma plus_0_l `{SemiRing} x: 0 + x == x. Proof. intros. apply (lunit x). Qed.
Lemma mult_1_l `{SemiRing}: forall a, 1 * a == a. Proof. intros. apply (lunit a). Qed.
Lemma mult_1_r `{SemiRing}: forall a, a * 1 == a. Proof. intros. apply (runit a). Qed.

Lemma twice `{Ring R} a (h: a == a + a): a == 0. (* todo: doesn't this hold for semirings? *)
 rewrite <- (plus_opp_r a).
 rewrite h at 2.
 rewrite <- associativity.
 rewrite plus_opp_r.
 rewrite (runit a).
 reflexivity.
Qed.

Instance Ring_Semi `{Ring}: SemiRing _ _ _ _ _ := { mult_0_l := _ }.
Proof. intros. apply twice. rewrite <- distribute_r. rewrite (lunit 0). reflexivity. Qed.

Instance Ring_Semi_Morphism `{Ring_Morphism}: SemiRing_Morphism f.

Require Ring_theory.

Lemma Ring_ring_theory R `{Ring R}: Ring_theory.ring_theory 0 1 ring_plus ring_mult (fun x y => x + - y) group_inv equiv.
Proof.
 constructor; intros.
         apply plus_0_l.
        apply commutativity.
       apply associativity.
      apply mult_1_l.
     apply commutativity.
    apply associativity.
   apply distribute_r.
  reflexivity.
 apply plus_opp_r.
Qed.

Lemma SemiRing_semi_ring_theory R `{SemiRing R}: Ring_theory.semi_ring_theory 0 1 ring_plus ring_mult equiv.
Proof with try reflexivity.
 constructor; intros.
        apply plus_0_l.
       apply commutativity.
      apply associativity.
     apply mult_1_l.
    apply mult_0_l.
   apply commutativity.
  apply associativity.
 apply distribute_r.
Qed.
