Set Automatic Introduction.

Require Import Structures Program Morphisms util.

Instance compose_semiring_morphisms A B C `{SemiRing A} `{SemiRing B} `{SemiRing C} (f: A -> B) (g: B -> C)
 `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}:
  SemiRing_Morphism (fun x => g (f x)).
Proof with try reflexivity.
 intros.
 assert (Proper (equiv ==> equiv) (fun x: A => g (f x))).
  intros x y E.
  rewrite E...
 repeat (constructor; try apply _); intros.
    do 2 rewrite preserves_sg_op...
   pose proof (preserves_mon_unit). rewrite H3.
   apply (@preserves_mon_unit B C _ _ _ _ _ _ _ _).
  do 2 rewrite preserves_sg_op...
 unfold mon_unit.
 pose proof (@preserves_mon_unit A B _ _ one one0 _ _ f _). rewrite H3.
 apply (@preserves_mon_unit B C _ _ _ _ _ _ _ _).
Qed. (* todo: this belongs elsewhere, and should follow from UA stuff *)

Instance compose_ring_morphisms A B C `{Ring A} `{Ring B} `{Ring C} (f: A -> B) (g: B -> C)
 `{!Ring_Morphism f} `{!Ring_Morphism g}:
  Ring_Morphism (fun x => g (f x)).
Proof with try reflexivity.
 intros.
 assert (Proper (equiv ==> equiv) (fun x: A => g (f x))).
  intros x y E.
  rewrite E...
 repeat (constructor; try apply _); intros.
     do 2 rewrite preserves_sg_op...
    pose proof (preserves_mon_unit). rewrite H3.
    apply (@preserves_mon_unit B C _ _ _ _ _ _ _ _).
   do 2 rewrite preserves_inv...
  do 2 rewrite preserves_sg_op...
 unfold mon_unit.
 pose proof (@preserves_mon_unit A B _ _ one one0 _ _ f _). rewrite H3.
 apply (@preserves_mon_unit B C _ _ _ _ _ _ _ _).
Qed. (* todo: this belongs elsewhere, and should follow from UA stuff *)

Require UniversalAlgebra.
Module UA := UniversalAlgebra.
Import UA.notations.

Section srm. Context `{SemiRing_Morphism}.
  Existing Instance a_sg.
  Lemma preserves_0: f 0 == 0.
  Proof. intros. apply (@preserves_mon_unit _ _ _ _ _ _ _ _ f _). Qed.
  Lemma preserves_1: f 1 == 1.
  Proof. intros. apply (@preserves_mon_unit _ _ _ _ _ _ _ _ f _). Qed.
  Lemma preserves_mult: forall x y, f (x * y) == f x * f y.
  Proof. intros. apply preserves_sg_op. Qed.
  Lemma preserves_plus: forall x y, f (x + y) == f x + f y.
  Proof. intros. apply preserves_sg_op. Qed.
End srm.

Section rm. Context `{Ring_Morphism}.
  Lemma preserves_opp x: f (- x) == - f x.
  Proof. intros. apply preserves_inv. Qed.
End rm.

Lemma plus_opp_r `{Ring} x: x + -x == 0. Proof. intros. apply (inv_r x). Qed.
Lemma plus_opp_l `{Ring} x: -x + x == 0. Proof. intros. apply (inv_l x). Qed.
Lemma plus_0_r `{SemiRing} x: x + 0 == x. Proof. intros. apply (monoid_runit x). Qed.
Lemma plus_0_l `{SemiRing} x: 0 + x == x. Proof. intros. apply (monoid_lunit x). Qed.
Lemma mult_1_l `{SemiRing}: forall a, 1 * a == a. Proof. intros. apply (monoid_lunit a). Qed.
Lemma mult_1_r `{SemiRing}: forall a, a * 1 == a. Proof. intros. apply (monoid_runit a). Qed.

Lemma plus_mul_distribute_r `{Ring} x y z: (x + y) * z == x * z + y * z. Proof. apply distribute_r. Qed.
Lemma plus_mul_distribute_l `{Ring} x y z: x * (y + z) == x * y + x * z. Proof. apply distribute_l. Qed.

Lemma twice `{Ring R} a (h: a == a + a): a == 0. (* todo: doesn't this hold for semirings? *)
 rewrite <- (plus_opp_r a).
 rewrite h at 2.
 rewrite <- associativity.
 rewrite plus_opp_r.
 rewrite (monoid_runit a).
 reflexivity.
Qed.

Instance Ring_Semi `{Ring}: !SemiRing _ := { mult_0_l := _ }.
Proof. intros. apply twice. rewrite <- distribute_r. rewrite (monoid_lunit 0). reflexivity. Qed.

Instance Ring_Semi_Morphism `{Ring_Morphism}: SemiRing_Morphism f.
 pose proof ringmor_a.
 pose proof ringmor_b.
 constructor; apply _.
Qed.

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
