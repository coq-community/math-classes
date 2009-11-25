(* Things we can prove once we have a model (simpleZ). *)

Set Automatic Introduction.

Require Export AbstractIntegers.
Require Import RelationClasses Morphisms Ring.
Require Import simpleZ RingOps Naturals AbstractProperties nat_Naturals Structures SemiRingOrder.

Section contents.

  Context `{Integers Int}.

  Add Ring Int: (Ring_ring_theory Int).

  Let itoZnat_mor := integers_to_ring_mor (Z nat).
  Let nat_to_Int_mor := _: Proper (equiv ==> equiv) (naturals_to_semiring nat Int).

  Global Program Instance: forall x y: Int, Decision (x == y) | 10 :=
    match decide (integers_to_ring _ (Z nat) x == integers_to_ring _ (Z nat) y) with
    | left E => left _
    | right E => right _
    end.

  Next Obligation. rewrite <- (iso_ints (Z nat) x), <- (iso_ints (Z nat) y), E. reflexivity. Qed.
  Next Obligation. apply E. rewrite H1. reflexivity. Qed.

  Global Instance naturals_to_integers_injective `{Naturals N}: Injective (naturals_to_semiring N Int).
  Proof.
   set (itoZN_mor := integers_to_ring_mor (Z N)).
   intros x y E.
   rewrite <- (plus_0_r x), <- (plus_0_r y).
   change (NtoZ N x == NtoZ N y).
   do 2 rewrite <- (NtoZ_uniq N).
   rewrite <- (naturals_to_semiring_unique (Z N) (fun x => integers_to_ring Int (Z N) (naturals_to_semiring N Int x))).
    rewrite <- (naturals_to_semiring_unique (Z N) (fun x => integers_to_ring Int (Z N) (naturals_to_semiring N Int x))).
     rewrite E. reflexivity.
    apply _.
   apply _.
  Qed.

  Instance: AntiSymmetric integer_precedes.
   intros x y.
   intros [v p] [w q].
   rewrite <- p in *.
   clear p y.
   rewrite <- associativity in q.
   rewrite <- (plus_0_r x) in q at 2.
   pose proof (plus_reg_l _ _ _ q).
   rewrite <- preserves_plus in H1.
   assert (naturals_to_semiring nat Int (v + w) == naturals_to_semiring nat Int 0).
    rewrite H1. symmetry. apply preserves_0.
   pose proof (naturals_to_integers_injective (v + w) 0 H2).
   destruct (naturals_zero_sum v w H3).
   rewrite H4.
   rewrite preserves_0.
   ring.
  Qed. (* ugh.. *)

  Global Instance: PartialOrder integer_precedes.

  Global Instance: ZeroNeOne Int.
   intros E.
   apply (@zero_ne_one nat _ _ _ _).
   apply (injective (naturals_to_semiring nat Int)). 
   set (naturals_to_semiring nat Int).
   rewrite preserves_0, preserves_1. assumption.
  Qed.

  Lemma abs_uniq `{Naturals N} (a a': IntAbs Int N): forall z: Int, proj1_sig (a z) == proj1_sig (a' z).
  Proof with try apply neg_precedes_pos.
   intros.
   destruct a.
   destruct a'.
   simpl.
   apply (injective (naturals_to_semiring N Int)).
   destruct o; destruct o0; rewrite <- H3 in H4; clear H3.
      symmetry. assumption.
     apply (@antisymmetry _ _ integer_precedes _).
      rewrite <- H4...
     apply <- precedes_flip.
     rewrite H4...
    apply (@antisymmetry _ _ integer_precedes _).
     apply <- precedes_flip.
     rewrite <- H4...
    rewrite H4...
   apply (injective group_inv).
   symmetry. assumption.
  Qed.

Lemma abs_nat `{Naturals N} `{!IntAbs Int N} (n: N): int_abs' Int N (naturals_to_semiring N Int n) == n.
  Proof.
   unfold int_abs'. destruct int_abs. simpl.
   apply (injective (naturals_to_semiring N Int)).
   destruct o. assumption.
   apply (@antisymmetry _ _ integer_precedes _).
    apply <- precedes_flip. rewrite H3. apply neg_precedes_pos.
   rewrite <- H3. apply neg_precedes_pos.
  Qed. 
  
  Lemma abs_opp_nat `{Naturals N} `{!IntAbs Int N} (n: N): int_abs' Int N (- naturals_to_semiring N Int n) == n.
  Proof.
   unfold int_abs'. destruct int_abs. simpl. apply (injective (naturals_to_semiring N Int)). 
   destruct o. 
    apply (@antisymmetry _ _ integer_precedes _).
     rewrite H3. apply neg_precedes_pos.
    apply <- precedes_flip. rewrite <- H3. apply neg_precedes_pos.
   apply (injective group_inv). assumption.
  Qed. 
  
  Lemma neg_is_pos `{Naturals N} (x y: N): - naturals_to_semiring N Int x == naturals_to_semiring N Int y -> x == 0 /\ y == 0.
  Proof.
   intro E.
   split; apply (injective (naturals_to_semiring N Int)); apply (@antisymmetry _ _ integer_precedes _).
      apply <- precedes_flip. rewrite E. apply neg_precedes_pos.
     rewrite preserves_0. apply zero_sr_precedes_nat.
    rewrite <- E. apply neg_precedes_pos.
   rewrite preserves_0.
   apply zero_sr_precedes_nat.
  Qed. 
  
  Global Instance int_abs'_proper `{Naturals N} `{!IntAbs Int N}: Proper (equiv ==> equiv) (int_abs' Int N).
  Proof with reflexivity.
   intros z z' E.
   unfold int_abs'.
   do 2 destruct int_abs.
   simpl.
   rewrite E in o. 
   clear E z.
   apply (injective (naturals_to_semiring N Int)).
   destruct o; destruct o0.
      rewrite H3, H4...
     rewrite <- H3 in H4.
     destruct (neg_is_pos _ _ H4).
     rewrite H5, H6...
    rewrite <- H4 in H3.
    destruct (neg_is_pos _ _ H3).
    rewrite H5, H6... 
   apply (injective group_inv). 
   rewrite H3, H4...
  Qed. 
  
  Lemma abs_nat' `{Naturals N} `{Naturals N'} `{!IntAbs Int N} (n: N'): int_abs' Int N (naturals_to_semiring N' Int n) == naturals_to_semiring N' N n.
  Proof.
   rewrite <- (naturals_to_semiring_unique Int (fun x => naturals_to_semiring N Int (naturals_to_semiring N' N x))).
    rewrite abs_nat.
    reflexivity.
   apply (compose_semiring_morphisms _ _ _ _ _).
  Qed.
  
  Lemma abs_opp `{Naturals N} `{!IntAbs Int N} z: int_abs' Int N (- z) == int_abs' Int N z.
  Proof.
   unfold int_abs' at 2.
   destruct int_abs as [x [E | E]]; simpl; rewrite <- E.
    apply abs_opp_nat.
   rewrite inv_involutive.
   apply abs_nat.
  Qed.
  
  Obligation Tactic := idtac.
  
  Global Program Instance slow_int_abs `{Naturals N}: IntAbs Int N | 10 :=
    fun x => exist _ (proj1_sig (int_abs (Z N) N (integers_to_ring Int (Z N) x))) _.
  
  Next Obligation.
   intros.
   destruct (int_abs _ _ (integers_to_ring Int (Z N) x)) as [x0 [M|M]]; simpl; [left | right].
    rewrite <- (iso_ints (Z N) x).
    rewrite <- M.
    symmetry.
    apply (naturals_to_semiring_unique Int (fun x => integers_to_ring (Z N) Int (naturals_to_semiring N (Z N) x))).
    apply _.
   rewrite <- (iso_ints (Z N) x).
   rewrite <- M.
   rewrite preserves_inv. 
   apply inv_proper. 
   symmetry.
   apply (naturals_to_semiring_unique Int (fun x => integers_to_ring (Z N) Int (naturals_to_semiring N (Z N) x))).
   apply _.
  Qed.
  
  Lemma eq_opp_self (z: Int): z == -z -> z == 0.
  Proof with auto.
   intros.
   destruct (int_abs Int nat z).
   assert (naturals_to_semiring nat Int x == z).
    destruct o...
    rewrite H1.
    rewrite <- H2.
    rewrite inv_involutive.
    reflexivity.
   clear o.
   rewrite <- H2 in *.
   clear H2.
   apply antisymmetry...
    rewrite H1.
    apply -> precedes_0_flip.
    apply zero_sr_precedes_nat.
   apply zero_sr_precedes_nat.
  Qed.
  
  Global Instance integers_zero_product: ZeroProduct Int.
   intros x y E.
   destruct (int_abs Int nat x).
   destruct (int_abs Int nat y).
   assert (x0 * x1 == 0) as U.
    apply (injective (naturals_to_semiring _ _)).
    set (naturals_to_semiring nat Int) in *.
    rewrite preserves_mult, preserves_0.
    rewrite <- ring_opp_mult_opp.
    destruct o; destruct o0; rewrite H1, H2.
       rewrite ring_opp_mult_opp, E. ring.
      rewrite <- ring_distr_opp_mult, E. ring.
     rewrite commutativity, <- ring_distr_opp_mult, commutativity, E. ring.
    assumption.
   set (naturals_to_semiring nat Int) in *.
   destruct o; rewrite <- H1 in E |- *; clear H1 x;
    destruct o0; rewrite <- H1 in E |- *; clear H1 y;
      destruct (zero_product x0 x1 U); rewrite H1; rewrite preserves_0;
       [left | right | left | right | left | right | left | right]; ring.
  Qed.
  
  Global Instance int_mult_injective (x: Int): ~ x == 0 -> Injective (ring_mult x).
  Proof with intuition.
   intros E y z U.
   assert (x * (y + - z) == 0) as V. rewrite distribute_l, U. ring.
   destruct (zero_product _ _ V)...
   apply equal_by_zero_sum...
  Qed.
  
End contents.

Lemma preserves_abs `{Integers A} `{Integers B} `{Naturals N} `{!IntAbs A N} `{!IntAbs B N} (f: A -> B) `{!Ring_Morphism f}: forall z: A,
  f (naturals_to_semiring N A (int_abs' A N z)) == naturals_to_semiring N B (int_abs' B N (f z)).
Proof.
 intros.
 unfold int_abs'.
 destruct int_abs.
 destruct int_abs.
 simpl.
 destruct o; destruct o0.
    rewrite H5.
    rewrite H6.
    reflexivity.
   apply (@antisymmetry B _ integer_precedes _).
    apply <- (@precedes_flip B _ _ _ _ _ _ _).
    rewrite H5.
    rewrite <- H6.
    rewrite inv_involutive.
    apply neg_precedes_pos.
   pose proof (@transitivity B sr_precedes _) as TR.
   apply TR with 0.
    apply <- (precedes_flip (naturals_to_semiring N B x0) 0).
    rewrite H6.
    rewrite <- H5.
    rewrite opp_0.
    apply preserves_nonneg.
    apply _.
   apply preserves_nonneg.
   apply _.
  apply (@antisymmetry B _ integer_precedes _).
   apply <- (@precedes_flip B _ _ _ _ _ _ _).
   rewrite <- preserves_opp.
   rewrite H5.
   rewrite <- H6.
   apply neg_precedes_pos.
  rewrite H6.
  rewrite <- H5.
  rewrite preserves_opp.
  pose proof (@transitivity B sr_precedes _) as TR.
  apply TR with 0.
   apply <- (@precedes_flip B _ _ _ _ _ _ _).
   rewrite opp_0.
   rewrite inv_involutive.
   apply preserves_nonneg.
   apply _.
  apply preserves_nonneg.
  apply _.
 apply (injective group_inv).
 rewrite H6.
 rewrite <- H5.
 symmetry.
 apply preserves_opp.
Qed. (* ugh *)

Lemma ints_preserve_sr_order `{Integers A} `{Integers B} (f: A -> B) `{!Ring_Morphism f} (x y: A):
  sr_precedes x y -> sr_precedes (f x) (f y).
Proof. intros [z p]. 
 unfold sr_precedes. 
 exists (int_abs' _ _ (f (naturals_to_semiring nat A z))).
 rewrite <- preserves_abs.
  rewrite <- p, preserves_sg_op, abs_nat. reflexivity.
 apply _. 
Qed. 

Section more. Context `{Integers Int}.

  Add Ring Int2: (Ring_ring_theory Int).

  Global Instance: TotalOrder (_: Order Int).
   intros x y.
   rewrite <- (iso_ints (Z nat) x), <- (iso_ints (Z nat) y).
   destruct (total_order (integers_to_ring Int (Z nat) x) (integers_to_ring Int (Z nat) y));
       [left | right]; apply ints_preserve_sr_order.
    apply _. assumption.
   apply _. assumption.
  Qed.

  Global Program Instance: forall x y: Int, Decision (x <= y) | 10 :=
   match decide (integers_to_ring Int (Z nat) x <= integers_to_ring Int (Z nat) y) with
   | left E => left _
   | right E => right _
   end.

  Next Obligation.
   change (x <= y). rewrite <- (iso_ints (Z nat) x), <- (iso_ints (Z nat) y).
   apply ints_preserve_sr_order. apply _. assumption.
  Qed. 

  Next Obligation.
   apply E. apply ints_preserve_sr_order. apply _. assumption.
  Qed.

  Global Instance int_le_mult_compat_r (x: Int) (xnonneg: 0 <= x): Proper (integer_precedes ==> integer_precedes) (ring_mult x).
  Proof.
   intros y y'.
   destruct xnonneg as [z E]. rewrite <- E. clear E x.
   intros [x E]. rewrite <- E. clear E y'. 
   rewrite plus_0_l.
   rewrite distribute_l.
   exists (z * x).
   rewrite preserves_mult.
   reflexivity.
  Qed.

    (* todo: by generalizing [Injective] to work with signatures, we should be able to write the following as an inverse proper thingy *)
  Lemma int_le_mult_compat_inv_l (x x' y: Int): 1 <= y -> x * y <= x' * y -> x <= x'.
  Proof.
   intros.
   destruct (total_order x x').
    assumption. 
   destruct H3.
   rewrite <- H3 in *.
   clear H3 x.
   unfold precedes, integer_precedes, sr_precedes.
   exists 0.
   cut (x0 == 0).
    intro.
    rewrite H3.
    rewrite preserves_0.
    ring.
   ring_simplify in H2.
   destruct H2.
   rewrite <- associativity in H2.
   assert (naturals_to_semiring nat Int x0 * y + naturals_to_semiring nat Int x == 0).
    apply (plus_reg_l) with (x' * y).
    rewrite H2.
    ring.
   clear H2. 
   destruct H1.
   rewrite <- H1 in *. clear H1 y.
   rewrite distribute_l in H3.
   rewrite mult_1_r in H3.
   rewrite <- preserves_mult in H3.
   rewrite <- preserves_plus in H3.
   rewrite <- preserves_plus in H3.
   assert (x0 + x0 * x1 + x == 0).
    apply (injective (naturals_to_semiring nat Int)).
    assumption.
   rewrite <- associativity in H1.
   destruct (naturals_zero_sum _ _ H1).
   assumption.
  Qed.

End more.
