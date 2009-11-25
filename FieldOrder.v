Set Automatic Introduction.

Require Import Relation_Definitions Morphisms Structures AbstractNaturals nat_Naturals RingOps Ring AbstractProperties FieldOps.

Section decfield_order. Context `{Field F} `{forall x y: F, Decision (x == y)}.

  Add Ring F: (Ring_ring_theory F).

  Instance field_precedes: Order F := fun x y: F =>
    exists num: nat, exists den: nat, x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den == y.

  Lemma ook (x y: F): x <= y -> 
    exists num: nat, exists den: nat, ~ den == 0 /\ x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den == y.
  Proof.
   intros.
   destruct H1.
   destruct H1.
   destruct x1.
    pose proof (_: Proper (equiv ==> equiv) dec_mult_inv).
    exists 0.
    exists 1.
    split.
     discriminate. 
    assert (naturals_to_semiring nat F 0 == 0).
     apply preserves_0.
    set (naturals_to_semiring nat F) in *.
    rewrite <- H1.
    rewrite H3.
    rewrite inv_0.
    ring.
   exists x0.
   exists (S x1).
   split.
    discriminate.
   assumption.
  Qed.

  Lemma wtf n: ~ 1 + naturals_to_semiring nat F n == naturals_to_semiring nat F n.
   pattern n.
   apply Naturals_ordinary_ind.
     repeat intro.
     rewrite H1.
     intuition.
    rewrite preserves_0.
    rewrite plus_0_r.
    intro.
    apply field_0neq1.
    symmetry.
    assumption.
   intros.
   rewrite preserves_plus.
   rewrite preserves_1.
   intro.
   apply H1.
   clear H1.
   apply (plus_reg_l) with 1.
   assumption.
  Qed.

  Context `{!Injective (naturals_to_semiring nat F)}.

  Lemma enzelfs (x y: F): x <= y -> 
    exists num: nat, exists den: nat, ~ naturals_to_semiring nat F den == 0 /\
      x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den == y.
  Proof.
   intros.
   destruct H1.
   destruct H1.
   destruct x1.
    pose proof (_: Proper (equiv ==> equiv) dec_mult_inv).
    exists 0.
    exists 1.
    split.
     rewrite preserves_1.
     intro.
     apply field_0neq1.
     symmetry.
     assumption.
    assert (naturals_to_semiring nat F 0 == 0).
     apply preserves_0.
    set (naturals_to_semiring nat F) in *.
    rewrite <- H1.
    rewrite H3.
    rewrite inv_0.
    ring.
   exists x0.
   exists (S x1).
   split; [| assumption].
   intros.
   intro.
   absurd (S x1 = 0).
    discriminate.
   apply (injective (naturals_to_semiring nat F) (S x1) 0).
   rewrite H2.
   reflexivity.
  Qed.

  Global Instance field_precedes_proper: Proper (equiv ==> equiv ==> iff) field_precedes.
  Proof with assumption.
   intros x x' E y y' E'. unfold field_precedes.
   split; intros [num [den U]]; exists num, den.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance field_precedes_reflexive: Reflexive field_precedes.
  Proof.
   pose proof (_: Proper (equiv ==> equiv) dec_mult_inv).
   intros x.
   unfold field_precedes.
   exists 0.
   exists 0.
   assert (naturals_to_semiring nat F 0 == 0).
    apply preserves_0.
   assert (/ naturals_to_semiring nat F 0 == 0).
    set (naturals_to_semiring nat F 0) in *.
    rewrite H2.
    unfold dec_mult_inv.
    destruct decide.
     reflexivity.
    intuition.
   set (naturals_to_semiring nat F 0) in *.
   rewrite H2.
   rewrite mult_0_l.
   rewrite plus_0_r.
   reflexivity.
  Qed.

  Global Instance field_precedes_transitive: Transitive field_precedes.
  Proof with auto.
   pose proof (_: Proper (equiv ==> equiv) dec_mult_inv).
   intros x y z E G.
   destruct (enzelfs _ _ E) as [num [den [A U]]].
   destruct (enzelfs _ _ G) as [num' [den' [B V]]].
   clear E G.
   unfold field_precedes.
   exists (num * den' + num' * den), (den * den').
   rewrite <- V, <- U. clear V U.
   rewrite preserves_plus.
   repeat rewrite preserves_mult.
   set (naturals_to_semiring nat F) in *. 
   rewrite distribute_r.
   rewrite dec_mult_inv_distr. 
   transitivity (x + (f num * / f den * (f den' * / f den') + f num' * / f den' * (f den * / f den))). ring.
   rewrite dec_mult_inverse...
   rewrite dec_mult_inverse...
   ring.
  Qed.

  Global Instance field_preorder: PreOrder field_precedes.

  Instance: AntiSymmetric field_precedes.
  Proof with auto.
   intros x y E G. 
   destruct (enzelfs _ _ E) as [num [den [A U]]].
   destruct (enzelfs _ _ G) as [num' [den' [B V]]].
   clear E G.
   rewrite <- V in U |- *.
   clear V x.
   assert (naturals_to_semiring nat F num' * / naturals_to_semiring nat F den' +
     naturals_to_semiring nat F num * / naturals_to_semiring nat F den == 0).
    apply (plus_reg_l) with y.
    rewrite plus_0_r.
    rewrite associativity.
    assumption.
   set (naturals_to_semiring nat F) in *. 
   assert (f den' * / f den' * f den * f num' + f den * / f den * f num * f den' == f den * f den' * 0).
    rewrite <- H1 at 3.
    ring.
   rewrite dec_mult_inverse in H2...
   rewrite dec_mult_inverse in H2...
   ring_simplify in H2.
   do 2 rewrite <- preserves_mult in H2.
   rewrite <- preserves_plus in H2.
   assert (den * num' + num * den' == 0).
    apply (injective f).
    assumption.
   destruct (naturals_zero_sum _ _ H3).
   assert (f den * f num' == 0). rewrite <- preserves_mult. rewrite H4. apply preserves_0.
   destruct (zero_product _ _ H6). intuition.
   rewrite H7.
   ring.
  Qed.

  Global Instance field_partialorder: PartialOrder field_precedes.

  Lemma ringorder_plus: forall x y: F, x <= y -> forall z, (x + z) <= (y + z).
   intros x y [num [den E]] z. 
   exists num, den. rewrite <- E. ring.
  Qed.

  Lemma ringorder_mult: forall x: F, 0 <= x -> forall y: F, 0 <= y -> 0 <= (x * y).
   intros x [num [den E]] y [num' [den' G]].
   exists (num * num'), (den * den').
   rewrite <- G, <- E.
   pose proof (_: Proper (equiv ==> equiv) dec_mult_inv).
   do 2 rewrite preserves_mult.
   rewrite dec_mult_inv_distr.
   ring.
  Qed.

  Global Instance field_ringorder: RingOrder _ _ _ _ field_precedes
    := { ringorder_plus := ringorder_plus; ringorder_mult := ringorder_mult }.

End decfield_order.
