Set Automatic Introduction.

Require
  theory.naturals.
Require Import
  Relation_Definitions Morphisms Ring Field
  abstract_algebra interfaces.naturals theory.fields theory.rings.

Section decfield_order. Context `{Field F} `{forall x y: F, Decision (x == y)}.

  Add Ring F: (stdlib_ring_theory F).
    (* Trying to register F as a field fails with an obscure error. Looks like a Coq bug.
     Fortunately we only need [ring] right now. *)

  Instance field_precedes: Order F := fun x y: F =>
    exists num: nat, exists den: nat,
     x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den == y.

  Global Instance field_precedes_proper: Proper (equiv ==> equiv ==> iff) field_precedes.
  Proof with assumption.
   intros x x' E y y' E'. unfold field_precedes.
   split; intros [num [den U]]; exists num, den.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance field_precedes_reflexive: Reflexive field_precedes.
  Proof. intro. exists (0:nat), (0:nat). rewrite preserves_0. ring. Qed.

  (* field_precedes can actually only happen if the denominator is nonzero: *)

  Lemma field_precedes_with_nonzero_nat_denominator (x y: F): x <= y -> 
    exists num: nat, exists den: nat, ~ den == 0 /\
     x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den == y.
  Proof with auto.
   intros [x0 [x1 H1]].
   destruct x1.
    exists (0:nat), (1:nat).
    split. discriminate.
    change (x + naturals_to_semiring nat F x0 * / naturals_to_semiring nat F 0 == y) in H1.
    fold 0 in H1.
    rewrite <- H1, preserves_0, preserves_0, inv_0. ring.
   exists x0, (S x1).
   split... discriminate.
  Qed. (* Todo: can be cleaned up further. *)

  (* And if the map from nat to F is injective, we know even more: *)

  Context `{!Injective (naturals_to_semiring nat F)}.

  Lemma field_precedes_with_nonzero_denominator (x y: F): x <= y -> 
    exists num: nat, exists den: nat, ~ naturals_to_semiring nat F den == 0 /\
      x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den == y.
  Proof with auto.
   intros [x0 [[|x1] E]].
    exists (0:nat), (1:nat).
    rewrite preserves_1, preserves_0.
    split. intro. apply field_0neq1. symmetry...
    change (x + naturals_to_semiring nat F x0 * / naturals_to_semiring nat F 0 == y) in E.
    rewrite <- E, preserves_0, inv_0. ring.
   exists x0, (S x1).
   split... intro  U.
   absurd (S x1 = 0). discriminate.
   apply (injective (naturals_to_semiring nat F)).
   rewrite U. reflexivity.
  Qed.

  Global Instance field_precedes_transitive: Transitive field_precedes.
  Proof with auto.
   intros x y z E G.
   destruct (field_precedes_with_nonzero_denominator _ _ E) as [num [den [A U]]].
   destruct (field_precedes_with_nonzero_denominator _ _ G) as [num' [den' [B V]]].
   unfold field_precedes.
   exists (num * den' + num' * den), (den * den').
   rewrite <- V, <- U.
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
   destruct (field_precedes_with_nonzero_denominator _ _ E) as [num [den [A U]]].
   destruct (field_precedes_with_nonzero_denominator _ _ G) as [num' [den' [B V]]].
   clear E G.
   rewrite <- V in U |- *.
   clear V x.
   assert (naturals_to_semiring nat F num' * / naturals_to_semiring nat F den' +
     naturals_to_semiring nat F num * / naturals_to_semiring nat F den == 0).
    apply (injective (ring_plus y)).
    rewrite plus_0_r.
    rewrite associativity...
   set (naturals_to_semiring nat F) in *. 
   assert (f den' * / f den' * f den * f num' + f den * / f den * f num * f den' == f den * f den' * 0).
    rewrite <- H1 at 1. ring.
   rewrite dec_mult_inverse in H2...
   rewrite dec_mult_inverse in H2...
   ring_simplify in H2.
   do 2 rewrite <- preserves_mult in H2.
   rewrite <- preserves_plus in H2.
   destruct (zero_product (f den) (f num')).
     assert (den * num' + num * den' == 0). apply (injective f)...
     destruct (theory.naturals.zero_sum (den * num') (num * den') H3).
     rewrite <- preserves_mult. rewrite H4. apply preserves_0.
    intuition.
   rewrite H3. ring.
  Qed. (* Todo: can be cleaned up further. *)

  Global Instance field_partialorder: PartialOrder field_precedes.

  Lemma ringorder_plus: forall x y: F, x <= y -> forall z, x + z <= y + z.
  Proof. intros x y [num [den E]] z. exists num, den. rewrite <- E. ring. Qed.

  Lemma ringorder_mult: forall x: F, 0 <= x -> forall y: F, 0 <= y -> 0 <= x * y.
  Proof.
   intros x [num [den E]] y [num' [den' G]].
   exists (num * num'), (den * den').
   rewrite <- G, <- E, preserves_mult, preserves_mult, dec_mult_inv_distr.
   ring.
  Qed.

  Global Instance field_ringorder: RingOrder _ _ _ _ field_precedes
    := { ringorder_plus := ringorder_plus; ringorder_mult := ringorder_mult }.

End decfield_order.
