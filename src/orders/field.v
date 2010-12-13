Set Automatic Introduction.

Require
  theory.naturals.
Require Import
  Relation_Definitions Morphisms Ring Field
  abstract_algebra interfaces.naturals theory.fields theory.rings.

Section decfield_order. 
  Context `{Field F} `{∀ x y: F, Decision (x = y)}.

  Add Ring F: (stdlib_ring_theory F).
    (* Trying to register F as a field fails with an obscure error. Looks like a Coq bug.
     Fortunately we only need [ring] right now. *)

  Global Instance field_precedes: Order F | 8 := λ x y: F,
    ∃ num: nat, ∃ den: nat,
     x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den = y.

  Global Instance field_precedes_proper: Proper ((=) ==> (=) ==> iff) field_precedes.
  Proof with assumption.
   intros x x' E y y' E'. unfold field_precedes.
   split; intros [num [den U]]; exists num, den.
    rewrite <- E, <- E'...
   rewrite E, E'...
  Qed.

  Global Instance field_precedes_reflexive: Reflexive field_precedes.
  Proof. intro. exists (0:nat), (0:nat). rewrite preserves_0. ring. Qed.

  (* field_precedes can actually only happen if the denominator is nonzero: *)

  Lemma field_precedes_with_nonzero_nat_denominator (x y: F): x ≤ y → 
    ∃ num: nat, ∃ den: nat, den ≠ 0 ∧
     x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den = y.
  Proof with eauto.
   intros [num [den E]].
   destruct (decide (den = 0)) as [A|A]...
   exists (0:nat), (1:nat).
   split. discriminate.
   rewrite <- E, A, preserves_0, preserves_1, dec_mult_inv_0.
   ring.
  Qed.

  (* And if the map from nat to F is injective, we know even more: *)

  Context `{!Injective (naturals_to_semiring nat F)}.

  Lemma field_precedes_with_nonzero_denominator (x y: F): x ≤ y →
    ∃ num: nat, ∃ den: nat, naturals_to_semiring nat F den ≠ 0 ∧
      x + naturals_to_semiring nat F num * / naturals_to_semiring nat F den = y.
  Proof with auto.
   intros [num [den E]].
   destruct (decide (den = 0)) as [A|A].
    exists (0:nat), (1:nat).
    rewrite preserves_1, preserves_0.
    split. apply (ne_zero 1).
    rewrite <- E, A, preserves_0, dec_mult_inv_0.
    ring.
   exists num, den. split... intro. apply A.
   apply (injective (naturals_to_semiring nat F)).
   rewrite preserves_0...
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
     naturals_to_semiring nat F num * / naturals_to_semiring nat F den = 0) as E1.
    apply (left_cancellation (+) y)...
    rewrite plus_0_r.
    rewrite associativity...
   set (naturals_to_semiring nat F) in *. 
   assert (f den' * / f den' * f den * f num' + f den * / f den * f num * f den' = f den * f den' * 0) as E2.
    rewrite <- E1 at 1. ring.
   rewrite dec_mult_inverse in E2...
   rewrite dec_mult_inverse in E2...
   ring_simplify in E2.
   do 2 rewrite <- preserves_mult in E2.
   rewrite <- preserves_plus in E2.
   destruct (zero_product (f den) (f num')) as [E3|E3].
     assert (den * num' + num * den' = 0) as E3. apply (injective f)...
     destruct (theory.naturals.zero_sum (den * num') (num * den') E3) as [E4a E4b].
     rewrite <- preserves_mult. rewrite E4a. apply preserves_0.
    intuition.
   rewrite E3. ring.
  Qed. (* Todo: can be cleaned up further. *)

  Global Instance field_partialorder: PartialOrder field_precedes.

  Lemma ringorder_plus: ∀ `(x ≤ y) (z : F), x + z ≤ y + z.
  Proof. intros x y [num [den E]] z. exists num, den. rewrite <- E. ring. Qed.

  Lemma ringorder_mult: ∀ x: F, 0 ≤ x → ∀ y: F, 0 ≤ y → 0 ≤ x * y.
  Proof.
   intros x [num [den E]] y [num' [den' G]].
   exists (num * num'), (den * den').
   rewrite <- G, <- E, preserves_mult, preserves_mult, dec_mult_inv_distr.
   ring.
  Qed.

  Global Instance field_ringorder: RingOrder field_precedes.
  Proof with auto.
    split; try apply _.
     intros; apply ringorder_plus...
    intros; apply ringorder_mult...
  Qed.

End decfield_order.

Instance: Params (@field_precedes) 8.
