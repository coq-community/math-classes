Set Automatic Introduction.

Require Import
 Relation_Definitions Morphisms
 Structures nat_Naturals RingOps Ring BoringInstances AbstractProperties.
Require Export
 AbstractNaturals.

Section contents. Context `{Naturals N}.

  Add Ring N: (SemiRing_semi_ring_theory N).

  Global Instance: AntiSymmetric natural_precedes.
   intros x y [v A] [w B].
   rewrite <- A in *. clear A.
   change (x + v + w == x) in B.
   change (x == x + v).
   rewrite <- associativity in B.
   assert (v + w == 0) as C.
    apply (injective (ring_plus x)). rewrite plus_0_r. assumption.
   destruct (naturals_zero_sum v w C) as [D _]. rewrite D.
   ring.
  Qed.

  Global Instance: PartialOrder natural_precedes.

  Obligation Tactic := idtac.

  Global Program Instance: forall x y: N, Decision (x <= y) | 10 :=
    match decide (natural_precedes (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y)) with
    | left E => left _
    | right E => right _
    end.

  Next Obligation.
   intros.
   apply (preserves_naturals_order (naturals_to_semiring N nat) x y).
   assumption. 
  Qed.

  Next Obligation.
   intros.
   apply E.
   apply (preserves_naturals_order (naturals_to_semiring N nat) x y).
   assumption. 
  Qed.

  Global Program Instance: NatDistance N | 10 := fun (x y: N) => 
    naturals_to_semiring _ N (proj1_sig (nat_distance (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y))).

  Next Obligation.
   intros. destruct nat_distance. simpl.
   destruct o; [left | right].
    rewrite <- (iso_nats N nat y).
    rewrite <- H1.
    rewrite preserves_sg_op.
    rewrite (iso_nats N nat).
    reflexivity.
   rewrite <- (iso_nats N nat x).
   rewrite <- H1.
   rewrite preserves_sg_op.
   rewrite (iso_nats N nat).
   reflexivity.
  Qed.

  Global Program Instance: forall x y: N, Decision (x == y) | 10 :=
    match Peano_dec.eq_nat_dec (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y) with
    | left E => left _
    | right E => right _
    end.
 
  Next Obligation.
   intros.
   rewrite <- (iso_nats _ nat x), <- (iso_nats _ nat y).
   rewrite E. reflexivity.
  Qed.

  Next Obligation.
   intros.
   apply E.
   change (naturals_to_semiring _ nat x == naturals_to_semiring _ nat y).
   apply (naturals_to_semiring_mor _ nat).
   assumption.
  Qed.

  Global Instance: ZeroProduct N.
  Proof with intuition.
   intros a b E.
   destruct (decide (a == 0))...
   destruct (decide (b == 0))...
   exfalso. apply (naturals_nz_mult_nz b a)...
  Qed.

  Lemma nats_le_mult_compat_inv_l (x x' y: N): ~ y == 0 -> x * y <= x' * y -> x <= x'.
  Proof.
   destruct (total_order x x') as [|[z E]]. intuition.
   rewrite <- E. clear E x.
   unfold precedes, natural_precedes, SemiGroupOrder.sg_precedes.
   intros ne [v F].
   exists 0.
   apply (naturals_mult_injective y). assumption.
   destruct (naturals_zero_sum (z * y) v) as [A _].
    apply (injective (ring_plus (x' * y))). 
    change ((x' + z) * y + v == x' * y) in F.
    rewrite <- F at 2. ring.
   change (y * (x' + z + 0) == y * x').
   ring_simplify. rewrite (commutativity y z), A. ring.
  Qed.

End contents.
