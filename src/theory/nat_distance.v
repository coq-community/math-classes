Require
  orders.naturals peano_naturals theory.cut_minus.
Require Import
  Morphisms Ring
  abstract_algebra interfaces.naturals interfaces.additional_operations.

Section contents.
Context `{Naturals N}.
Add Ring N : (rings.stdlib_semiring_theory N).

(* NatDistance instances are all equivalent, because their behavior is fully
 determined by the specification. *)
Program Lemma nat_distance_unique_respectful {a b: NatDistance N} : ((=) ==> (=) ==> (=))%signature a b.
Proof with intuition.
  intros ? ? x1 y1 E x2 y2 F.
  destruct a as [z1 [A|A]], b as [z2 [B|B]]; simpl.
     apply (left_cancellation (+) x1)... rewrite A, E, B...
    destruct (naturals.zero_sum z1 z2).
     apply (left_cancellation (+) x1)...
     rewrite associativity, A, F, B, E. ring.
    transitivity 0...
   destruct (naturals.zero_sum z1 z2).
   rewrite commutativity.
   apply (left_cancellation (+) y1)...
   rewrite associativity, B, <-F, A, E. ring.
   transitivity 0...
  apply (left_cancellation (+) x2)...
  rewrite A, E, F, B...
Qed.

Lemma nat_distance_unique {a b: NatDistance N} {x y : N} : a x y = b x y.
Proof. apply nat_distance_unique_respectful; reflexivity. Qed.

Context `{nd : !NatDistance N}.

Global Instance nat_distance_proper : Proper ((=) ==> (=) ==> (=)) nat_distance.
Proof. apply nat_distance_unique_respectful. Qed.
End contents.

(* We can make an instance of [NatDistance] using [CutMinus] *)
Program Instance natdistancecut_minus `{Naturals N} `{!SemiRingOrder oN} `{!TotalOrder oN} `{!CutMinus N} : NatDistance N 
  := λ x y, if decide (x ≤ y) then y ∸ x else x ∸ y.
Next Obligation. 
  left. rewrite commutativity.
  apply cut_minus.cut_minus_precedes. assumption.
Qed.

Next Obligation.
  right. rewrite commutativity.
  apply cut_minus.cut_minus_precedes, orders.precedes_flip. assumption.
Qed.

(* Using that we can make a default instance, because we have a [CutMinus] for [nat] *)
Global Program Instance natdistance_default `{Naturals N} : NatDistance N | 10 := λ x y: N,
  naturals_to_semiring nat N (nat_distance (naturals_to_semiring N nat x) (naturals_to_semiring N nat y)).
Next Obligation.
  unfold nat_distance.
  destruct nat_distance_sig as [z [F|F]]; simpl.
  left.
   rewrite <- (naturals.to_semiring_involutive N nat y).
   rewrite <- F.
   rewrite rings.preserves_plus.
   rewrite (naturals.to_semiring_involutive N nat).
   reflexivity.
  right.
  rewrite <- (naturals.to_semiring_involutive N nat x).
  rewrite <- F.
  rewrite rings.preserves_plus.
  rewrite (naturals.to_semiring_involutive N nat).
  reflexivity.
Qed.
