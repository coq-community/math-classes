Require
  orders.naturals peano_naturals.
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

Context `{!NatDistance N}.

Global Instance nat_distance_proper : Proper ((=) ==> (=) ==> (=)) nat_distance.
Proof. apply nat_distance_unique_respectful. Qed.
End contents.

(* An existing instance of [CutMinus] allows to create an instance of [NatDistance] *)
Program Instance natdistancecut_minus `{Naturals N} `{!SemiRingOrder oN} 
       `{!TotalOrder oN} `{!CutMinusSpec N cm} `{∀ x y, Decision (x ≤ y)} : NatDistance N 
  := λ x y, if decide_rel (≤) x y then y ∸ x else x ∸ y.
Next Obligation. 
  left. rewrite commutativity.
  now apply cut_minus_precedes.
Qed.
Next Obligation.
  right. rewrite commutativity.
  now apply cut_minus_precedes, orders.precedes_flip.
Qed.

(* Using the preceding instance we can make an instance for arbitrary models of the naturals
    by translation into [nat] on which we already have a [CutMinus] instance. *)
Global Program Instance natdistance_default `{Naturals N} : NatDistance N | 10 := λ x y: N,
  naturals_to_semiring nat N (nat_distance (naturals_to_semiring N nat x) (naturals_to_semiring N nat y)).
Next Obligation.
  unfold nat_distance.
  destruct nat_distance_sig as [z [F|F]]; simpl.
  left.
   rewrite <- (naturals.to_semiring_involutive N nat y).
   rewrite <- F.
   rewrite rings.preserves_plus.
   now rewrite (naturals.to_semiring_involutive N nat).
  right.
  rewrite <- (naturals.to_semiring_involutive N nat x).
  rewrite <- F.
  rewrite rings.preserves_plus.
  now rewrite (naturals.to_semiring_involutive N nat).
Qed.
