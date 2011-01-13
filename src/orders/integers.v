Require
  theory.integers theory.int_abs.
Require Import
  Morphisms Ring Program Setoid
  abstract_algebra interfaces.integers interfaces.naturals interfaces.additional_operations
  natpair_integers orders.semirings orders.naturals theory.rings.

Section another_ring.
  Context `{Integers Int} {o : Order Int} `{!RingOrder o} `{!TotalOrder o} 
    `{Ring R} {oR : Order R} `{!RingOrder oR} `{!TotalOrder oR}
     {f : Int → R} `{!Ring_Morphism f}.

  Let f_preserves_0 x : 0 ≤ x → 0 ≤ f x.
  Proof.
    intros E.
    rewrite (integers.to_ring_unique f).
    destruct (int_abs_sig Int nat x) as [z [Ez | Ez]].
     rewrite <-Ez. 
     change (0 ≤ (integers_to_ring Int R ∘ naturals_to_semiring nat Int) z).
     rewrite (naturals.to_semiring_unique _).
     apply to_semiring_nonneg.
    rewrite <-Ez in E |- *.
    setoid_replace z with (0 : nat).
     rewrite preserves_0, opp_0, preserves_0. reflexivity.
    apply (injective (naturals_to_semiring nat Int)).
    rewrite preserves_0.
    apply (antisymmetry (≤)).
     apply flip_nonpos_inv. assumption.
    apply to_semiring_nonneg.
  Qed.

  Global Instance morphism_order_preserving: OrderPreserving f.
  Proof with trivial.
    apply preserving_preserves_0. apply f_preserves_0.
  Qed.

  (* Because each morphism [f] between two [Integers] implementations is injective, we
      obtain from the following lemma that the order on the integers is uniquely specified. *)
  Context `{!Injective f}.
  Let f_preserves_0_back x : 0 ≤ f x → 0 ≤ x.
  Proof with trivial.
    intros E.
    rewrite (integers.to_ring_unique f) in E.
    destruct (int_abs_sig Int nat x) as [z [Ez | Ez]].
     rewrite <-Ez.
     apply to_semiring_nonneg. 
    rewrite <-Ez in E |- *.
    setoid_replace z with (0 : nat).
     rewrite preserves_0, opp_0. reflexivity.
    apply (injective (f ∘ naturals_to_semiring nat Int)).
    rewrite (naturals.to_semiring_unique _).
    unfold compose. do 2 rewrite preserves_0.
    rewrite preserves_inv in E.
    apply (antisymmetry (≤)).
     rewrite <-(naturals.to_semiring_unique (integers_to_ring Int R ∘ naturals_to_semiring nat Int)).
     apply flip_nonpos_inv...
    apply to_semiring_nonneg.
  Qed.
  
  Global Instance: OrderEmbedding f.
  Proof with trivial.
    split. apply _.
    apply preserving_back_preserves_0. apply f_preserves_0_back.
  Qed.
End another_ring.

Section other_results.
Context `{Integers Int} `{!RingOrder o} `{!TotalOrder o} .
Add Ring Int : (rings.stdlib_ring_theory Int).

Global Program Instance: ∀ x y: Int, Decision (x ≤ y) | 10 := λ x y,
  match decide (integers_to_ring _ (SRpair nat) x ≤ integers_to_ring _ (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. 
  apply (order_preserving_back (integers_to_ring _ (SRpair nat))). 
  assumption.
Qed.
Next Obligation.
  intros F. apply E.
  apply (order_preserving _). assumption.
Qed.

Lemma induction
  (P: Int → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → (∀ n, n ≤ 0 → P n → P (n - 1)) → ∀ n, P n.
Proof with auto.
  intros P0 Psuc1 Psuc2 n.
  destruct (int_abs_sig Int nat n) as [m [E|E]].
   rewrite <-E. clear E. pattern m. 
   apply naturals.induction; clear m.
     intros ? ? E. rewrite E. tauto.
    rewrite preserves_0...
   intros m E. 
   rewrite preserves_plus, preserves_1.
   apply Psuc1... apply to_semiring_nonneg.
  rewrite <-E. clear E. pattern m. 
  apply naturals.induction; clear m.
    intros ? ? E. rewrite E. tauto.
   rewrite preserves_0, opp_0...
  intros m E. 
  rewrite preserves_plus, preserves_1.
  rewrite plus_opp_distr, commutativity.
  apply Psuc2...
  apply inv_to_semiring_nonpos.
Qed.

Lemma biinduction
  (P: Int → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, P n ↔ P (1 + n)) → ∀ n, P n.
Proof with auto.
  intros P0 Psuc. apply induction...
  firstorder.
  intros. apply Psuc. setoid_replace (1+(n-1)) with n by ring...
Qed.
End other_results.

Section default_order.
Context `{Integers Int}.
Add Ring Int2 : (rings.stdlib_ring_theory Int).

Global Instance int_precedes : Order Int | 9 :=  λ x y, ∃ z, y = x + naturals_to_semiring nat Int z.

Global Instance: Proper ((=) ==> (=) ==> iff) int_precedes.
Proof with assumption.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   rewrite <-E1, <-E2...
  rewrite E1, E2...
Qed.

Global Instance: RingOrder int_precedes.
Proof with trivial; try ring.
  repeat (split; try apply _).
      intros x. exists (0:nat). rewrite preserves_0...
     intros x y z [a A] [b B]. exists (a + b). rewrite preserves_plus, associativity, <-A, B...
    intros x y [a A] [b B].
    destruct (naturals.zero_sum a b) as [E1 E2].
     apply integers.naturals_to_integers_injective.
     rewrite preserves_plus, preserves_0.
     apply (left_cancellation (+) x). rewrite B at 2. rewrite A...
    rewrite A, B, E1, E2, preserves_0...
   intros x y [a A]. exists a. rewrite <-associativity, A...
  intros x [a A] y [b B]. exists (a * b). rewrite A, B, preserves_mult...
Qed.

Notation i_to_r := (integers_to_ring Int (SRpair nat)).

Global Instance: TotalOrder int_precedes.
Proof with trivial; try reflexivity.
  assert (∀ x y, i_to_r x ≤ i_to_r y → x ≤ y) as P.
   intros x y E. apply srorder_plus in E. 
   destruct E as [a [A B]].
   exists (pos a ∸ neg a). 
   apply (injective i_to_r).
   rewrite preserves_plus, B. clear B. apply sg_mor...
   change (a = (i_to_r ∘ naturals_to_semiring nat Int) (pos a ∸ neg a)).
   rewrite (naturals.to_semiring_unique_alt _ SRpair_inject).
   unfold equiv, SRpair_equiv, precedes, SRpair_order in *. simpl in *.
   rewrite right_identity, cut_minus.cut_minus_precedes...
   rewrite right_identity in A. rewrite left_identity in A...
  intros x y.
  destruct (total_order (i_to_r x) (i_to_r y)); intuition.
Qed.
End default_order.
