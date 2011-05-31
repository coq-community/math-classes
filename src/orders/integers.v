Require
  theory.integers theory.int_abs.
Require Import
  Ring workaround_tactics
  abstract_algebra interfaces.integers interfaces.naturals interfaces.additional_operations interfaces.orders
  natpair_integers orders.rings orders.naturals theory.rings.

Section integers_order.
Context `{Integers Int} `{Apart Int} `{!TrivialApart Int} `{!FullPseudoSemiRingOrder Intle Intlt}.

Lemma integers_le_plus (x y: Int) : x ≤ y ↔ ∃ z: nat, y = x + naturals_to_semiring nat Int z.
Proof.
  split; intros E.
   destruct (decompose_le E) as [z [Ez1 Ez2]].
    destruct (int_abs_sig Int nat z) as [k [Ek | Ek]].
     exists k. now rewrite Ek.
    exists (0 : nat).
    rewrite preserves_0.
    setoid_replace 0 with z; auto.
    apply (antisymmetry (≤)).
     assumption.
    rewrite <-Ek. apply flip_nonneg_opp. 
    apply to_semiring_nonneg.
   destruct E as [z E].
   apply compose_le with (naturals_to_semiring nat Int z).
    now apply to_semiring_nonneg.
   easy.
Qed.

Section another_ring.
  Context `{Ring R} `{Apart R} `{!FullPseudoSemiRingOrder (A:=R) Rle Rlt} {f : Int → R} `{!SemiRing_Morphism f}.

  Let f_preserves_nonneg x : 0 ≤ x → 0 ≤ f x.
  Proof.
    intros E.
    apply integers_le_plus in E.
    destruct E as [z E].
    apply compose_le with (naturals_to_semiring nat R z).
     apply to_semiring_nonneg.
    rewrite E.
    rewrite preserves_plus, preserves_0. 
    apply sm_proper.
    apply (naturals.to_semiring_twice _ _ _).
  Qed.
   
  Global Instance morphism_order_preserving: OrderPreserving f.
  Proof. apply preserving_preserves_nonneg. apply f_preserves_nonneg. Qed.

  (* Because each morphism [f] between two [Integers] implementations is injective, we
      obtain, by the following lemma, that the order on the integers is uniquely specified. *)
  Context `{!Injective f}.
  Let f_preserves_nonneg_back x : 0 ≤ f x → 0 ≤ x.
  Proof.
    intros E.
    destruct (int_abs_sig Int nat x) as [z [Ez | Ez]].
     rewrite <-Ez.
     apply to_semiring_nonneg.
    rewrite <-Ez in E |- *.
    setoid_replace z with (0 : nat).
     now rewrite preserves_0, opp_0.
    apply (injective (f ∘ naturals_to_semiring nat Int)).
    rewrite (naturals.to_semiring_unique _), preserves_0.
    rewrite preserves_opp, (naturals.to_semiring_twice _ _ (naturals_to_semiring nat R)) in E.
    apply (antisymmetry (≤)).
     now apply flip_nonpos_opp.
    apply to_semiring_nonneg.
  Qed.
  
  Global Instance: OrderEmbedding f.
  Proof.
    split. apply _.
    now apply reflecting_preserves_nonneg, f_preserves_nonneg_back.
  Qed.
End another_ring.
End integers_order.

Section other_results.
Context `{Integers Int} `{Apart Int} `{!TrivialApart Int} `{!FullPseudoSemiRingOrder Intle Intlt}.
Add Ring Int : (rings.stdlib_ring_theory Int).

Global Program Instance: ∀ x y: Int, Decision (x ≤ y) | 10 := λ x y,
  match decide (integers_to_ring _ (SRpair nat) x ≤ integers_to_ring _ (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation.
  now apply (order_reflecting (integers_to_ring _ (SRpair nat))). 
Qed.
Next Obligation.
  intros F. apply E.
  now apply (order_preserving _).
Qed.

Add Ring nat : (stdlib_semiring_theory nat).

Lemma le_iff_lt_plus_1 x y : x ≤ y ↔ x < y + 1.
Proof.
  split; intros E.
   apply pos_plus_le_lt_compat_r. now apply lt_0_1. easy.
  assert (∀ a b : SRpair nat, a < b + 1 → a ≤ b) as P.
   intros [ap an] [bp bn]. rewrite lt_iff_le_apart. intros [F1 F2].
   unfold le, SRpair_le in *. simpl in *.
   apply naturals.le_iff_lt_plus_1.
   apply lt_iff_le_apart. split.
    now ring_simplify in F1.
   intros F3. apply F2. 
   simpl. rewrite associativity, F3. ring.
  apply (order_reflecting (integers_to_ring _ (SRpair nat))), P.
  rewrite <-(preserves_1 (f:=integers_to_ring Int (SRpair nat))), <-preserves_plus.
  now apply (strictly_order_preserving (integers_to_ring _ (SRpair nat))).
Qed.

Lemma lt_iff_plus_1_le x y : x < y ↔ x + 1 ≤ y.
Proof.
  split; intros E.
   apply le_iff_lt_plus_1. now apply (strictly_order_preserving (+ 1)).
  apply (strictly_order_reflecting (+ 1)). now apply le_iff_lt_plus_1.
Qed.

Lemma induction
  (P: Int → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → (∀ n, n ≤ 0 → P n → P (n - 1)) → ∀ n, P n.
Proof with auto.
  intros P0 Psuc1 Psuc2 n.
  destruct (int_abs_sig Int nat n) as [m [E|E]].
   rewrite <-E. clear E. pattern m. 
   apply naturals.induction; clear m.
     solve_proper.
    now rewrite preserves_0.
   intros m E. 
   rewrite preserves_plus, preserves_1.
   apply Psuc1... apply to_semiring_nonneg.
  rewrite <-E. clear E. pattern m. 
  apply naturals.induction; clear m.
    intros ? ? E. rewrite E. tauto.
   rewrite preserves_0, opp_0...
  intros m E. 
  rewrite preserves_plus, preserves_1.
  rewrite opp_distr, commutativity.
  apply Psuc2...
  apply opp_to_semiring_nonpos.
Qed.

Lemma induction_nonneg
  (P: Int → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → ∀ n, 0 ≤ n → P n.
Proof with auto.
  intros P0 PS n. pattern n. apply induction; clear n...
   solve_proper.
  intros n E1 ? E2.
  destruct (is_ne_0 1).
  apply (antisymmetry (≤)).
   apply (order_reflecting ((n - 1) +)). ring_simplify. now transitivity 0.
  transitivity (n - 1)... apply (order_reflecting (1 +)). ring_simplify.
  transitivity 0... apply semirings.le_0_2.
Qed.

Global Instance biinduction: Biinduction Int.
Proof.
  intros P ? P0 Psuc. apply induction; trivial.
   firstorder.
  intros. apply Psuc. 
  now setoid_replace (1 + (n - 1)) with n by ring.
Qed.
End other_results.

Instance int_le `{Integers Z} : Le Z | 10 :=  λ x y, ∃ z, y = x + naturals_to_semiring nat Z z.
Instance int_lt  `{Integers Z} : Lt Z | 10 := dec_lt.

Section default_order.
Context `{Integers Int} `{Apart Int} `{!TrivialApart Int}.
Add Ring Int2 : (rings.stdlib_ring_theory Int).

Instance: Proper ((=) ==> (=) ==> iff) int_le.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   now rewrite <-E1, <-E2.
  now rewrite E1, E2.
Qed.

Instance: PartialOrder int_le.
Proof.
  repeat (split; try apply _).
    intros x. exists (0:nat). rewrite preserves_0. ring.
   intros x y z [a A] [b B]. exists (a + b). 
   now rewrite preserves_plus, associativity, <-A, B.
  intros x y [a A] [b B].
  destruct (naturals.zero_sum a b) as [E1 E2].
   apply (injective (naturals_to_semiring nat Int)).
   rewrite preserves_plus, preserves_0.
   apply (left_cancellation (+) x). 
   rewrite B at 2. rewrite A. ring.
  rewrite A, B, E1, E2, preserves_0. ring.
Qed.

Instance: SemiRingOrder int_le.
Proof.
  apply from_ring_order.
   repeat (split; try apply _).
   intros x y [a A]. exists a. rewrite A. ring.
  intros x y [a A] [b B]. exists (a * b). rewrite A, B, preserves_mult. ring.
Qed.

Notation i_to_r := (integers_to_ring Int (SRpair nat)).

Instance: TotalRelation int_le.
Proof.
  assert (∀ x y, i_to_r x ≤ i_to_r y → x ≤ y) as P.
   intros x y E.
   destruct (decompose_le E) as [a [A B]].
   exists (pos a ∸ neg a). 
   apply (injective i_to_r).
   rewrite preserves_plus, B. clear B. apply sm_proper.
   rewrite (naturals.to_semiring_twice _ _ SRpair_inject).
   unfold equiv, SRpair_equiv, le, SRpair_le in *. simpl in *.
   rewrite right_identity, cut_minus_le.
    reflexivity.
   now rewrite plus_0_l, plus_0_r in A.
  intros x y.
  now destruct (total (≤) (i_to_r x) (i_to_r y)); [left|right]; eapply P.
Qed.

Global Instance: FullPseudoSemiRingOrder int_le int_lt.
Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
