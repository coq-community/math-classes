Require
  theory.integers theory.int_abs.
Require Import
  Morphisms Ring Program Setoid workaround_tactics
  abstract_algebra interfaces.integers interfaces.naturals interfaces.additional_operations
  natpair_integers orders.semirings orders.naturals theory.rings.

Section integers_order.
Context `{Integers Int} `{!RingOrder o} `{!TotalOrder o}.

Lemma integers_precedes_plus (x y: Int) : x ≤ y ↔ ∃ z: nat, y = x + naturals_to_semiring nat Int z.
Proof with auto; try reflexivity.
  split; intros E.
   apply srorder_plus in E. destruct E as [z [Ez1 Ez2]].
    destruct (int_abs_sig Int nat z) as [k [Ek | Ek]].
     exists k. rewrite Ek...
    exists (0 : nat).
    rewrite preserves_0.
    rewrite Ez2. apply sg_mor...
    apply (antisymmetry (≤))...
    rewrite <-Ek. apply flip_nonneg_opp. apply to_semiring_nonneg.
   destruct E as [z E].
   apply srorder_plus. exists (naturals_to_semiring nat Int z). split...
   apply to_semiring_nonneg.
Qed.

Section another_ring.
  Context `{Ring R} {oR : Order R} `{!RingOrder oR} `{!TotalOrder oR}
     {f : Int → R} `{!SemiRing_Morphism f}.

  Let f_preserves_nonneg x : 0 ≤ x → 0 ≤ f x.
  Proof with try reflexivity.
    intros E.
    apply integers_precedes_plus in E.
    destruct E as [z E].
    apply srorder_plus. exists (naturals_to_semiring nat R z). split...
     apply to_semiring_nonneg.
    rewrite E.
    rewrite preserves_plus, preserves_0. apply sg_mor...
    change ((f ∘ naturals_to_semiring nat Int) z = naturals_to_semiring nat R z).
    apply (naturals.to_semiring_unique _).
  Qed.
   
  Global Instance morphism_order_preserving: OrderPreserving f.
  Proof. apply preserving_preserves_nonneg. apply f_preserves_nonneg. Qed.

  (* Because each morphism [f] between two [Integers] implementations is injective, we
      obtain, by the following lemma, that the order on the integers is uniquely specified. *)
  Context `{!Injective f}.
  Let f_preserves_nonneg_back x : 0 ≤ f x → 0 ≤ x.
  Proof.
    intros E.
    rewrite (integers.to_ring_unique f) in E.
    destruct (int_abs_sig Int nat x) as [z [Ez | Ez]].
     rewrite <-Ez.
     apply to_semiring_nonneg. 
    rewrite <-Ez in E |- *.
    setoid_replace z with (0 : nat).
     now rewrite preserves_0, opp_0.
    apply (injective (f ∘ naturals_to_semiring nat Int)).
    rewrite (naturals.to_semiring_unique _).
    unfold compose. rewrite 2!preserves_0.
    rewrite preserves_opp in E.
    apply (antisymmetry (≤)).
     rewrite <-(naturals.to_semiring_unique (integers_to_ring Int R ∘ naturals_to_semiring nat Int)).
     now apply flip_nonpos_opp.
    apply to_semiring_nonneg.
  Qed.
  
  Global Instance: OrderEmbedding f.
  Proof.
    split. apply _.
    apply preserving_back_preserves_nonneg. apply f_preserves_nonneg_back.
  Qed.
End another_ring.
End integers_order.

Section other_results.
Context `{Integers Int} `{!RingOrder o} `{!TotalOrder o} .
Add Ring Int : (rings.stdlib_ring_theory Int).

Global Program Instance: ∀ x y: Int, Decision (x ≤ y) | 10 := λ x y,
  match decide (integers_to_ring _ (SRpair nat) x ≤ integers_to_ring _ (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. 
  now apply (order_preserving_back (integers_to_ring _ (SRpair nat))). 
Qed.
Next Obligation.
  intros F. apply E.
  now apply (order_preserving _).
Qed.

Add Ring nat : (stdlib_semiring_theory nat).

Lemma precedes_sprecedes x y : x ≤ y ↔ x < y + 1.
Proof.
  split; intros E.
   apply pos_plus_scompat_r. easy. apply sprecedes_0_1.
  assert (∀ a b : SRpair nat, a < b + 1 → a ≤ b) as P.
   intros a b [F1 F2].
   unfold precedes, SRpair_order in *. simpl in *.
   apply naturals.precedes_sprecedes.
   split.
    now ring_simplify in F1.
   intros F3. apply F2. 
   unfold ring_plus, SRpair_plus, equiv, SRpair_equiv. simpl.
   rewrite associativity, F3. ring.
  apply (order_preserving_back (integers_to_ring _ (SRpair nat))), P.
  rewrite <-(preserves_1 (f:=integers_to_ring Int (SRpair nat))), <-preserves_plus.
  now apply (strictly_order_preserving (integers_to_ring _ (SRpair nat))).
Qed.

Lemma precedes_sprecedes_alt x y : x < y ↔ x + 1 ≤ y.
Proof.
  split; intros E.
   apply precedes_sprecedes. now apply (strictly_order_preserving (+ 1)).
  apply (strictly_order_preserving_back (+ 1)). now apply precedes_sprecedes.
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
  destruct (ne_0 1).
  apply (antisymmetry (≤)).
   apply (order_preserving_back ((n - 1) +)). ring_simplify. now transitivity 0.
  transitivity (n - 1)... apply (order_preserving_back (1 +)). ring_simplify.
  transitivity 0... apply semirings.precedes_0_2.
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

Instance int_precedes `{Integers Z} : Order Z | 10 :=  λ x y, ∃ z, y = x + naturals_to_semiring nat Z z.

Section default_order.
Context `{Integers Int}.
Add Ring Int2 : (rings.stdlib_ring_theory Int).

Global Instance: Proper ((=) ==> (=) ==> iff) int_precedes.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  split; intros [z p]; exists z.
   now rewrite <-E1, <-E2.
  now rewrite E1, E2.
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
   rewrite right_identity. posed_rewrite cut_minus_precedes...
   rewrite right_identity in A. rewrite left_identity in A...
  intros x y.
  destruct (total_order (i_to_r x) (i_to_r y)); intuition.
Qed.
End default_order.
