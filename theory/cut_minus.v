Require
  MathClasses.orders.semirings.
Require Import
  Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.interfaces.additional_operations
  MathClasses.interfaces.orders MathClasses.orders.minmax.

(* * Properties of Cut off Minus *)
Section cut_minus_properties.
  Context `{FullPseudoSemiRingOrder R} `{!TrivialApart R}
    `{∀ x y, Decision (x = y)} `{!CutMinusSpec R cm}.

  Local Existing Instance pseudo_srorder_semiring.

  Add Ring SR: (rings.stdlib_semiring_theory R).
  Hint Resolve (@orders.le_flip R _ _).

  Global Instance cut_minus_proper: Proper ((=) ==> (=) ==> (=)) cut_minus | 1.
  Proof.
    intros x₁ x₂ E y₁ y₂ F.
    destruct (total (≤) x₂ y₂).
     rewrite cut_minus_0, cut_minus_0; try easy. now rewrite E, F.
    apply (right_cancellation (+) y₂).
    rewrite cut_minus_le by easy.
    rewrite <-E, <-F. apply cut_minus_le. now rewrite E, F.
  Qed.

  Global Instance cut_minus_mor_1: ∀ x : R, Setoid_Morphism (x ∸) | 0.
  Proof. split; try apply _. Qed.

  Global Instance cut_minus_mor_2: ∀ x : R, Setoid_Morphism (∸ x) | 0.
  Proof. split; try apply _. solve_proper. Qed.

  Hint Resolve (cut_minus_0).
  Hint Resolve (cut_minus_le).

  Lemma cut_minus_diag x : x ∸ x = 0.
  Proof. now apply cut_minus_0. Qed.

  Lemma cut_minus_nonneg_0_r x : 0 ≤ x → x ∸ 0 = x.
  Proof. intros E. rewrite <-(rings.plus_0_r (x ∸ 0)). auto. Qed.

  Lemma cut_minus_0_l x : 0 ≤ x → 0 ∸ x = 0.
  Proof. auto. Qed.

  Lemma cut_minus_nonpos_0_r x : x ≤ 0 → x ∸ 0 = 0.
  Proof. auto. Qed.

  Lemma cut_minus_nonneg x y : 0 ≤ x ∸ y.
  Proof.
    destruct (total (≤) x y) as [E|E].
     apply orders.eq_le. symmetry. now auto.
    apply (order_reflecting (+ y)).
    now rewrite cut_minus_le; ring_simplify.
  Qed.

  Lemma cut_minus_le_r x y : y ≤ x → x ∸ y + y = x.
  Proof cut_minus_le x y.

  Lemma cut_minus_le_l x y : y ≤ x → y + (x ∸ y) = x.
  Proof. rewrite commutativity. now apply cut_minus_le. Qed.

  Lemma cut_minus_le_trans x y z : y ≤ x → z ≤ y → (x ∸ y) + (y ∸ z) = x ∸ z.
  Proof.
    intros. apply (right_cancellation (+) z).
    rewrite <-associativity, !cut_minus_le; try easy.
    now transitivity y.
  Qed.
  Hint Resolve cut_minus_le_trans.

  (* We need y₁ ≤ x₁ ∧ y₂ ≤ x₂, e.g. (5 ∸ 6) + (5 ∸0) = 0 + 5 = 5, whereas (10 ∸ 6) = 4 *)
  (* This example illustrates that y₁ + y₂ ≤ x₁ + x₂ does not work either. *)
  Lemma cut_minus_plus_distr x₁ x₂ y₁ y₂ :
     y₁ ≤ x₁ → y₂ ≤ x₂ → (x₁ ∸ y₁) + (x₂ ∸ y₂) = (x₁ + x₂) ∸ (y₁ + y₂).
  Proof.
    intros E F. apply (right_cancellation (+) (y₁ + y₂)).
    rewrite cut_minus_le.
     setoid_replace (x₁ ∸ y₁ + (x₂ ∸ y₂) + (y₁ + y₂)) with (((x₁ ∸ y₁) + y₁) + ((x₂ ∸ y₂) + y₂)) by ring.
     now rewrite !cut_minus_le.
    now apply semirings.plus_le_compat.
  Qed.

  (* We need 0 ≤ x, e.g. (-1) * (2 ∸ 1) = -1, whereas (-2) ∸ (-1) = 0 *)
  Lemma cut_minus_mult_distr_l x y z : 0 ≤ x →  x * (y ∸ z) = x * y ∸ x * z.
  Proof.
    intros E. destruct (total (≤) y z).
     rewrite !cut_minus_0; trivial.
      ring.
     now apply (maps.order_preserving_nonneg (.*.) x).
    apply (right_cancellation (+) (x * z)).
    rewrite <-distribute_l, !cut_minus_le; try easy.
    now apply (maps.order_preserving_nonneg (.*.) x).
  Qed.

  Lemma cut_minus_mult_distr_r x y z : 0 ≤ x →  (y ∸ z) * x = y * x ∸ z * x.
  Proof.
    intros E. rewrite 3!(commutativity _ x).
    now apply cut_minus_mult_distr_l.
  Qed.

  Lemma cut_minus_plus_rev_l x y z : y ∸ z = (x + y) ∸ (x + z).
  Proof.
    destruct (total (≤) y z).
     rewrite !cut_minus_0; intuition.
    apply (right_cancellation (+) (x + z)).
    transitivity ((y ∸ z + z) + x); try ring.
    rewrite !cut_minus_le; try easy; try ring.
    now apply (order_preserving (x +)).
  Qed.

  Lemma cut_minus_plus_rev_r x y z : y ∸ z = (y + x) ∸ (z + x).
  Proof. rewrite !(commutativity _ x). now apply cut_minus_plus_rev_l. Qed.

  (* We need 0 ≤ z, e.g. 2 ∸ (5 - 5) = 2, whereas (2 ∸ 5) ∸ (-5) = 0 ∸ (-5) = 5 *)
  Lemma cut_minus_plus_r x y z : 0 ≤ z → x ∸ (y + z) = (x ∸ y) ∸ z.
  Proof.
    intros E. case (total (≤) x y); intros Exy.
     rewrite (cut_minus_0 x y) by easy.
     rewrite cut_minus_0_l, cut_minus_0; try easy.
     now apply semirings.plus_le_compat_r.
    rewrite (cut_minus_plus_rev_r y (x ∸ y) z).
    now rewrite cut_minus_le, commutativity.
  Qed.

  Lemma cut_minus_plus_l x y z : 0 ≤ y → x ∸ (y + z) = (x ∸ z) ∸ y.
  Proof. rewrite commutativity. now apply cut_minus_plus_r. Qed.

  Lemma cut_minus_plus_toggle1 x y z : x ≤ y → z ≤ y → (y ∸ x) + (x ∸ z) = (y ∸ z) + (z ∸ x).
  Proof.
    intros. destruct (total (≤) x z).
     rewrite (cut_minus_0 x z), cut_minus_le_trans by easy. ring.
    rewrite (cut_minus_0 z x), cut_minus_le_trans by easy. ring.
  Qed.

  Lemma cut_minus_plus_toggle2 x y z : y ≤ x → y ≤ z →  (x ∸ z) + (z ∸ y) = (z ∸ x) + (x ∸ y).
  Proof.
    intros. destruct (total (≤) x z).
     rewrite (cut_minus_0 x z), cut_minus_le_trans by easy. ring.
    rewrite (cut_minus_0 z x) by easy. ring_simplify. now auto.
  Qed.

  Lemma cut_minus_plus_toggle3 x₁ x₂ y₁ y₂ : x₁ ≤ y₁ → y₂ ≤ x₂
     → (y₁ ∸ x₁) + ((x₁ + x₂) ∸ (y₁ + y₂)) = (x₂ ∸ y₂) + ((y₁ + y₂) ∸ (x₁ + x₂)).
  Proof.
    intros. destruct (total (≤) (x₁ + x₂) (y₁ + y₂)).
     rewrite (cut_minus_0 (x₁ + x₂) (y₁ + y₂)) by easy.
     rewrite cut_minus_plus_distr by easy.
     setoid_replace (x₂ + (y₁ + y₂)) with (y₁ + (x₂ + y₂)) by ring.
     setoid_replace (y₂ + (x₁ + x₂)) with (x₁ + (x₂ + y₂)) by ring.
     rewrite <-cut_minus_plus_rev_r. ring.
    rewrite (cut_minus_0 (y₁ + y₂) (x₁ + x₂)) by easy.
    rewrite cut_minus_plus_distr by easy.
    setoid_replace (y₁ + (x₁ + x₂)) with (x₂ + (x₁ + y₁)) by ring.
    setoid_replace (x₁ + (y₁ + y₂)) with (y₂ + (x₁ + y₁)) by ring.
    rewrite <-cut_minus_plus_rev_r. ring.
  Qed.

  Lemma cut_minus_0_plus_toggle x : x + (0 ∸ x) = x ∸ 0.
  Proof.
    destruct (total (≤) 0 x).
     rewrite (cut_minus_0 0 x), (cut_minus_nonneg_0_r x) by easy. ring.
    rewrite (cut_minus_0 x 0), commutativity; auto.
  Qed.

  Lemma cut_minus_0_le x y : x ≤ y → (y ∸ x) + (x ∸ 0) + (0 ∸ y) = (y ∸ 0) + (0 ∸ x).
  Proof.
    intros. rewrite <-!cut_minus_0_plus_toggle.
    apply (right_cancellation (+) x).
    setoid_replace (y ∸ x + (x + (0 ∸ x)) + (0 ∸ y) + x) with ((y ∸ x + x) + (x + (0 ∸ x)) + (0 ∸ y)) by ring.
    rewrite (cut_minus_le y x) by easy. ring.
  Qed.

  (* * Properties of min and minus *)
  Section min.
  Context `{∀ x y : R, Decision (x ≤ y)}.

  Lemma cut_minus_min1 x y z : x ∸ (y ⊓ z) = x ∸ y + ((x ⊓ y) ∸ z).
  Proof with eauto; try ring.
    unfold meet, min, sort.
    case (decide_rel (≤) x y); case (decide_rel (≤) y z); intros F G; simpl.
       rewrite (cut_minus_0 x z)...
      rewrite (cut_minus_0 x y)...
     rewrite (cut_minus_0 y z)...
    symmetry...
  Qed.

  Lemma cut_minus_min2 x y z : y ∸ z + ((y ⊓ z) ∸ x) = y ∸ x + ((x ⊓ y) ∸ z).
  Proof.
    rewrite <-cut_minus_min1.
    rewrite (commutativity x y), <-cut_minus_min1.
    now rewrite commutativity.
  Qed.

  Lemma cut_minus_min3 x y z : (x + (y ⊓ z)) ∸ ((x + y) ⊓ (x + z)) = ((x + y) ⊓ (x + z)) ∸ (x + (y ⊓ z)).
  Proof with auto; try reflexivity.
    destruct (total (≤) y z) as [G1|G1].
     rewrite (lattices.meet_l y z), (lattices.meet_l (x + y) (x + z))...
    rewrite (lattices.meet_r y z), (lattices.meet_r (x + y) (x + z))...
  Qed.
  End min.

  (* The relation to ring minus *)
  Context `{Negate R} `{!Ring R}.
  Add Ring R: (rings.stdlib_ring_theory R).

  Lemma cut_minus_ring_minus (x y : R) : y ≤ x → x ∸ y = x - y.
  Proof. intros. apply (right_cancellation (+) y). ring_simplify. now auto. Qed.

  Lemma cut_minus_negate (x : R) : x ≤ 0 → 0 ∸ x = -x.
  Proof. intros. now rewrite <-(rings.plus_0_l (-x)), cut_minus_ring_minus. Qed.
End cut_minus_properties.

(* * Default implementation for Rings *)
Section cut_minus_default.
  Context `{Ring R} `{!SemiRingOrder o} `{∀ x y : R, Decision (x ≤ y)}.

  Global Instance default_cut_minus: CutMinus R | 10 := λ x y, if decide_rel (≤) x y then 0 else x - y.

  Add Ring R2: (rings.stdlib_ring_theory R).

  Global Instance: CutMinusSpec R default_cut_minus.
  Proof.
    split; unfold cut_minus, default_cut_minus; intros x y ?.
     case (decide_rel (≤) x y); intros.
      ring_simplify. now apply (antisymmetry (≤)).
     ring.
    now case (decide_rel (≤) x y).
  Qed.
End cut_minus_default.

Typeclasses Opaque default_cut_minus.

Section order_preserving.
  Context `{FullPseudoSemiRingOrder A} `{!TrivialApart A} `{!CutMinusSpec A cmA} `{∀ x y : A, Decision (x = y)}
   `{FullPseudoSemiRingOrder B} `{!TrivialApart B} `{!CutMinusSpec B cmB} `{∀ x y : B, Decision (x = y)}
     {f : A → B} `{!OrderPreserving f} `{!SemiRing_Morphism f}.

  Local Existing Instance pseudo_srorder_semiring.

  Lemma preserves_cut_minus x y : f (x ∸ y) = f x ∸ f y.
  Proof.
    destruct (total (≤) x y) as [E|E].
     rewrite (cut_minus_0 x y E), (cut_minus_0 (f x) (f y)).
     apply rings.preserves_0.
     now apply (order_preserving _).
    apply (left_cancellation (+) (f y)). rewrite 2!(commutativity (f y)).
    rewrite <-rings.preserves_plus.
    rewrite (cut_minus_le x y E), (cut_minus_le (f x) (f y)).
     reflexivity.
    now apply (order_preserving _).
  Qed.
End order_preserving.
