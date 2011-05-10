Require
  orders.semirings.
Require Import 
  Ring
  abstract_algebra interfaces.additional_operations
  interfaces.orders orders.minmax.

(* * Properties of Cut off Minus *)
Section cut_minus_properties.
  Context `{SemiRing R} `{Apart R} `{!FullPseudoSemiRingOrder Rle Rlt} `{!TrivialApart R} 
    `{∀ x y, Decision (x = y)} `{!CutMinusSpec R cm}.

  Add Ring SR: (rings.stdlib_semiring_theory R).
  Hint Resolve (@orders.le_flip R _ _).

  Global Instance cut_minus_proper: Proper ((=) ==> (=) ==> (=)) cut_minus | 1.
  Proof.
    intros x1 x2 E y1 y2 F.
    destruct (total (≤) x2 y2).
     rewrite cut_minus_0, cut_minus_0; try easy. now rewrite E, F.
    apply (right_cancellation (+) y2).
    rewrite cut_minus_le; try easy.
    rewrite <-E, <-F. apply cut_minus_le. now rewrite E, F.
  Qed.

  Global Instance cut_minus_mor_1: ∀ x : R, Setoid_Morphism (x ∸) | 0.
  Proof. split; try apply _. Qed.

  Global Instance cut_minus_mor_2: ∀ x : R, Setoid_Morphism (∸ x) | 0.
  Proof. split; try apply _. solve_proper. Qed.

  Hint Resolve cut_minus_0.
  Hint Resolve cut_minus_le.

  Lemma cut_minus_diag x : x ∸ x = 0.
  Proof. 
    now apply cut_minus_0.
  Qed.

  Lemma cut_minus_rightidentity x : 0 ≤ x → x ∸ 0 = x.
  Proof.
    intros E.
    rewrite <-(rings.plus_0_r (x ∸ 0)). auto.
  Qed.

  Lemma cut_minus_leftabsorb x : 0 ≤ x → 0 ∸ x = 0.
  Proof. auto. Qed.

  Lemma cut_minus_rightabsorb x : x ≤ 0 → x ∸ 0 = 0.
  Proof. auto. Qed.

  Lemma cut_minus_nonneg x y : 0 ≤ x ∸ y.
  Proof with auto.
    destruct (total (≤) x y) as [E|E].
     apply orders.eq_le. symmetry...
    apply (order_reflecting (+ y))...
    rewrite cut_minus_le; ring_simplify...
  Qed.

  Lemma cut_minus_le_trans x y z : y ≤ x → z ≤ y → (x ∸ y) + (y ∸ z) = x ∸ z.
  Proof with auto; try reflexivity. 
    intros. 
    apply (right_cancellation (+) z)...
    rewrite <-associativity. 
    rewrite !cut_minus_le... 
    transitivity y...
  Qed.
  Hint Resolve cut_minus_le_trans.

  Lemma cut_minus_plus_distr x1 x2 y1 y2 : 
     y1 ≤ x1 → y2 ≤ x2 → (x1 ∸ y1) + (x2 ∸ y2) = (x1 + x2) ∸ (y1 + y2).
  Proof with auto.
    intros E F.
    apply (right_cancellation (+) (y1 + y2))...
    rewrite cut_minus_le.
     setoid_replace (x1 ∸ y1 + (x2 ∸ y2) + (y1 + y2)) with (((x1 ∸ y1) + y1) + ((x2 ∸ y2) + y2)) by ring.
     rewrite !cut_minus_le... reflexivity. 
    apply semirings.plus_le_compat...
  Qed.

  Lemma cut_minus_mult_distr_l (x y z : R) : 0 ≤ x →  x * (y ∸ z) = x * y ∸ x * z.
  Proof.
    intros E.
    destruct (total (≤) y z).
     rewrite ?cut_minus_0; trivial.
      ring.
     now apply (maps.order_preserving_nonneg (.*.) x).
    apply (right_cancellation (+) (x * z)). 
    rewrite <-distribute_l.
    rewrite !cut_minus_le; try easy.
    now apply (maps.order_preserving_nonneg (.*.) x).
  Qed.

  Lemma cut_minus_mult_distr_r (x y z : R) : 0 ≤ x →  (y ∸ z) * x = y * x ∸ z * x.
  Proof.
    intros E.
    rewrite 3!(commutativity _ x).
    now apply cut_minus_mult_distr_l.
  Qed.

  Lemma cut_minus_plus_l_rev x y z : y ∸ z = (x + y) ∸ (x + z).
  Proof with auto; try reflexivity.
    destruct (total (≤) y z) as [E|E].
     rewrite ?cut_minus_0... 
     apply (order_preserving (x +))...
    apply (right_cancellation (+) (x + z))...
    setoid_replace (y ∸ z + (x + z)) with ((y ∸ z + z) + x) by ring.
    rewrite !cut_minus_le... 
     apply commutativity.
    apply (order_preserving (x +))...
  Qed.

  Lemma cut_minus_plus_r_rev x y z : y ∸ z = (y + x) ∸ (z + x).
  Proof.
    rewrite (commutativity y x), (commutativity z x).
    apply cut_minus_plus_l_rev.
  Qed.

  Lemma cut_minus_plus_toggle1 x y z : x ≤ y → z ≤ y → (y ∸ x) + (x ∸ z) = (y ∸ z) + (z ∸ x).
  Proof with auto.
    intros. destruct (total (≤) x z).
    rewrite (cut_minus_0 x z), cut_minus_le_trans... ring.
    rewrite (cut_minus_0 z x), cut_minus_le_trans... ring.
  Qed.

  Lemma cut_minus_plus_toggle2 x y z : y ≤ x → y ≤ z →  (x ∸ z) + (z ∸ y) = (z ∸ x) + (x ∸ y).
  Proof with auto.
    intros. destruct (total (≤) x z).
    rewrite (cut_minus_0 x z), cut_minus_le_trans... ring.
    rewrite (cut_minus_0 z x)... ring_simplify...
  Qed.

  Lemma cut_minus_plus_toggle3 x1 x2 y1 y2 : x1 ≤ y1 → y2 ≤ x2 
     → (y1 ∸ x1) + ((x1 + x2) ∸ (y1 + y2)) = (x2 ∸ y2) + ((y1 + y2) ∸ (x1 + x2)).
  Proof with auto.
    intros E F.
    destruct (total (≤) (x1 + x2) (y1 + y2)).
     rewrite (cut_minus_0 (x1 + x2) (y1 + y2))...
     rewrite cut_minus_plus_distr...
     setoid_replace (x2 + (y1 + y2)) with (y1 + (x2 + y2)) by ring.
     setoid_replace (y2 + (x1 + x2)) with (x1 + (x2 + y2)) by ring.
     rewrite <-cut_minus_plus_r_rev. ring.
    rewrite (cut_minus_0 (y1 + y2) (x1 + x2))...
    rewrite cut_minus_plus_distr...
    setoid_replace (y1 + (x1 + x2)) with (x2 + (x1 + y1)) by ring.
    setoid_replace (x1 + (y1 + y2)) with (y2 + (x1 + y1)) by ring.
    rewrite <-cut_minus_plus_r_rev. ring.
  Qed.

  Lemma cut_minus_zero_plus_toggle x : x + (0 ∸ x) = x ∸ 0.
  Proof with auto.
    destruct (total (≤) 0 x) as [E|E].
     rewrite (cut_minus_0 0 x), (cut_minus_rightidentity x)... ring.
    rewrite (cut_minus_0 x 0), commutativity...
  Qed.

  Lemma cut_minus_zeros_le x y : x ≤ y → (y ∸ x) + (x ∸ 0) + (0 ∸ y) = (y ∸ 0) + (0 ∸ x).
  Proof with auto; try reflexivity.
    intros E.
    rewrite <-?cut_minus_zero_plus_toggle.
    apply (right_cancellation (+) x)...
    setoid_replace (y ∸ x + (x + (0 ∸ x)) + (0 ∸ y) + x) with ((y ∸ x + x) + (x + (0 ∸ x)) + (0 ∸ y)) by ring.
    rewrite (cut_minus_le y x)... ring.
  Qed.

  (* * Properties of min and minus *)
  Section min.
  Context `{∀ (x y : R), Decision (x ≤ y)}.
  Lemma cut_minus_min1 x y z : x ∸ min y z = x ∸ y + (min x y ∸ z). 
  Proof with eauto; try ring.
    unfold min, sort.
    case (decide_rel (≤) x y); case (decide_rel (≤) y z); intros F G; simpl.
       rewrite (cut_minus_0 x z)... transitivity y...
      rewrite (cut_minus_0 x y)...
     rewrite (cut_minus_0 y z)...
    symmetry...
  Qed.
  
  Lemma cut_minus_min2 x y z : y ∸ z + (min y z ∸ x) = y ∸ x + (min x y ∸ z).
  Proof.
    rewrite <-cut_minus_min1. 
    rewrite (commutativity x y), <-cut_minus_min1.
    now rewrite commutativity.
  Qed.

  Lemma cut_minus_min3 x y z : (x + min y z) ∸ min (x + y) (x + z) = min (x + y) (x + z) ∸ (x + min y z).
  Proof with auto; try reflexivity.
    destruct (total (≤) y z) as [G1|G1].
     rewrite (min_l y z), (min_l (x + y) (x + z))...
     apply (order_preserving (x +))...
    rewrite (min_r y z), (min_r (x + y) (x + z))...
    apply (order_preserving (x +))...
  Qed.
  End min.

  (* The relation to ring minus *)
  Context `{GroupInv R} `{!Ring R}.
  Add Ring R: (rings.stdlib_ring_theory R).

  Lemma cut_minus_ring_minus (x y : R) : y ≤ x → x ∸ y = x - y.
  Proof with auto.
    intros E.
    apply (right_cancellation (+) y)... ring_simplify...
  Qed.

  Lemma cut_minus_opp (x : R) : x ≤ 0 → 0 ∸ x = -x.
  Proof with auto.
    intros E. rewrite <-(rings.plus_0_l (-x)). 
    rewrite cut_minus_ring_minus... ring.
  Qed.
End cut_minus_properties.

(* * Default implementation for Rings *)
Section cut_minus_default.
  Context `{Ring R} `{!SemiRingOrder o} `{∀ (x y : R), Decision (x ≤ y)}.

  Global Instance default_cut_minus: CutMinus R | 10 := λ x y, if decide_rel (≤) x y then 0 else x - y.

  Add Ring R2: (rings.stdlib_ring_theory R).
  
  Global Instance: CutMinusSpec R default_cut_minus.
  Proof.
    split; unfold cut_minus, default_cut_minus; intros x y ?.
     case (decide_rel (≤) x y); intros E.
      ring_simplify. now apply (antisymmetry (≤)).
     ring.
    case (decide_rel (≤) x y); easy.
  Qed.
End cut_minus_default.

Typeclasses Opaque default_cut_minus.

Section order_preserving.
  Context `{SemiRing A} `{Apart A} `{!TrivialApart A} 
   `{!FullPseudoSemiRingOrder (A:=A) Ale Alt} `{!CutMinusSpec A cmA} `{∀ (x y : A), Decision (x = y)}
   `{SemiRing B} `{Apart B} `{!TrivialApart B} 
   `{!FullPseudoSemiRingOrder (A:=B) Ble Blt} `{!CutMinusSpec B cmB} `{∀ (x y : B), Decision (x = y)}
     {f : A → B} `{!OrderPreserving f} `{!SemiRing_Morphism f}.
  
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
