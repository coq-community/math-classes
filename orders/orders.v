Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders MathClasses.theory.strong_setoids.

Lemma le_flip `{Le A} `{!TotalRelation (≤)} x y : ¬y ≤ x → x ≤ y.
Proof. firstorder. Qed.

Section partial_order.
  Context `{PartialOrder A}.

  Instance: Setoid A := po_setoid.

  Lemma eq_le x y : x = y → x ≤ y.
  Proof. intros E. now rewrite E. Qed.

  Lemma eq_le_flip x y : x = y → y ≤ x.
  Proof. intros E. now rewrite E. Qed.

  Lemma not_le_ne x y : ¬x ≤ y → x ≠ y.
  Proof. intros E1 E2. destruct E1. now rewrite E2. Qed.

  Lemma eq_iff_le x y : x = y ↔ x ≤ y ∧ y ≤ x.
  Proof. split; intros E. now rewrite E. now apply (antisymmetry (≤) x y). Qed.
End partial_order.

Section strict_order.
  Context `{StrictSetoidOrder A}.

  Instance: Setoid A := strict_setoid_order_setoid.

  Lemma lt_flip x y : x < y → ¬y < x.
  Proof.
    intros E1 E2.
    apply (irreflexivity (<) x).
    now transitivity y.
  Qed.

  Lemma lt_antisym x y : ¬(x < y < x).
  Proof.
    intros [E1 E2].
    now destruct (lt_flip x y).
  Qed.

  Lemma lt_ne x y : x < y → x ≠ y.
  Proof. unfold PropHolds. intros E1 E2. rewrite E2 in E1. now destruct (irreflexivity (<) y). Qed.

  Lemma lt_ne_flip x y : x < y → y ≠ x.
  Proof. intro. now apply not_symmetry, lt_ne. Qed.

  Lemma eq_not_lt x y : x = y → ¬x < y.
  Proof. intros E. rewrite E. now apply (irreflexivity (<)). Qed.
End strict_order.

Section pseudo_order.
  Context `{PseudoOrder A}.

  Instance: StrongSetoid A := pseudo_order_setoid.

  Lemma apart_total_lt x y : x ≶ y → x < y ∨ y < x.
  Proof. intros. now apply apart_iff_total_lt. Qed.

  Lemma pseudo_order_lt_apart x y : x < y → x ≶ y.
  Proof. intros. apply apart_iff_total_lt. tauto. Qed.

  Lemma pseudo_order_lt_apart_flip x y : x < y → y ≶ x.
  Proof. intros. apply apart_iff_total_lt. tauto. Qed.

  Lemma not_lt_apart_lt_flip x y : ¬x < y → x ≶ y → y < x.
  Proof. rewrite apart_iff_total_lt. intuition. Qed.

  Lemma pseudo_order_cotrans_twice x₁ y₁ x₂ y₂ : x₁ < y₁ → x₂ < y₂ ∨ x₁ < x₂ ∨ y₂ < y₁.
  Proof.
    intros E1.
    destruct (cotransitive E1 x₂) as [E2|E2]; try tauto.
    destruct (cotransitive E2 y₂); try tauto.
  Qed.

  Lemma pseudo_order_lt_ext x₁ y₁ x₂ y₂ : x₁ < y₁ → x₂ < y₂ ∨ x₁ ≶ x₂ ∨ y₂ ≶ y₁.
  Proof.
    intros E.
    destruct (pseudo_order_cotrans_twice x₁ y₁ x₂ y₂ E) as [?|[?|?]]; auto using pseudo_order_lt_apart.
  Qed.

  Instance: Proper ((=) ==> (=) ==> iff) (<).
  Proof.
    assert (∀ x₁ y₁ x₂ y₂, x₁ < y₁ → x₁ = x₂ → y₁ = y₂ → x₂ < y₂) as P.
     intros x₁ y₁ x₂ y₂ E Ex Ey.
     destruct (pseudo_order_lt_ext x₁ y₁ x₂ y₂ E) as [?|[?|?]]; try tauto.
      contradict Ex. now apply apart_ne.
     contradict Ey. now apply not_symmetry, apart_ne.
    split; intros; eapply P; eauto; now symmetry.
  Qed.

  Global Instance: StrictSetoidOrder (_ : Lt A).
  Proof.
    repeat (split; try apply _).
     intros x E.
     destruct (pseudo_order_antisym x x); tauto.
    intros x y z E1 E2.
    destruct (cotransitive E1 z); trivial.
    destruct (pseudo_order_antisym y z); tauto.
  Qed.

  Global Instance: Transitive (complement (<)).
  Proof.
    intros x y z.
    intros E1 E2 E3.
    destruct (cotransitive E3 y); contradiction.
  Qed.

  Global Instance: AntiSymmetric (complement (<)).
  Proof. intros x y. rewrite <-tight_apart, apart_iff_total_lt. intuition. Qed.

  Lemma ne_total_lt `{!TrivialApart A} x y : x ≠ y → x < y ∨ y < x.
  Proof. rewrite <-trivial_apart. now apply apart_total_lt. Qed.

  Global Instance lt_trichotomy `{!TrivialApart A} `{∀ x y, Decision (x = y)} : Trichotomy (<).
  Proof.
    intros x y.
    destruct (decide (x = y)) as [?|?]; try tauto.
    destruct (ne_total_lt x y); tauto.
  Qed.
End pseudo_order.

Section full_partial_order.
  Context `{FullPartialOrder A}.

  Instance: StrongSetoid A := strict_po_setoid.

  (* Duplicate of strong_setoids.apart_ne. This is useful because a
    StrongSetoid is not defined as a substructure of a FullPartialOrder *)
  Instance strict_po_apart_ne x y : PropHolds (x ≶ y) → PropHolds (x ≠ y).
  Proof. intros. apply _. Qed.

  Global Instance apart_proper: Proper ((=) ==> (=) ==> iff) (≶).
  Proof. apply _. Qed.

  Global Instance: StrictSetoidOrder (<).
  Proof.
    split; try apply _.
     intros x1 y1 E1 x2 y2 E2.
     rewrite ?lt_iff_le_apart.
     now rewrite E1, E2.
    split; try apply _.
    intros x. red. rewrite lt_iff_le_apart. intros [_ ?].
    now destruct (irreflexivity (≶) x).
  Qed.

  Lemma lt_le x y : PropHolds (x < y) → PropHolds (x ≤ y).
  Proof. intro. now apply lt_iff_le_apart. Qed.

  Lemma not_le_not_lt x y : ¬x ≤ y → ¬x < y.
  Proof. firstorder using lt_le. Qed.

  Lemma lt_apart x y : x < y → x ≶ y.
  Proof. intro. now apply lt_iff_le_apart. Qed.

  Lemma lt_apart_flip x y : x < y → y ≶ x.
  Proof. intro. now apply symmetry, lt_iff_le_apart. Qed.

  Lemma le_not_lt_flip x y : y ≤ x → ¬x < y.
  Proof.
    rewrite lt_iff_le_apart.
    intros E1 [E2a E2b].
    contradict E2b. setoid_replace x with y.
     now apply (irreflexivity _).
    now apply (antisymmetry (≤)).
  Qed.

  Lemma lt_not_le_flip x y : y < x → ¬x ≤ y.
  Proof.
    intros E1 E2.
    now destruct (le_not_lt_flip y x).
  Qed.

  Lemma lt_le_trans x y z : x < y → y ≤ z → x < z.
  Proof.
    rewrite !lt_iff_le_apart.
    intros [E1a E1b] E2.
    split.
     now transitivity y.
    destruct (cotransitive E1b z) as [E3 | E3]; trivial.
    apply lt_apart. symmetry in E3.
    transitivity y; rewrite lt_iff_le_apart; tauto.
  Qed.

  Lemma le_lt_trans x y z : x ≤ y → y < z → x < z.
  Proof.
    rewrite !lt_iff_le_apart.
    intros E2 [E1a E1b].
    split.
     now transitivity y.
    destruct (cotransitive E1b x) as [E3 | E3]; trivial.
    apply lt_apart. symmetry in E3.
    transitivity y; rewrite lt_iff_le_apart; tauto.
  Qed.

  Lemma lt_iff_le_ne `{!TrivialApart A} x y : x < y ↔ x ≤ y ∧ x ≠ y.
  Proof. rewrite <-trivial_apart. now apply lt_iff_le_apart. Qed.

  Lemma le_equiv_lt `{!TrivialApart A} `{∀ x y, Decision (x = y)} x y : x ≤ y → x = y ∨ x < y.
  Proof.
    intros. destruct (decide (x = y)); try tauto.
    right. rewrite lt_iff_le_ne; tauto.
  Qed.

  Program Instance dec_from_lt_dec `{!TrivialApart A} `{∀ x y, Decision (x ≤ y)} :
     ∀ x y, Decision (x = y) := λ x y,
    match decide_rel (≤) x y with
    | left E1 => match decide_rel (≤) y x with
       | left E2 => left _
       | right E2 => right _
       end
     | right E1 => right _
     end.
  Next Obligation. now apply (antisymmetry (≤)). Qed.
  Next Obligation. apply not_symmetry. now apply not_le_ne. Qed.
  Next Obligation. now apply not_le_ne. Qed.

  Definition lt_dec_slow `{!TrivialApart A} `{∀ x y, Decision (x ≤ y)} :
    ∀ x y, Decision (x < y).
  Proof.
    intros x y.
    destruct (decide (x ≤ y)).
     destruct (decide (x = y)).
      right. now apply eq_not_lt.
     left. apply lt_iff_le_ne; intuition.
    right. now apply not_le_not_lt.
  Defined.
End full_partial_order.

(* Due to bug #2528 *)
Hint Extern 5 (PropHolds (_ ≠ _)) => eapply @strict_po_apart_ne :  typeclass_instances.
Hint Extern 10 (PropHolds (_ ≤ _)) => eapply @lt_le : typeclass_instances.
Hint Extern 20 (Decision (_ < _)) => eapply @lt_dec_slow : typeclass_instances.

Section full_pseudo_order.
  Context `{FullPseudoOrder A}.

  Instance: StrongSetoid A := pseudo_order_setoid.

  Lemma not_lt_le_flip x y : ¬y < x → x ≤ y.
  Proof. intros. now apply le_iff_not_lt_flip. Qed.

  Instance: PartialOrder (≤).
  Proof.
    split; try apply _.
      intros ? ? E1 ? ? E2.
      now rewrite !le_iff_not_lt_flip, E1, E2.
     split.
      intros x. apply not_lt_le_flip, (irreflexivity (<)).
     intros x y z.
     rewrite !le_iff_not_lt_flip.
     intros. change (complement (<) z x).
     now transitivity y.
    intros x y.
    rewrite !le_iff_not_lt_flip.
    intros E1 E2.
    now apply (antisymmetry (complement (<))).
  Qed.

  Global Instance: FullPartialOrder (_ : Le A) (_ : Lt A).
  Proof.
    split; try apply _.
    intros x y. rewrite !le_iff_not_lt_flip. split.
     intros E. split.
      now apply lt_flip.
     now apply pseudo_order_lt_apart.
    intros [? E].
    now apply not_lt_apart_lt_flip.
  Qed.

  Global Instance: ∀ x y, Stable (x ≤ y).
  Proof.
    intros x y. unfold Stable, DN.
    rewrite !le_iff_not_lt_flip. tauto.
  Qed.

  Lemma le_or_lt `{!TrivialApart A} `{∀ x y, Decision (x = y)} x y : x ≤ y ∨ y < x.
  Proof.
    destruct (trichotomy (<) x y) as [|[|]]; try tauto.
     left. now apply lt_le.
    left. now apply eq_le_flip.
  Qed.

  Global Instance le_total `{!TrivialApart A} `{∀ x y, Decision (x = y)} : TotalOrder (≤).
  Proof. split; try apply _. intros x y. destruct (le_or_lt x y). tauto. right. now apply lt_le. Qed.

  Lemma not_le_lt_flip `{!TrivialApart A} `{∀ x y, Decision (x = y)} x y : ¬y ≤ x → x < y.
  Proof. intros. destruct (le_or_lt y x); intuition. Qed.

  Existing Instance dec_from_lt_dec.

  Program Definition lt_dec `{!TrivialApart A} `{∀ x y, Decision (x ≤ y)} :
      ∀ x y, Decision (x < y) := λ x y,
    match decide_rel (≤) y x with
    | left E => right _
    | right E => left _
    end.
  Next Obligation. now apply le_not_lt_flip. Qed.
  Next Obligation. now apply not_le_lt_flip. Qed.
End full_pseudo_order.

Hint Extern 8 (Decision (_ < _)) => eapply @lt_dec : typeclass_instances.
(*
The following instances would be tempting, but turn out to be a bad idea.

Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne : typeclass_instances.
Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne_flip : typeclass_instances.

It will then loop like:

semirings.lt_0_1 → lt_ne_flip → ...
*)

Section dec_strict_setoid_order.
  Context `{StrictSetoidOrder A} `{Apart A} `{!TrivialApart A} `{∀ x y, Decision (x = y)}.

  Instance: Setoid A := strict_setoid_order_setoid.
  Instance: StrongSetoid A := dec_strong_setoid.

  Context `{!Trichotomy (<)}.

  Instance dec_strict_pseudo_order: PseudoOrder (<).
  Proof.
    split; try apply _.
      intros x y [??]. destruct (lt_antisym x y); tauto.
     intros x y Exy z.
     destruct (trichotomy (<) x z) as [? | [Exz | Exz]]; try tauto.
      right. now rewrite <-Exz.
     right. now transitivity x.
    intros x y. rewrite trivial_apart. split.
     destruct (trichotomy (<) x y); intuition.
    intros [?|?]. now apply lt_ne. now apply lt_ne_flip.
  Qed.
End dec_strict_setoid_order.

Section dec_partial_order.
  Context `{PartialOrder A} `{∀ x y, Decision (x = y)}.

  Instance: Setoid A := po_setoid.
  Definition dec_lt: Lt A := λ x y, x ≤ y ∧ x ≠ y.

  Context `{Alt : Lt A} (lt_correct : ∀ x y, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance dec_order: StrictSetoidOrder (<).
  Proof.
    split; try apply _.
     intros ? ? E1 ? ? E2.
     now rewrite !lt_correct, E1, E2.
    split; try apply _.
     intros x. red. rewrite lt_correct. now intros [_ []].
    intros x y z. rewrite !lt_correct. intros [E1a E1b] [E2a E2b].
    split.
     now transitivity y.
    intros E3. destruct E2b.
    apply (antisymmetry (≤)); trivial.
    now rewrite <-E3.
  Qed.

  Context `{Apart A} `{!TrivialApart A}.

  Instance: StrongSetoid A := dec_strong_setoid.

  Instance dec_full_partial_order: FullPartialOrder (≤) (<) := {}.
  Proof. setoid_rewrite trivial_apart; apply lt_correct. Qed.

  Context `{!TotalRelation (≤)}.

  Instance: Trichotomy (<).
  Proof.
    intros x y. rewrite !lt_correct.
    destruct (decide (x = y)); try tauto.
    destruct (total (≤) x y); intuition.
  Qed.

  Instance dec_pseudo_order: PseudoOrder (<).
  Proof dec_strict_pseudo_order.

  Instance dec_full_pseudo_order: FullPseudoOrder (≤) (<).
  Proof.
    split; try apply _.
    intros x y. rewrite lt_correct. split.
     intros ? [? []]. now apply (antisymmetry (≤)).
    intros E1.
    destruct (total (≤) x y); trivial.
    destruct (decide (x = y)) as [E2|E2].
     now rewrite E2.
    intuition.
  Qed.
End dec_partial_order.
