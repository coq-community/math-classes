Require Import Morphisms Setoid Program abstract_algebra.

Section contents.
  Context `{Setoid A} `{Order A}.

  Lemma strictly_precedes_weaken x y : x < y → x ≤ y.
  Proof. firstorder. Qed.

  Lemma precedes_flip `{!TotalOrder (≤)} x y : ¬y ≤ x → x ≤ y.
  Proof. firstorder. Qed.

  Lemma neq_precedes_precedes x y : (x ≠ y ∧ x ≤ y) ↔ x < y.
  Proof. firstorder. Qed.

  Lemma strictly_precedes_flip `{!TotalOrder (≤)} x y : ¬y < x → y ≠ x → x < y.
  Proof. firstorder. Qed.

  Lemma equiv_not_strictly_precedes x y : x = y → ¬x < y.
  Proof. firstorder. Qed.

  Context `{!Proper ((=) ==> (=) ==> iff) (≤)}.

  Global Instance: Proper ((=) ==> (=) ==> iff) (<).
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    unfold "<". rewrite E1, E2. tauto.
  Qed.

  Context `{!PartialOrder (≤)}.

  Lemma strictly_precedes_trans_l x y z : x < y → y ≤ z → x < z.
  Proof with auto.
    intros [E1a E1b] E2.
    split. transitivity y...
    intro E. rewrite <-E in E2. apply E1b.
    apply (antisymmetry (≤))...
  Qed.

  Lemma strictly_precedes_trans_r x y z : x ≤ y → y < z → x < z.
  Proof with auto.
    intros E1 [E2a E2b].
    split. transitivity y...
    intro E. rewrite E in E1. apply E2b.
    apply (antisymmetry (≤))...
  Qed.

  Global Instance strictly_precedes_trans : Transitive (<).
  Proof with auto.
    intros x y z E1 E2.
    apply strictly_precedes_trans_l with y...
    apply strictly_precedes_weaken...
  Qed.

  Lemma equiv_precedes x y : x = y → x ≤ y.
  Proof. intros E. rewrite E. reflexivity. Qed.
 
  Lemma equal_strictly_precedes_precedes x y : (x = y ∨ x < y) → x ≤ y.
  Proof. intros [E|E]. apply equiv_precedes; auto. firstorder. Qed.

  Lemma strictly_precedes_or_equiv `{∀ x y, Decision (x = y)} `{!TotalOrder (≤)} x y : x < y ∨ x = y ∨ y < x.
  Proof with auto.
    destruct (decide (x = y))...
    destruct (total_order y x)...
     right. right. split... apply not_symmetry...
    left. split...
  Qed.
  
  Lemma precedes_or_strictly_precedes `{!TotalOrder (≤)} `{∀ x y, Decision (x = y)} x y : 
    x ≤ y ∨ y < x.
  Proof with auto. 
    destruct (strictly_precedes_or_equiv y x) as [|[|]]...
     left. apply equiv_precedes. symmetry...
    left. apply strictly_precedes_weaken...
  Qed.

  Lemma strictly_precedes_precedes `{∀ x y, Decision (x = y)} x y : (x = y ∨ x < y) ↔ x ≤ y.
  Proof with auto.
    split.
    apply equal_strictly_precedes_precedes.
    intros E. destruct (decide (x = y))... right; split...
  Qed.

  Lemma not_precedes_strictly_precedes `{!TotalOrder (≤)} x y : ¬y ≤ x ↔ x < y.
  Proof with auto.
    split. 
    intros E. split. apply precedes_flip... 
    intros F. apply E. apply equiv_precedes. symmetry...
    firstorder.
  Qed.

  Lemma not_strictly_precedes_precedes `{!TotalOrder (≤)} `{∀ x y, Decision (x = y)}
    x y : ¬y < x ↔ x ≤ y.
  Proof with auto.
    split; intros E.
     destruct (strictly_precedes_or_equiv x y) as [|[|]].
       apply strictly_precedes_weaken...
      apply equiv_precedes...
     contradiction.
    firstorder. 
  Qed.

  Global Instance strictly_precedes_dec_slow `{∀ x y, Decision (x ≤ y)} `{∀ x y, Decision (x = y)} : 
    ∀ x y, Decision (x < y) | 10.
  Proof with auto.
    intros x y.
    destruct (decide (x ≤ y)) as [|E].
    destruct (decide (x = y)).
    right. apply equiv_not_strictly_precedes...
    left; split...
    right. intros F. apply E. apply strictly_precedes_weaken...
  Qed.

  Global Instance strictly_precedes_dec `{!TotalOrder (≤)} `{∀ x y, Decision (x ≤ y)} : 
    ∀ x y, Decision (x < y) | 9.
  Proof with auto.
    intros x y.
    destruct (decide (y ≤ x)).
    right. intro. apply (not_precedes_strictly_precedes x y)...
    left. apply not_precedes_strictly_precedes...
  Qed.
End contents.
