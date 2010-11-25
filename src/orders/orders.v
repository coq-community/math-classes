Require Import Morphisms Setoid Program abstract_algebra.

Section contents.
  Context `{Setoid A} `{Order A}.

  Lemma precedes_neq_weaken x y : x < y → x ≤ y.
  Proof. firstorder. Qed.

  Lemma precedes_flip {t : TotalOrder (≤)} x y : ¬y ≤ x → x ≤ y.
  Proof. firstorder. Qed.

  Lemma neq_precedes_precedes x y : (x ≠ y ∧ x ≤ y) ↔ x < y.
  Proof. firstorder. Qed.

  Lemma precedes_neq_flip {t : TotalOrder (≤)} x y : ¬y < x → y ≠ x → x < y.
  Proof. firstorder. Qed.

  Lemma equiv_not_precedes_neq x y : x = y → ¬x < y.
  Proof. firstorder. Qed.

  Context `{!Proper ((=) ==> (=) ==> iff) (≤)}.

  Global Instance: Proper ((=) ==> (=) ==> iff) (<).
  Proof. 
    intros x1 y1 E1 x2 y2 E2. 
    unfold "<". rewrite E1, E2. tauto.
  Qed.

  Global Instance precedes_neq_trans {t : Transitive (≤)} {a : AntiSymmetric (≤)} : 
    Transitive (<).
  Proof with auto.
    intros x y z E1 E2.
    destruct E1 as [E1a E1b]. destruct E2 as [E2a E2b].
    split. transitivity y...
    intro E. rewrite E in E1a. eapply E2b.  
    apply (antisymmetry (≤))...
  Qed.

  Lemma equiv_precedes {r : Reflexive (≤)} x y : x = y → x ≤ y.
  Proof. 
    intros E. rewrite E. reflexivity.
  Qed.

  Lemma precedes_neq_precedes x y {r : Reflexive (≤)} `{∀ x y, Decision (x = y)} : (x = y ∨ x < y) ↔ x ≤ y.
  Proof with auto.
    split. 
    intros [E|E]. apply equiv_precedes... firstorder.
    intros E. destruct (decide (x = y))... right; split...
  Qed.

  Lemma not_precedes_precedes_neq {t : TotalOrder (≤)} {r : Reflexive (≤)} {a : AntiSymmetric (≤)}
    x y : ¬y ≤ x ↔ x < y.
  Proof with auto.
    split. 
    intros E. split. apply precedes_flip... 
    intros F. apply E. apply equiv_precedes. symmetry...
    firstorder.
  Qed.

  Lemma not_precedes_neq_precedes {t : TotalOrder (≤)} {r : Reflexive (≤)} {a : AntiSymmetric (≤)} `{∀ x y, Decision (x ≤ y)}
    x y : ¬y < x ↔ x ≤ y.
  Proof with auto.
    split; intros E. 
    apply stable. intros F. apply E, not_precedes_precedes_neq...
    firstorder. 
  Qed.

  Lemma precedes_or_precedes_neq {t : TotalOrder (≤)} {r : Reflexive (≤)} `{∀ x y, Decision (x ≤ y)} x y : 
    x ≤ y ∨ y < x.
  Proof with auto. 
    destruct (decide (x ≤ y)) as [|E]...
    right. split. apply precedes_flip...
    intro. apply E. apply equiv_precedes. symmetry...
  Qed.

  Lemma precedes_neq_or_equiv {t : TotalOrder (≤)} {r : Reflexive (≤)} `{∀ x y, Decision (x ≤ y)} `{∀ x y, Decision (x = y)} x y : 
    x < y ∨ x = y ∨ y < x.
  Proof.
    destruct (precedes_or_precedes_neq x y) as [E|E].
    apply precedes_neq_precedes in E; try apply _.
    intuition. intuition.
  Qed.

  Global Instance precedes_neq_dec_slow `{∀ x y, Decision (x ≤ y)} `{∀ x y, Decision (x = y)} : 
    ∀ x y, Decision (x < y) | 10.
  Proof with auto.
    intros x y.
    destruct (decide (x ≤ y)) as [|E].
    destruct (decide (x = y)).
    right. apply equiv_not_precedes_neq...
    left; split...
    right. intros F. apply E. apply precedes_neq_weaken...
 Qed.

  Global Instance precedes_neq_dec {t : TotalOrder (≤)} {r : Reflexive (≤)} {a : AntiSymmetric (≤)} `{∀ x y, Decision (x ≤ y)} : 
    ∀ x y, Decision (x < y) | 9.
  Proof with auto.
    intros x y.
    destruct (decide (y ≤ x)).
    right. intro. apply (not_precedes_precedes_neq x y)...
    left. apply not_precedes_precedes_neq...
 Qed.

End contents.