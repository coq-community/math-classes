Require Import Morphisms Setoid Program abstract_algebra.

Section contents.
Context `{Setoid A} `{Order A}.

Lemma sprecedes_weaken x y : PropHolds (x < y) → PropHolds (x ≤ y).
Proof. firstorder. Qed.

Lemma sprecedes_ne x y : PropHolds (x < y) → PropHolds (x ≠ y).
Proof. firstorder. Qed.

Lemma sprecedes_ne_flip x y : PropHolds (x < y) → PropHolds (y ≠ x).
Proof. firstorder. Qed.

Lemma precedes_flip `{!TotalOrder (≤)} x y : ¬y ≤ x → x ≤ y.
Proof. firstorder. Qed.

Lemma neq_precedes_sprecedes x y : (x ≠ y ∧ x ≤ y) ↔ x < y.
Proof. firstorder. Qed.

Lemma sprecedes_flip `{!TotalOrder (≤)} x y : ¬y < x → y ≠ x → x < y.
Proof. firstorder. Qed.

Lemma equiv_not_sprecedes x y : x = y → ¬x < y.
Proof. firstorder. Qed.

Context `{!Proper ((=) ==> (=) ==> iff) (≤)}.

Global Instance sprecedes_proper: Proper ((=) ==> (=) ==> iff) (<) | 0.
Proof. 
  intros x1 y1 E1 x2 y2 E2. 
  unfold "<". rewrite E1, E2. tauto.
Qed.

Context `{!PartialOrder (≤)}.

Lemma sprecedes_trans_l x y z : x < y → y ≤ z → x < z.
Proof with auto.
  intros [E1a E1b] E2.
  split. transitivity y...
  intro E. rewrite <-E in E2. apply E1b.
  apply (antisymmetry (≤))...
Qed.

Lemma sprecedes_trans_r x y z : x ≤ y → y < z → x < z.
Proof with auto.
  intros E1 [E2a E2b].
  split. transitivity y...
  intro E. rewrite E in E1. apply E2b.
  apply (antisymmetry (≤))...
Qed.

Global Instance sprecedes_trans : Transitive (<).
Proof with auto.
  intros x y z E1 E2.
  apply sprecedes_trans_l with y...
  apply sprecedes_weaken...
Qed.

Lemma equiv_precedes x y : x = y → x ≤ y.
Proof. intros E. rewrite E. reflexivity. Qed.
 
Lemma equiv_sprecedes_precedes x y : (x = y ∨ x < y) → x ≤ y.
Proof. intros [E|E]. apply equiv_precedes; auto. firstorder. Qed.

Lemma sprecedes_or_equiv `{∀ x y, Decision (x = y)} `{!TotalOrder (≤)} x y : x < y ∨ x = y ∨ y < x.
Proof with auto.
  destruct (decide (x = y))...
  destruct (total_order y x)...
   right. right. split... apply not_symmetry...
  left. split...
Qed.

Lemma precedes_or_sprecedes `{!TotalOrder (≤)} `{∀ x y, Decision (x = y)} x y : 
  x ≤ y ∨ y < x.
Proof with auto. 
  destruct (sprecedes_or_equiv y x) as [|[|]]...
   left. apply equiv_precedes. symmetry...
  left. apply sprecedes_weaken...
Qed.

Lemma sprecedes_precedes `{∀ x y, Decision (x = y)} x y : (x = y ∨ x < y) ↔ x ≤ y.
Proof with auto.
  split.
   apply equiv_sprecedes_precedes.
  intros E. destruct (decide (x = y))... right; split...
Qed.

Lemma not_precedes_sprecedes `{!TotalOrder (≤)} x y : ¬y ≤ x ↔ x < y.
Proof with auto.
  split. 
   intros E. split. apply precedes_flip; trivial.
   intros F. apply E. apply equiv_precedes. now symmetry.
  firstorder.
Qed.

Lemma not_sprecedes_precedes `{!TotalOrder (≤)} `{∀ x y, Decision (x = y)} x y : 
  ¬y < x ↔ x ≤ y.
Proof.
  split; intros E.
   destruct (sprecedes_or_equiv x y) as [|[|]].
     now apply sprecedes_weaken.
    now apply equiv_precedes.
   contradiction.
  firstorder. 
Qed.

Global Instance sprecedes_dec_slow `{∀ x y, Decision (x ≤ y)} `{∀ x y, Decision (x = y)} : ∀ x y, Decision (x < y) | 10.
Proof.
  intros x y.
  destruct (decide (x ≤ y)) as [|E].
   destruct (decide (x = y)).
    right. now apply equiv_not_sprecedes.
   left; now split.
  right. intros F. apply E. now apply sprecedes_weaken.
Defined.

Global Program Instance sprecedes_dec `{!TotalOrder (≤)} `{∀ x y, Decision (x ≤ y)} : ∀ x y, Decision (x < y) | 9 := λ x y, 
  match decide_rel (≤) y x with
  | left E => right _
  | right E => left _
  end.
Next Obligation. intro. now apply (not_precedes_sprecedes x y). Qed.
Next Obligation. now apply not_precedes_sprecedes. Qed.
End contents.

Hint Extern 10 (PropHolds (_ ≤ _)) => eapply @sprecedes_weaken : typeclass_instances. 

(*
The following instances turn out to be a bad idea, we then have:
  semirings.sprecedes_0_1 -> sprecedes_ne_flip -> ...

Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @sprecedes_ne : typeclass_instances. 
Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @sprecedes_ne_flip : typeclass_instances. 
*)
