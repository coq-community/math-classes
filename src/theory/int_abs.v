Require
  theory.nat_distance.
Require Import
  interfaces.naturals abstract_algebra interfaces.orders natpair_integers
  theory.integers theory.rings orders.naturals orders.rings.

Section contents. 
Context `{Integers Z} `{Apart Z} `{!TrivialApart Z} `{!FullPseudoSemiRingOrder Zle Zlt} `{Naturals N}.

Lemma int_abs_uniq (a b : IntAbs Z N) (z : Z) : a z = b z.
Proof.
  destruct a as [a A], b as [b B].
  unfold equiv, sig_equiv. simpl.
  apply (injective (naturals_to_semiring N Z)).
  destruct A as [A|A], B as [B|B]; rewrite <-A in B; clear A.
     now symmetry.
    symmetry. now apply opp_to_semiring.
   apply opp_to_semiring. now symmetry.
  apply (injective (-)). now symmetry.
Qed.

Global Program Instance slow_int_abs: IntAbs Z N | 10 :=
  λ x, (int_abs (SRpair N) N (integers_to_ring Z (SRpair N) x))↾_.
Next Obligation.
  unfold int_abs.
  destruct int_abs_sig as [z [M|M]]; simpl; [left | right].
   apply (injective (integers_to_ring Z (SRpair N))).
   transitivity ((integers_to_ring Z (SRpair N) ∘ (naturals_to_semiring N Z)) z).
    reflexivity.
   now rewrite (naturals.to_semiring_unique _).
  apply (injective (integers_to_ring Z (SRpair N))).
  rewrite preserves_opp. 
  transitivity (-(integers_to_ring Z (SRpair N) ∘ (naturals_to_semiring N Z)) z).
    reflexivity.
  now rewrite (naturals.to_semiring_unique _).
Qed.

Context `{!IntAbs Z N}.

Global Instance int_abs_proper: Setoid_Morphism (int_abs Z N) | 0.
Proof.
  split; try apply _.
  intros z z' E.
  unfold int_abs.
  destruct int_abs_sig as [a A], int_abs_sig as [b B].
  simpl. rewrite E in A. clear E z.
  apply (injective (naturals_to_semiring N Z)).
  destruct A as [A|A], B as [B|B]; rewrite <-B in A; clear B z'.
     assumption.
    symmetry. apply opp_to_semiring. now symmetry.
   now apply opp_to_semiring.
  now apply (injective (-)).
Qed.

Lemma int_abs_nat (n: N) : int_abs Z N (naturals_to_semiring N Z n) = n.
Proof.
  apply (injective (naturals_to_semiring N Z)).
  unfold int_abs. destruct int_abs_sig as [a [A | A]]; simpl; trivial.
  now apply opp_to_semiring.
Qed. 

Lemma int_abs_opp_nat (n: N) : int_abs Z N (-naturals_to_semiring N Z n) = n.
Proof.
  apply (injective (naturals_to_semiring N Z)). 
  unfold int_abs. destruct int_abs_sig as [a [A | A]]; simpl.
   symmetry. apply opp_to_semiring. now symmetry.
  now apply (injective (-)).
Qed. 

Lemma int_abs_neg_is_pos (x y: N) : 
  - naturals_to_semiring N Z x = naturals_to_semiring N Z y → x = 0 ∧ y = 0.
Proof.
  intro E.
  split; apply (injective (naturals_to_semiring N Z)); rewrite rings.preserves_0; 
      apply (antisymmetry (≤)); try apply to_semiring_nonneg.
   apply flip_nonpos_opp. rewrite E. now apply to_semiring_nonneg.
  rewrite <-E. now apply opp_to_semiring_nonpos.
Qed. 

Lemma int_abs_nonneg x : 0 ≤ x → naturals_to_semiring N Z (int_abs Z N x) = x.
Proof.
  intros E. 
  unfold int_abs. destruct int_abs_sig as [z Ez]. simpl.
  destruct Ez as [? | Ez]; [assumption |].
  rewrite <-Ez in E. rewrite <-Ez.
  apply (antisymmetry (≤)).
   apply flip_nonneg_minus.
   now apply nonneg_plus_compat.
  now apply opp_to_sr_le_to_sr.
Qed.

Lemma int_abs_nonneg_plus x y : 
  0 ≤ x → 0 ≤ y → int_abs Z N (x + y) = int_abs Z N x + int_abs Z N y.
Proof with auto; try reflexivity.
  intros Ex Ey.
  apply (injective (naturals_to_semiring N Z)). 
  rewrite preserves_plus.
  rewrite ?int_abs_nonneg...
  now apply nonneg_plus_compat.
Qed.

Lemma int_abs_0 : int_abs Z N 0 = 0.
Proof.
  apply (injective (naturals_to_semiring N Z)). 
  rewrite preserves_0.
  now apply int_abs_nonneg.
Qed.

Lemma int_abs_0_alt x : int_abs Z N x = 0 ↔ x = 0.
Proof.
  split; intros E.
   unfold int_abs in E. destruct int_abs_sig as [z [E1 | E1]]; simpl in E.
    now rewrite <-E1, E, preserves_0.
   rewrite <-E1, E, preserves_0. now apply opp_0.
  rewrite E. now apply int_abs_0.
Qed.

Lemma int_abs_ne_0 x : int_abs Z N x ≠ 0 ↔ x ≠ 0.
Proof. firstorder using int_abs_0_alt. Qed.

Lemma int_abs_nonneg_mult x y : 
  0 ≤ x → 0 ≤ y → int_abs Z N (x * y) = int_abs Z N x * int_abs Z N y.
Proof.
  intros Ex Ey.
  apply (injective (naturals_to_semiring N Z)). 
  rewrite preserves_mult.
  rewrite ?int_abs_nonneg; intuition.
  now apply nonneg_mult_compat.
Qed.

Lemma int_abs_1 : int_abs Z N 1 = 1.
Proof.
  apply (injective (naturals_to_semiring N Z)). 
  rewrite preserves_1.
  apply int_abs_nonneg.
  now apply le_0_1.
Qed.

Lemma int_abs_opp z : int_abs Z N (- z) = int_abs Z N z.
Proof.
  unfold int_abs at 2.
  destruct int_abs_sig as [x [E | E]]; simpl; rewrite <- E. 
   now apply int_abs_opp_nat.
  rewrite opp_involutive.
  now apply int_abs_nat.
Qed.
End contents.
