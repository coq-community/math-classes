Require
  theory.nat_distance.
Require Import
  Morphisms Setoid Program
  interfaces.naturals abstract_algebra natpair_integers
  theory.integers theory.rings orders.naturals orders.semirings.

Section contents. 
Context `{Integers Int} `{!RingOrder oR} `{!TotalOrder oR} `{Naturals N}.

Lemma int_abs_uniq (a b : IntAbs Int N) (z : Int) : a z = b z.
Proof.
  destruct a as [a A], b as [b B].
  unfold equiv, sig_equiv. simpl.
  apply (injective (naturals_to_semiring N Int)).
  destruct A as [A|A], B as [B|B]; rewrite <-A in B; clear A.
     now symmetry.
    symmetry. now apply opp_to_semiring.
   apply opp_to_semiring. now symmetry.
  apply (injective (-)). now symmetry.
Qed.
 
Global Program Instance slow_int_abs: IntAbs Int N | 10 :=
  λ x, (int_abs (SRpair N) N (integers_to_ring Int (SRpair N) x))↾_.
Next Obligation.
  unfold int_abs.
  destruct int_abs_sig as [z [M|M]]; simpl; [left | right].
   apply (injective (integers_to_ring Int (SRpair N))).
   transitivity ((integers_to_ring Int (SRpair N) ∘ (naturals_to_semiring N Int)) z).
    reflexivity.
   rewrite (naturals.to_semiring_unique _). assumption.
  apply (injective (integers_to_ring Int (SRpair N))).
  rewrite preserves_opp. 
  transitivity (-(integers_to_ring Int (SRpair N) ∘ (naturals_to_semiring N Int)) z).
    reflexivity.
   rewrite (naturals.to_semiring_unique _). assumption.
Qed.

Context `{!IntAbs Int N}.

Global Instance int_abs_proper: Proper ((=) ==> (=)) (int_abs Int N).
Proof with eauto; try reflexivity.
  intros z z' E.
  unfold int_abs.
  destruct int_abs_sig as [a A], int_abs_sig as [b B].
  simpl. rewrite E in A. clear E z.
  apply (injective (naturals_to_semiring N Int)).
  destruct A as [A|A], B as [B|B]; rewrite <-B in A; clear B z'...
    symmetry. apply opp_to_semiring. symmetry...
   apply opp_to_semiring...
  apply (injective (-))...
Qed.

Lemma int_abs_nat (n: N) : int_abs Int N (naturals_to_semiring N Int n) = n.
Proof with auto.
  apply (injective (naturals_to_semiring N Int)).
  unfold int_abs. destruct int_abs_sig as [a [A | A]]; simpl...
  apply opp_to_semiring...
Qed. 
  
Lemma int_abs_opp_nat (n: N) : int_abs Int N (-naturals_to_semiring N Int n) = n.
Proof with auto.
  apply (injective (naturals_to_semiring N Int)). 
  unfold int_abs. destruct int_abs_sig as [a [A | A]]; simpl.
   symmetry. apply opp_to_semiring. symmetry...
  apply (injective (-))...
Qed. 
  
Lemma int_abs_neg_is_pos (x y: N) : 
  - naturals_to_semiring N Int x = naturals_to_semiring N Int y → x = 0 ∧ y = 0.
Proof with auto using to_semiring_nonneg.
  intro E.
  split; apply (injective (naturals_to_semiring N Int)); rewrite rings.preserves_0; 
      apply (antisymmetry (≤))...
   apply flip_nonpos_opp. rewrite E...
  rewrite <-E. apply opp_to_semiring_nonpos.
Qed. 

Lemma int_abs_nonneg x : 0 ≤ x → naturals_to_semiring N Int (int_abs Int N x) = x.
Proof with auto.
  intros E. 
  unfold int_abs. destruct int_abs_sig as [z Ez]. simpl.
  destruct Ez as [? | Ez]... 
  rewrite <-Ez in E. rewrite <-Ez.
  apply (antisymmetry (≤)).
   apply flip_nonneg_minus.
   apply nonneg_plus_compat...
  apply opp_to_sr_precedes_to_sr.
Qed.

Lemma int_abs_nonneg_plus x y : 
  0 ≤ x → 0 ≤ y → int_abs Int N (x + y) = int_abs Int N x + int_abs Int N y.
Proof with auto; try reflexivity.
  intros Ex Ey.
  apply (injective (naturals_to_semiring N Int)). 
  rewrite preserves_plus.
  rewrite ?int_abs_nonneg...
  apply nonneg_plus_compat...
Qed.

Lemma int_abs_0 : int_abs Int N 0 = 0.
Proof with auto; try reflexivity.
  apply (injective (naturals_to_semiring N Int)). 
  rewrite preserves_0.
  apply int_abs_nonneg...
Qed.

Lemma int_abs_zero x : int_abs Int N x = 0 ↔ x = 0.
Proof with auto; try reflexivity.
  split; intros E.
   unfold int_abs in E. destruct int_abs_sig as [z [E1 | E1]]; simpl in E.
    rewrite <-E1, E, preserves_0...
   rewrite <-E1, E, preserves_0... apply opp_0.
  rewrite E. apply int_abs_0.
Qed.

Lemma int_abs_nonzero x : int_abs Int N x ≠ 0 ↔ x ≠ 0.
Proof. firstorder using int_abs_zero. Qed.

Lemma int_abs_nonneg_mult x y : 
  0 ≤ x → 0 ≤ y → int_abs Int N (x * y) = int_abs Int N x * int_abs Int N y.
Proof with auto; try reflexivity.
  intros Ex Ey.
  apply (injective (naturals_to_semiring N Int)). 
  rewrite preserves_mult.
  rewrite ?int_abs_nonneg...
  apply nonneg_mult_compat...
Qed.

Lemma int_abs_1 : int_abs Int N 1 = 1.
Proof with auto.
  apply (injective (naturals_to_semiring N Int)). 
  rewrite preserves_1.
  apply int_abs_nonneg... 
  apply precedes_0_1.
Qed.

Lemma int_abs_opp z : int_abs Int N (- z) = int_abs Int N z.
Proof.
  unfold int_abs at 2.
  destruct int_abs_sig as [x [E | E]]; simpl; rewrite <- E. apply int_abs_opp_nat.
  rewrite opp_involutive.
  apply int_abs_nat.
Qed.
End contents.
  