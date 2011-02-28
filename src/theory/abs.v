Require Import
  Morphisms Ring
  abstract_algebra orders.semirings.

Section contents.
Context `{Ring R} `{oR : Order R} `{!RingOrder oR} `{!TotalOrder oR} `{a : !Abs R}.
Add Ring R : (rings.stdlib_ring_theory R).

Global Instance abs_proper: Proper ((=) ==> (=)) abs.
Proof.
  intros x y E.
  unfold abs, abs_sig. destruct (a x) as [z1 [Ez1 Fz1]]. destruct (a y) as [z2 [Ez2 Fz2]].
  simpl.
  rewrite <-E in Ez2, Fz2.
  destruct (total_order 0 x).
   now rewrite Ez1, Ez2.
  now rewrite Fz1, Fz2.
Qed.

Lemma abs_nonneg (x : R) : 0 ≤ x → abs x = x.
Proof.
  intros E. unfold abs, abs_sig. destruct (a x) as [z1 [Ez1 Fz1]]. auto.
Qed.

Lemma abs_nonpos (x : R) : x ≤ 0 → abs x = -x.
Proof.
  intros E. unfold abs, abs_sig. destruct (a x) as [z1 [Ez1 Fz1]]. auto.
Qed.

Lemma abs_nonneg_plus (x y : R) :
  0 ≤ x → 0 ≤ y → abs (x + y) = abs x + abs y.
Proof.
  intros Ex Ey.
  rewrite ?abs_nonneg; trivial.
   reflexivity.
  now apply nonneg_plus_compat.
Qed.

Lemma abs_nonpos_plus (x y : R) :
  x ≤ 0 → y ≤ 0 → abs (x + y) = abs x + abs y.
Proof.
  intros Ex Ey.
  rewrite ?abs_nonpos; trivial.
   ring.
  now apply nonpos_plus_compat.
Qed.

Lemma abs_0 : abs 0 = 0.
Proof.
  now rewrite abs_nonneg.
Qed.

Lemma abs_mult (x y : R) : abs (x * y) = abs x * abs y.
Proof with try ring; auto.
  destruct (total_order 0 x) as [Ex|Ex]; destruct (total_order 0 y) as [Ey|Ey].
     rewrite ?abs_nonneg...
     apply nonneg_mult_compat...
    rewrite (abs_nonneg x), (abs_nonpos y), (abs_nonpos (x * y))...
    apply nonneg_nonpos_mult...
   rewrite (abs_nonpos x), (abs_nonneg y), (abs_nonpos (x * y))...
   apply nonpos_nonneg_mult...
  rewrite (abs_nonpos x), (abs_nonpos y), (abs_nonneg (x * y))...
  apply nonpos_mult...
Qed.

Lemma abs_1 : abs 1 = 1.
Proof.
  rewrite abs_nonneg.
   reflexivity.
  apply precedes_0_1.
Qed.

Lemma abs_opp (x : R) : abs (-x) = abs x.
Proof with trivial.
  destruct (total_order 0 x).
   rewrite (abs_nonneg x), abs_nonpos...
    apply rings.opp_involutive.
   apply flip_nonneg_opp...
  rewrite (abs_nonneg (-x)), abs_nonpos...
   reflexivity.
  apply flip_nonpos_opp...
Qed.

End contents.

Section order_preserving.
  Context `{Ring A} `{oA : Order A} `{!RingOrder oA} `{!TotalOrder oA} `{!Abs A}
    `{Ring B} `{oB : Order B} `{!RingOrder oB} `{!TotalOrder oB} `{!Abs B}
    {f : A → B} `{!OrderPreserving f} `{!SemiRing_Morphism f}.

  Lemma preserves_abs x : f (abs x) = abs (f x).
  Proof with trivial.
    destruct (total_order 0 x).
     rewrite ?abs_nonneg...
      reflexivity.
     now apply preserves_nonneg.
    rewrite ?abs_nonpos...
     apply rings.preserves_opp.
    now apply preserves_nonpos.
  Qed.
End order_preserving.
