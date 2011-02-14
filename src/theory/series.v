Require Import 
  Program Morphisms Ring Factorial workaround_tactics
  abstract_algebra interfaces.additional_operations interfaces.naturals interfaces.integers
  theory.nat_pow theory.int_pow theory.streams.

Section series.
Context `{SemiRing A} `{!SemiRingOrder leA}.
Add Ring A : (rings.stdlib_semiring_theory A).
Add Ring nat : (rings.stdlib_semiring_theory nat).

Class DecreasingNonNegative (s : Stream A) : Prop := 
  decreasing_nonneg : ForAll (λ t, 0 ≤ hd (tl t) ≤ hd t) s.

(* An equivalent definition is to say that given a point [s] in the stream, 
  then every further point in that stream is in [[0,s]]. *)
Lemma dnn_alt (s : Stream A) : 
  DecreasingNonNegative s ↔ ForAll (λ s, ForAll (λ t, 0 ≤ hd t ≤ hd s) s) s.
Proof.
  split; revert s; cofix FIX; intros s E.
   constructor.
    cut (hd s ≤ hd s); [|reflexivity].
    set (x:=hd s).
    unfold x at 1.
    generalize s E x. clear s E x.
    cofix FIX2. intros s E.
    constructor.
     split; trivial.
     destruct E. 
     now transitivity (hd (tl s)).
    destruct E.
    apply FIX2; trivial.
    now transitivity (hd s).
   destruct E.
   now apply FIX. 
  constructor.
   now destruct E as [[? [? ?]] ?].
  apply FIX.
  now destruct E.
Qed.

Definition dnn_Str_nth (s : Stream A) : 
  DecreasingNonNegative s ↔ ∀ n, 0 ≤ Str_nth (S n) s ≤ Str_nth n s.
Proof.
  split.
   intros dnn n. revert s dnn.
   induction n; intros s E; unfold Str_nth in *; simpl.
    apply E.
   apply IHn. now destruct E.
  revert s. cofix FIX. intros s E.
  constructor; unfold Str_nth in *; simpl in *.
   apply (E O).
  apply FIX. intros n. 
  apply (E (S n)).
Qed.

Global Instance dnn_tl `(dnn : DecreasingNonNegative s) : DecreasingNonNegative (tl s).
Proof. now destruct dnn. Qed.

Global Instance dnn_Str_nth_tl `(dnn : DecreasingNonNegative s) : ∀ n, DecreasingNonNegative (Str_nth_tl n s).
Proof.
  intros n.
  revert s dnn.
  induction n; [easy|].
  intros s E.
  now apply IHn, _.
Qed.

Lemma dnn_hd_nonneg `(dnn : DecreasingNonNegative s) : 0 ≤ hd  s.
Proof. destruct dnn. now transitivity (hd (tl s)). Qed.

Lemma dnn_Str_nth_nonneg `(dnn : DecreasingNonNegative s) n : 0 ≤ Str_nth n s.
Proof. destruct n; apply (dnn_hd_nonneg _). Qed.

Class IncreasingNonNegative (s : Stream A) : Prop := 
  increasing_nonneg : ForAll (λ s, 0 ≤ hd s ≤ hd (tl s)) s.

Lemma inn_Str_nth (s : Stream A) :
  IncreasingNonNegative s ↔ ∀ n, 0 ≤ Str_nth n s ≤ Str_nth (S n) s.
Proof.
  split.
   intros E n. revert s E.
   induction n; intros s E; unfold Str_nth in *; simpl.
    apply E.
   apply IHn. now destruct E.
  revert s. cofix FIX. intros s E.
  constructor; unfold Str_nth in *; simpl in *.
   apply (E O).
  apply FIX. intros n. 
  apply (E (S n)).
Qed.

Global Instance inn_tl `(inn : IncreasingNonNegative s) : IncreasingNonNegative (tl s).
Proof. now destruct inn. Qed.

Global Instance inn_Str_nth_tl `(inn : IncreasingNonNegative s) : ∀ n, IncreasingNonNegative (Str_nth_tl n s).
Proof.
  intros n. revert s inn.
  induction n; trivial.
  intros s E.
  now apply IHn, _.
Qed.

Section every_other.
  CoFixpoint everyOther (s : Stream A) : Stream A := Cons (hd s) (everyOther (tl (tl s))).

  Lemma Str_nth_tl_everyOther (n : nat) (s : Stream A) : Str_nth_tl n (everyOther s) ≡ everyOther (Str_nth_tl (2 * n) s).
  Proof.
    revert s.
    induction n; intros s; simpl; trivial.
    rewrite IHn.
    replace (n + S (n + 0))%nat with (S (2*n))%nat.
     easy.
    change (1 + (1 + 1) * n = n + (1 + (n + 0))). ring.
  Qed.
  
  Lemma Str_nth_everyOther (n : nat) (s : Stream A) : Str_nth n (everyOther s) = Str_nth (2 * n) s.
  Proof.
    unfold Str_nth.
    rewrite Str_nth_tl_everyOther.
    now destruct (Str_nth_tl (2 * n) s).
  Qed.

  Global Instance everyOther_dnn `(dnn : !DecreasingNonNegative s) : DecreasingNonNegative (everyOther s).
  Proof.
    revert s dnn. 
    cofix FIX. intros s dnn.
    constructor; simpl.
     destruct dnn as [? [? ?]]. split. easy. now transitivity (hd (tl s)).
    now apply FIX, _.
  Qed.

  Global Instance everyOther_inc `(inn : !IncreasingNonNegative s) : IncreasingNonNegative (everyOther s).
  Proof.
    revert s inn.
    cofix FIX. intros s [? [? ?]].
    constructor; simpl.
     split. easy. now transitivity (hd (tl s)).
    now apply FIX.
  Qed.
End every_other.

Section mult.
  Definition mult_Streams := zipWith (.*.).
  
  Global Instance mult_Streams_dnn `(dnn1 : !DecreasingNonNegative s1) `(dnn2 : !DecreasingNonNegative s2) : 
    DecreasingNonNegative (mult_Streams s1 s2).
  Proof.
    revert s1 s2 dnn1 dnn2.
    cofix FIX. intros s1 s2 [[? ?] ?] [[? ?] ?].
    constructor; simpl.
     split.
      now apply semirings.nonneg_mult_compat.
     now apply semirings.mult_compat.
    now apply FIX.
  Qed.

  Global Instance mult_Streams_inc `(inn1 : !IncreasingNonNegative s1) `(inn2 : !IncreasingNonNegative s2) :
    IncreasingNonNegative (mult_Streams s1 s2).
  Proof .
    revert s1 s2 inn1 inn2.
    cofix FIX. intros s1 s2 [? ?] [? ?].
    constructor; simpl.
     split.
      now apply semirings.nonneg_mult_compat.
     now apply semirings.mult_compat.
    now apply FIX.
  Qed.
  
  Global Instance: Proper ((=) ==> (=) ==> (=)) mult_Streams.
  Proof. apply _. Qed. 
End mult.

Section powers.
  Context (a : A).

  CoFixpoint powers_help (c : A) : Stream A := Cons c (powers_help (c * a)).
  
  Definition powers : Stream A := powers_help 1.

  Section with_nat_pow.
  Context `{Naturals N} `{!NatPowSpec A N pw} (f : nat → N) `{!SemiRing_Morphism f}.

  Lemma Str_nth_powers_help (n : nat) (c : A) : Str_nth n (powers_help c) = c * a ^ (f n).
  Proof.
    revert c.
    induction n; intros c; unfold Str_nth in *; simpl.
     change O with (0 : nat).
     rewrite rings.preserves_0.
     rewrite nat_pow_0. ring.
    rewrite peano_naturals.S_nat_1_plus. 
    rewrite rings.preserves_plus, rings.preserves_1. 
    rewrite nat_pow_S.
    rewrite IHn. ring.
  Qed.

  Lemma Str_nth_powers (n : nat) : Str_nth n powers = a ^ (f n).
  Proof.
    unfold powers.
    rewrite Str_nth_powers_help.
    ring.
  Qed.
  End with_nat_pow.

  Section with_int_pow. 
  Context `{!GroupInv A} `{!MultInv A} `{!Field A} `{∀ x y, Decision (x = y)} `{!DecMultInv A}
     `{Integers Z} `{!IntPowSpec A Z pw} (f : nat → Z) `{!SemiRing_Morphism f}.

  Lemma Str_nth_powers_help_int_pow (n : nat) (c : A) : Str_nth n (powers_help c) = c * a ^ (f n).
  Proof.
    rewrite (Str_nth_powers_help id). unfold id.
    now rewrite int_pow_nat_pow.
  Qed.

  Lemma Str_nth_powers_int_pow (n : nat) : Str_nth n powers = a ^ (f n).
  Proof.
    unfold powers.
    rewrite Str_nth_powers_help_int_pow.
    ring.
  Qed.
  End with_int_pow.
End powers.

Global Instance powers_help_proper: Proper ((=) ==> (=) ==> (=)) powers_help.
Proof.
  intros ? ? E1 ? ? E2.
  apply stream_eq_Str_nth.
  intros n.
  now rewrite 2!(Str_nth_powers_help _ id), E1, E2.
Qed.

Global Instance powers_proper: Proper ((=) ==> (=)) powers.
Proof.
  intros ? ? E.
  apply stream_eq_Str_nth.
  intros n.
  now rewrite 2!(Str_nth_powers _ id), E.
Qed.

Section positives.
  CoFixpoint positives_help (x : A) : Stream A := Cons x (positives_help (1 + x)).

  Lemma Str_nth_positives_help (n : nat) (x : A) : 
    Str_nth n (positives_help x) = x + naturals_to_semiring nat A n.
  Proof.
    revert x.
    induction n; intros c; unfold Str_nth in *; simpl. 
     change (c = c + naturals_to_semiring nat A 0).
     rewrite rings.preserves_0. 
     now ring.
    rewrite IHn. 
    rewrite peano_naturals.S_nat_1_plus.
    rewrite rings.preserves_plus, rings.preserves_1.
    now ring.
  Qed.

  Definition positives : Stream A := positives_help 1.

  Lemma Str_nth_positives (n : nat) : 
    Str_nth n positives = 1 + naturals_to_semiring nat A n.
  Proof.
    unfold positives.
    now rewrite Str_nth_positives_help.
  Qed.
End positives.

Section factorials.
  CoFixpoint factorials_help (n c : A) : Stream A := Cons c (factorials_help (1 + n) (n * c)).

  Fixpoint fac_help (n : nat) (m c : A) : A := 
    match n with
    | O => c
    | S n' => (m + naturals_to_semiring nat A n') * fac_help n' m c
    end.

  Lemma Str_nth_factorials_help (n : nat) (m c : A) :
    Str_nth n (factorials_help m c) = fac_help n m c.
  Proof.
    revert m c.
    induction n; intros m c; unfold Str_nth in *; simpl.
     ring. 
    rewrite IHn. clear IHn.
    induction n; simpl.
     posed_rewrite (rings.preserves_0 (f:=naturals_to_semiring nat A)). 
     now ring.
    rewrite IHn.
    rewrite peano_naturals.S_nat_1_plus.
    rewrite rings.preserves_plus, rings.preserves_1.
    now ring.
  Qed.

  Definition factorials := factorials_help 1 1.

  Lemma Str_nth_factorials (n : nat) :
    Str_nth n factorials = naturals_to_semiring nat A (fact n).
  Proof.
    unfold factorials.
    rewrite Str_nth_factorials_help.
    induction n; simpl.
     symmetry. now apply rings.preserves_1.
    rewrite IHn.
    posed_rewrite (rings.preserves_plus (f:=naturals_to_semiring nat A)).
    posed_rewrite (rings.preserves_mult (f:=naturals_to_semiring nat A)).
    now ring.
  Qed.
End factorials.
End series.

Section preservation.
  Context `{SemiRing A} {leA : Order A} `{!SemiRingOrder leA}.
  Context `{SemiRing B} {leB : Order B} `{!SemiRingOrder leB}.
  Context `{!SemiRing_Morphism (f : A → B)}.

  Lemma preserves_powers_help (a c : A) (n : nat) :
    f (Str_nth n (powers_help a c)) = Str_nth n (powers_help (f a) (f c)).
  Proof.
    rewrite 2!(Str_nth_powers_help _ id).
    rewrite rings.preserves_mult.
    now rewrite preserves_nat_pow.
  Qed.

  Lemma preserves_powers (a : A) (n : nat) :
    f (Str_nth n (powers a)) = Str_nth n (powers (f a)).
  Proof.
    rewrite 2!(Str_nth_powers _ id).
    apply preserves_nat_pow.
  Qed.

  Lemma preserves_positives (n : nat) :
    f (Str_nth n positives) = Str_nth n positives.
  Proof.
    rewrite 2!Str_nth_positives.
    rewrite rings.preserves_plus, rings.preserves_1.
    now rewrite <-(naturals.to_semiring_unique (f ∘ naturals_to_semiring nat A)).
  Qed.

  Lemma preserves_factorials (n : nat) :
    f (Str_nth n factorials) = Str_nth n factorials.
  Proof.
    rewrite 2!Str_nth_factorials.
    now rewrite <-(naturals.to_semiring_unique (f ∘ naturals_to_semiring nat A)).
  Qed.
End preservation.
