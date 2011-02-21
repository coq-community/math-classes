(* In the standard library equality on streams is defined as pointwise Leibniz equality. 
    Here we prove similar results, but we use setoid equality instead. *)
Require Export Streams.
Require Import Morphisms peano_naturals abstract_algebra.

Section streams.
Context `{Setoid A}.

CoInductive Stream_eq_coind (s1 s2: Stream A) : Prop :=
  stream_eq_coind : hd s1 = hd s2 → Stream_eq_coind (tl s1) (tl s2) → Stream_eq_coind s1 s2.

Global Instance stream_eq: Equiv (Stream A) := Stream_eq_coind.

Global Instance: Setoid (Stream A).
Proof.
  split.
    cofix FIX.
    now constructor.
   cofix FIX. intros ? ? E.
   constructor.
    symmetry. now destruct E.
   apply FIX. now destruct E.
  cofix FIX. intros ? ? ? E1 E2.
  constructor.
   transitivity (hd y). now destruct E1. now destruct E2.
  apply FIX with (tl y). now destruct E1. now destruct E2.
Qed.

Global Instance: Proper ((=) ==> (=)) (@Cons A).
Proof. 
  intros ? ? E.
  constructor.
   simpl. now rewrite E.
  easy.
Qed.

Global Instance: Proper ((=) ==> (=)) (@hd A).
Proof. now intros ? ? []. Qed.

Global Instance: Proper ((=) ==> (=)) (@tl A).
Proof. now intros ? ? []. Qed.

Global Instance: Proper ((=) ==> (=) ==> (=)) (@Str_nth_tl A).
Proof.
  intros n m E1 ? ? E2.
  unfold equiv, peano_naturals.nat_equiv in E1.
  rewrite E1. clear E1 n.
  induction m.
   easy.
  simpl. rewrite <-2!tl_nth_tl.
  now rewrite IHm.
Qed.

Global Instance: Proper ((=) ==> (=) ==> (=)) (@Str_nth A).
Proof.
  intros ? ? E1 ? ? E2.
  unfold Str_nth.
  now rewrite E1, E2.
Qed.

Lemma stream_eq_Str_nth s1 s2 : s1 = s2 ↔ ∀ n, Str_nth n s1 = Str_nth n s2.
Proof.
  split.
   intros E ?. now rewrite E.
  revert s1 s2.
  cofix FIX.
  intros s1 s2 E.
  constructor.
   now apply (E O).
  apply FIX.
  intros. now apply (E (S n)).
Qed.

Global Instance ForAll_proper `{!Proper ((=) ==> iff) (P : Stream A → Prop)} : 
  Proper ((=) ==> iff) (ForAll P).
Proof.
  assert (∀ x y, x = y → ForAll P x → ForAll P y).
   cofix FIX.
   intros ? ? E1 E2.
   constructor.
    rewrite <-E1. now destruct E2.
   apply FIX with (tl x).
    now rewrite E1.
   now destruct E2.
  intros ? ? E1. firstorder.
Qed.

Lemma ForAll_tl (P : Stream A → Prop) s : ForAll P s → ForAll P (tl s).
Proof. apply (ForAll_Str_nth_tl 1). Qed.

Lemma ForAll_True (s : Stream A) : ForAll (λ _, True) s.
Proof. revert s. cofix. intros. constructor; trivial. Qed.

Definition EventuallyForAll (P : Stream A → Prop) := ForAll (λ s, P s → P (tl s)).

Lemma EventuallyForAll_tl P s : EventuallyForAll P s → EventuallyForAll P (tl s).
Proof. repeat intro. now apply ForAll_tl. Qed.

Lemma EventuallyForAll_Str_nth_tl P n s : 
  EventuallyForAll P s → EventuallyForAll P (Str_nth_tl n s).
Proof.
  revert s. 
  induction n. 
   easy.
  intros. now apply IHn, EventuallyForAll_tl.
Qed.

Global Instance EventuallyForAll_proper `{!Proper ((=) ==> iff) (P : Stream A → Prop)} : 
  Proper ((=) ==> iff) (EventuallyForAll P).
Proof.
  assert (Proper ((=) ==> iff) (λ s, P s → P (tl s))).
   intros ? ? E.
   now rewrite E.
  intros ? ? E.
  now rewrite E.
Qed.
End streams.

Section more.
Context `{Setoid A} `{Setoid B}.

CoInductive ForAllIf (PA : Stream A → Prop) (PB : Stream B → Prop) : Stream A → Stream B → Prop :=
  ext_if : ∀ s1 s2, (PA s1 → PB s2) → ForAllIf PA PB (tl s1) (tl s2) → ForAllIf PA PB s1 s2.

Global Instance ForAllIf_proper `{!Proper ((=) ==> iff) (PA : Stream A → Prop)} `{!Proper ((=) ==> iff) (PB : Stream B → Prop)} : 
  Proper ((=) ==> (=) ==> iff) (ForAllIf PA PB).
Proof.
  assert (∀ x1 y1 x2 y2, x1 = y1 → x2 = y2 → ForAllIf PA PB x1 x2 → ForAllIf PA PB y1 y2) as P.
   cofix FIX.
   intros ? ? ? ? E1 E2 E3.
   constructor.
    rewrite <-E1, <-E2. now destruct E3.
   apply FIX with (tl x1) (tl x2).
     now rewrite E1.
    now rewrite E2.
   now destruct E3.
  repeat intro. now split; apply P.
Qed.

Global Instance map_proper `{!Proper ((=) ==> (=)) (f : A → B)} : 
  Proper ((=) ==> (=)) (map f).
Proof.
  cofix FIX.
  intros ? ? E.
  constructor.
   simpl. destruct E as [E]. now rewrite E.
  simpl. apply FIX. now apply E.
Qed.

Context `{Setoid C}.
Global Instance zipWith_proper `{!Proper ((=) ==> (=) ==> (=)) (f : A → B → C)} : 
  Proper ((=) ==> (=) ==> (=)) (zipWith f).
Proof.
  cofix FIX.
  intros ? ? E1 ? ? E2.
  constructor.
   simpl. destruct E1 as [E1], E2 as [E2]. now rewrite E1, E2.
  simpl. apply FIX. now apply E1. now apply E2.
Qed.
End more.
