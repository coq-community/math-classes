(** 
  The dyadic rationals are numbers of the shape [m * 2 ^ e] with [m : Z] and [e : Z] 
   for some [Integers] implementation [Z]. These numbers form a ring and can be 
   embedded into any [Rationals] implementation [Q]. 
*)
Require
  theory.integers theory.rings theory.fields.
Require Import
  Morphisms Ring Program RelationClasses Setoid
  abstract_algebra 
  interfaces.integers interfaces.naturals interfaces.rationals
  interfaces.additional_operations
  orders.minmax orders.integers orders.rationals
  nonneg_integers_naturals stdlib_rationals
  theory.rationals theory.bit_shift theory.int_pow theory.nat_pow theory.abs. 

Record Dyadic Z := dyadic { mant: Z; expo: Z }.
Implicit Arguments dyadic [[Z]].
Implicit Arguments mant [[Z]].
Implicit Arguments expo [[Z]].

Infix "$" := dyadic (at level 80).

Section dyadics.
Context `{Integers Z} `{!RingOrder oZ} `{!TotalOrder oZ}
  `{equiv_dec : ∀ (x y : Z), Decision (x = y)}
  `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)}
  `{!ShiftLSpec Z (Z⁺) sl}.

Notation Dyadic := (Dyadic Z).
Add Ring Z: (rings.stdlib_ring_theory Z).

Global Program Instance dy_plus: RingPlus Dyadic := λ x y, 
  if precedes_dec (expo x) (expo y)
  then mant x + (mant y ≪ exist _ (expo y - expo x) _) $ min (expo x) (expo y)
  else (mant x ≪ exist _ (expo x - expo y) _) + mant y $ min (expo x) (expo y).
Next Obligation. now apply rings.flip_nonneg_minus. Qed.
Next Obligation. apply rings.flip_nonneg_minus. now apply orders.precedes_flip. Qed.

Global Instance dy_inject: Inject Z Dyadic := λ x, x $ 0.
Global Instance dy_opp: GroupInv Dyadic := λ x, -mant x $ expo x.
Global Instance dy_mult: RingMult Dyadic := λ x y, mant x * mant y $ expo x + expo y.
Global Instance dy_0: RingZero Dyadic := ('0:Dyadic).
Global Instance dy_1: RingOne Dyadic := ('1:Dyadic).

Section DtoQ_slow.
  Context `{Rationals Q} `{Pow Q Z} (ZtoQ: Z → Q).
  Definition DtoQ_slow  (x : Dyadic) := ZtoQ (mant x) * 2 ^ (expo x).
End DtoQ_slow.

Section with_rationals.
  Context `{Rationals Q} `{!IntPowSpec Q Z ipw} `{!SemiRing_Morphism (ZtoQ: Z → Q)}.
  Add Ring Q: (rings.stdlib_ring_theory Q).

  Notation DtoQ_slow' := (DtoQ_slow ZtoQ).

  Lemma ZtoQ_shift (x : Z) (n : Z⁺) : ZtoQ (x ≪ n) = ZtoQ x * 2 ^ ('n : Z).
  Proof.
    rewrite shiftl_nat_pow.
    rewrite rings.preserves_mult, nat_pow.preserves_nat_pow, rings.preserves_2.
    now rewrite <-int_pow_nat_pow.
  Qed.

  Lemma DtoQ_slow_preserves_plus x y : DtoQ_slow' (x + y) = DtoQ_slow' x + DtoQ_slow' y.
  Proof.
    destruct x as [xn xe], y as [yn ye].
    unfold ring_plus at 1. unfold DtoQ_slow, dy_plus. simpl.
    destruct (precedes_dec xe ye) as [E | E]; simpl.
     rewrite rings.preserves_plus, ZtoQ_shift.
     unfold inject, NonNeg_inject. simpl.
     rewrite min_l; try assumption. 
     ring_simplify.
     rewrite <-associativity, <-int_pow_exp_plus.
      now setoid_replace (ye - xe + xe) with ye by ring.
     now apply (ne_zero (2:Q)).
    rewrite rings.preserves_plus, ZtoQ_shift.
    unfold inject, NonNeg_inject. simpl.
    rewrite min_r. 
     ring_simplify.
     rewrite <-associativity, <-int_pow_exp_plus.
      now setoid_replace (xe - ye + ye) with xe by ring.
     now apply (ne_zero (2:Q)).
    now apply orders.precedes_flip.
  Qed. 

  Lemma DtoQ_slow_preserves_opp x : DtoQ_slow' (-x) = -DtoQ_slow' x.
  Proof.
    unfold DtoQ_slow. simpl.
    rewrite rings.preserves_inv. ring.
  Qed.

  Lemma DtoQ_slow_preserves_mult x y : DtoQ_slow' (x * y) = DtoQ_slow' x * DtoQ_slow' y.
  Proof.
    destruct x as [xn xe], y as [yn ye].
    unfold DtoQ_slow. simpl.
    rewrite rings.preserves_mult.
    rewrite int_pow_exp_plus. 
     ring.
    apply (ne_zero (2:Q)).
  Qed.

  Lemma DtoQ_slow_preserves_0 : DtoQ_slow' 0 = 0.
  Proof. 
    unfold DtoQ_slow. simpl.
    rewrite rings.preserves_0. ring.
  Qed.

  Lemma DtoQ_slow_preserves_1 : DtoQ_slow' 1 = 1.
  Proof.
    unfold DtoQ_slow. simpl.
    rewrite int_pow_0, rings.preserves_1. ring. 
  Qed.
End with_rationals.

(* It would be nicer to use [Frac Z] as implementation of the rationals. However, 
   that becomes horribly slow, so we stick with plain old [Qarith]. *)
Notation StdQ := QArith_base.Q.
Notation ZtoStdQ := (integers.integers_to_ring Z StdQ).
Notation DtoStdQ := (DtoQ_slow ZtoStdQ).

Add Ring StdQ : (rings.stdlib_ring_theory StdQ).

Global Instance dy_equiv: Equiv Dyadic := λ x y, DtoStdQ x = DtoStdQ y.

Instance: Setoid Dyadic.
Proof.
  split; red; unfold equiv, dy_equiv, DtoQ_slow.
    intros x. reflexivity.
   intros x y E. now symmetry.
  intros x y z E1 E2. 
  now transitivity (DtoStdQ y).
Qed.

Global Instance dyadic_proper: Proper ((=) ==> (=) ==> (=)) dyadic.
Proof.
  intros ? ? E1 ? ? E2.
  unfold equiv, dy_equiv, DtoQ_slow. simpl.
  now rewrite E1, E2.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) dy_plus.
Proof.
  repeat intro. unfold equiv, dy_equiv.
  rewrite 2!DtoQ_slow_preserves_plus.
  now apply sg_mor.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) dy_mult.
Proof.
  repeat intro. unfold equiv, dy_equiv.
  rewrite 2!DtoQ_slow_preserves_mult.
  now apply sg_mor.
Qed.

Instance: Proper ((=) ==> (=)) dy_opp.
Proof.
  repeat intro. unfold equiv, dy_equiv.
  rewrite 2!DtoQ_slow_preserves_opp.
  now apply inv_proper.
Qed.

Global Instance: Ring Dyadic.
Proof.
  repeat (split; try apply _); repeat intro; unfold equiv, dy_equiv;
    repeat (rewrite DtoQ_slow_preserves_plus 
      || rewrite DtoQ_slow_preserves_mult || rewrite DtoQ_slow_preserves_opp
      || rewrite DtoQ_slow_preserves_1 || rewrite DtoQ_slow_preserves_0); ring.
Qed.

Global Instance: Injective dy_inject.
Proof.
  repeat (split; try apply _).
   intros x y E. unfold equiv, dy_equiv, dy_inject, DtoQ_slow in E. simpl in *.
   rewrite int_pow_0 in E. ring_simplify in E.
   now apply (injective ZtoStdQ).
  intros x y E.
  unfold equiv, dy_equiv, dy_inject, DtoQ_slow. simpl in *.
  rewrite int_pow_0. now rewrite E.
Qed.

Global Instance: SemiRing_Morphism dy_inject.
Proof.
  repeat (split; try apply _).
   intros x y. unfold sg_op at 2, dy_plus.
   unfold equiv, dy_equiv, dy_inject, DtoQ_slow; simpl.
   case (precedes_dec 0 0); intros E; simpl.
    rewrite 2!rings.preserves_plus, ZtoQ_shift.
    unfold inject, NonNeg_inject. simpl.
    setoid_replace (0 - 0) with 0 by ring.
    rewrite min_l, int_pow_0. ring.
    reflexivity.
   now destruct E.
  intros x y. unfold sg_op at 2, dy_mult. simpl.
  now setoid_replace (0 + 0) with 0 by ring.
Qed.
     
Lemma dy_eq_dec_aux (x y : Dyadic) p : 
  mant x = mant y ≪ exist _ (expo y - expo x) p ↔ x = y.
Proof.
  destruct x as [xm xe], y as [ym ye].
  assert (xe ≤ ye).
   now apply rings.flip_nonneg_minus.
  pose proof (_ : NeZero (2:StdQ)).
  split; intros E.
   unfold equiv, dy_equiv, DtoQ_slow. simpl in *.
   rewrite E, ZtoQ_shift.
   unfold inject, NonNeg_inject. simpl.
   rewrite <-associativity, <-int_pow_exp_plus.
    now setoid_replace (ye - xe + xe) with ye by ring.
   easy.
  unfold equiv, dy_equiv, DtoQ_slow in E. simpl in *.
  apply (injective ZtoStdQ).
  apply (rings.right_cancellation_ne_0 (.*.) (2 ^ xe)).
   now apply int_pow_nonzero.
  rewrite E, ZtoQ_shift.
  unfold inject, NonNeg_inject. simpl.
  rewrite <-associativity, <-int_pow_exp_plus.
   now setoid_replace (ye - xe + xe) with ye by ring.
  easy.
Qed.

Lemma dy_eq_dec_aux_neg (x y : Dyadic) p : 
  mant x ≠ mant y ≪ exist _ (expo y - expo x) p ↔ x ≠ y.
Proof. split; intros E; intro; apply E; eapply dy_eq_dec_aux; eassumption. Qed.

Global Program Instance dy_eq_dec : ∀ (x y: Dyadic), Decision (x = y) := λ x y,
  if precedes_dec (expo x) (expo y) 
  then if equiv_dec (mant x) (mant y ≪ exist _ (expo y - expo x) _) then left _ else right _ 
  else if equiv_dec (mant x ≪ exist _ (expo x - expo y) _) (mant y) then left _ else right _.
Next Obligation. now apply rings.flip_nonneg_minus. Qed.
Next Obligation. eapply dy_eq_dec_aux; eauto. Qed.
Next Obligation. eapply dy_eq_dec_aux_neg; eauto. Qed.
Next Obligation. apply rings.flip_nonneg_minus. now apply orders.precedes_flip. Qed.
Next Obligation. symmetry. eapply dy_eq_dec_aux. symmetry. eassumption. Qed.
Next Obligation. apply not_symmetry. eapply dy_eq_dec_aux_neg. apply not_symmetry. eassumption. Qed.

Global Instance dy_pow `{!Pow Z (Z⁺)} : Pow Dyadic (Z⁺) := λ x n, (mant x) ^ n $ 'n * expo x.

Global Instance dy_pow_spec `{!NatPowSpec Z (Z⁺) pw} : NatPowSpec Dyadic (Z⁺) dy_pow.
Proof.
  split; unfold pow, dy_pow, equiv, dy_equiv, DtoQ_slow.
    intros [xm xe] [ym ye] E1 e1 e2 E2. simpl in *.
    rewrite E2. clear e1 E2.
    rewrite 2!(preserves_nat_pow (f:=ZtoStdQ)).
    rewrite 2!(commutativity ('e2 : Z)).
    rewrite 2!int_pow_exp_mult.
    rewrite 2!int_pow_nat_pow.
    rewrite <-2!nat_pow_base_mult.
    now rewrite E1.
   intros [xm xe]. simpl.
   rewrite rings.preserves_0, left_absorb.
   now rewrite nat_pow_0.
  intros [xm xe] n. simpl.
  rewrite nat_pow_S.
  rewrite rings.preserves_plus, rings.preserves_1.
  now rewrite distribute_r, left_identity.
Qed.

Global Instance dy_shiftl: ShiftL Dyadic Z := λ x n, mant x $ n + expo x.

Global Instance: ShiftLSpec Dyadic Z dy_shiftl.
Proof.
  split. 
    intros [xm xe] [ym ye] E1 n1 n2 E2. 
    unfold shiftl, dy_shiftl, equiv, dy_equiv, DtoQ_slow in *. simpl in *.
    rewrite 2!int_pow_exp_plus; try apply (ne_zero (2:StdQ)).
    transitivity (ZtoStdQ xm * 2 ^ xe * 2 ^ n1).
     ring.
    rewrite E1, E2. ring.
   intros [xm xe]. 
   unfold shiftl, dy_shiftl, equiv, dy_equiv, DtoQ_slow. simpl. 
   now rewrite left_identity.
  intros [xm xe] n. simpl.
  rewrite <-(rings.preserves_2 (f:=dy_inject)).
  unfold shiftl, dy_shiftl, equiv, dy_equiv, DtoQ_slow. simpl. 
  rewrite <-associativity, int_pow_S.
   rewrite rings.preserves_mult, rings.preserves_2.
   rewrite rings.plus_0_l. ring.
  apply (ne_zero (2:StdQ)).
Qed.

Global Instance dy_precedes: Order Dyadic := λ x y, DtoStdQ x ≤ DtoStdQ y.

Instance: Proper ((=) ==> (=) ==> iff) dy_precedes.
Proof.
  intros [x1m x1e] [y1m y1e] E1 [x2m x2e] [y2m y2e] E2. 
  unfold dy_precedes, equiv, dy_equiv, DtoQ_slow in *. simpl in *.
  now rewrite E1, E2.
Qed.

Instance: PartialOrder dy_precedes.
Proof.
  repeat (split; try apply _); unfold dy_precedes.
    intros x. reflexivity.
   intros x y z E1 E2. now transitivity (DtoStdQ y).
  intros x y E1 E2. 
  unfold dy_precedes, equiv, dy_equiv, DtoQ_slow in *. simpl in *.
  now apply (antisymmetry (≤)).
Qed.

Global Instance: TotalOrder dy_precedes.
Proof.
  intros x y. destruct (total_order (DtoStdQ x) (DtoStdQ y)); [left | right]; assumption.
Qed.

Global Instance: RingOrder dy_precedes.
Proof.
  repeat (split; try apply _); unfold "≤", dy_precedes.
   intros x y E.
   rewrite 2!DtoQ_slow_preserves_plus.
   now apply ringorder_plus.
  intros x E1 y E2.
  rewrite DtoQ_slow_preserves_0, DtoQ_slow_preserves_mult.
  apply ringorder_mult; now rewrite <-DtoQ_slow_preserves_0.
Qed.

Lemma nonneg_mant (x : Dyadic) : 0 ≤ x ↔ 0 ≤ mant x.
Proof.
  split; intros E.
   unfold precedes, dy_precedes, DtoQ_slow in E. simpl in *.
   apply (order_preserving_back ZtoStdQ).
   apply (maps.order_preserving_back_flip_gt_0 (.*.) (2 ^ (expo x))). 
    apply int_pow_pos. now apply semirings.sprecedes_0_2.
   unfold flip. now rewrite rings.preserves_0, left_absorb in E |- *.
  unfold precedes, dy_precedes, DtoQ_slow. simpl.
  apply (order_preserving ZtoStdQ) in E.
  apply (maps.order_preserving_flip_ge_0 (.*.) (2 ^ (expo x))) in E. 
   unfold flip in E. now rewrite rings.preserves_0, left_absorb in E |- *.
  apply int_pow_nonneg. now apply semirings.sprecedes_0_2.
Qed.

Lemma nonpos_mant (x : Dyadic) : x ≤ 0 ↔ mant x ≤ 0.
Proof.
  rewrite 2!rings.flip_nonpos_inv.
  apply nonneg_mant.
Qed.

Global Program Instance dy_abs `{!Abs Z} : Abs Dyadic := λ x, abs (mant x) $ expo x.
Next Obligation.
  split; intros E.
   rewrite abs_nonneg. 
    now destruct x.
   now apply nonneg_mant.
  rewrite abs_nonpos. 
   now destruct x.
  now apply nonpos_mant.
Qed.

Lemma dy_precedes_dec_aux (x y : Dyadic) p : 
  mant x ≤ mant y ≪ exist _ (expo y - expo x) p → x ≤ y.
Proof.
  destruct x as [xm xe], y as [ym ye].
  intros E. unfold precedes, dy_precedes, DtoQ_slow. simpl in *.
  apply (order_preserving ZtoStdQ) in E.
  rewrite ZtoQ_shift in E.
  unfold inject, NonNeg_inject in E. simpl in E.
  apply (maps.order_preserving_flip_ge_0 (.*.) (2 ^ xe)) in E. unfold flip in E.
   rewrite <-associativity, <-int_pow_exp_plus in E.
    now setoid_replace ((ye - xe) + xe) with ye in E by ring.
   now apply (ne_zero (2:StdQ)).
  apply int_pow_nonneg. 
  now apply semirings.precedes_0_2.
Qed.

Local Obligation Tactic := idtac.
Global Program Instance dy_precedes_dec : ∀ (x y: Dyadic), Decision (x ≤ y) := λ x y,
   if precedes_dec (expo x) (expo y) 
   then if precedes_dec (mant x) (mant y ≪ exist _ (expo y - expo x) _) then left _ else right _ 
   else if precedes_dec (mant x ≪ exist _ (expo x - expo y) _) (mant y) then left _ else right _.
Next Obligation. 
  intros. apply rings.flip_nonneg_minus. assumption. 
Qed.
Next Obligation. 
  intros x y E1 E2. eapply dy_precedes_dec_aux. eassumption.
Qed.
Next Obligation.
  intros x y E1 E2.
  apply orders.not_precedes_sprecedes.
  apply orders.not_precedes_sprecedes in E2. apply rings.flip_inv_strict in E2.
  destruct E2 as [E2a E2b]. split.
   apply rings.flip_inv.
   eapply dy_precedes_dec_aux.
   simpl. rewrite opp_shiftl. eassumption.
  intros E3. apply E2b. apply inv_proper.
  apply dy_eq_dec_aux. now symmetry.
Qed.
Next Obligation. 
  intros. apply rings.flip_nonneg_minus. now apply orders.precedes_flip.
Qed.
Next Obligation. 
  intros x y E1 E2. 
  apply orders.sprecedes_precedes in E2. destruct E2 as [E2 | E2].
   apply orders.equiv_precedes. symmetry in E2 |- *. 
   eapply dy_eq_dec_aux. eassumption.
  apply rings.flip_inv.
  eapply dy_precedes_dec_aux.
  simpl. rewrite opp_shiftl. apply (proj1 (rings.flip_inv _ _)). eapply E2.
Qed.
Next Obligation. 
  intros x y E1 E2.
  apply orders.not_precedes_sprecedes in E2. destruct E2 as [E2a E2b].
  apply orders.not_precedes_sprecedes. split.
   eapply dy_precedes_dec_aux. eassumption.
  eapply dy_eq_dec_aux_neg. eassumption.
Qed.

(** 
 * Embedding into the rationals
 If we already have a [Rationals] implementation [Q], then we can embed [Dyadic]
 into it. That is, we have an injective ring morphism [DtoQ : Dyadic → Q].
*)
Section DtoQ.
  Context `{Rationals Q} (ZtoQ: Z → Q) `{!SemiRing_Morphism (ZtoQ: Z → Q)}.

  Local Obligation Tactic := program_simpl.
  Program Definition DtoQ (x : Dyadic) : Q := 
    if precedes_dec 0 (expo x)
    then ZtoQ (mant x ≪ exist _ (expo x) _)
    else ZtoQ (mant x) // (ZtoQ (1 ≪ (exist _ (-expo x) _))).
  Next Obligation. 
    apply rings.flip_nonpos_inv.
    now apply orders.precedes_flip.
  Qed.
  Next Obligation.
    apply rings.injective_not_0.
    pose proof (shiftl_nonzero (A:=Z) (B:=Z⁺)) as P.
    apply P.
    apply (ne_zero 1).
  Qed.
End DtoQ.

Section two_rationals.
  Context Q1 `{Rationals Q1} `{!IntPowSpec Q1 Z ipw1} `{!SemiRing_Morphism (ZtoQ1 : Z → Q1)}.
  Context Q2 `{Rationals Q2} `{!IntPowSpec Q2 Z ipw2} `{!SemiRing_Morphism (ZtoQ2 : Z → Q2)}.

  Lemma equality_coincides_aux (x : Dyadic)  : 
    ZtoQ2 (mant x) * 2 ^ expo x = rationals_to_rationals Q1 Q2 (ZtoQ1 (mant x) * 2 ^ expo x).
  Proof.
    rewrite rings.preserves_mult, (preserves_int_pow 2), rings.preserves_2.
    now rewrite (integers.to_ring_unique_alt ZtoQ2 (rationals_to_rationals Q1 Q2 ∘ ZtoQ1)). 
  Qed.
End two_rationals.

Section embed_rationals.
  Context `{Rationals Q} `{!IntPowSpec Q Z ipw} `{!SemiRing_Morphism (ZtoQ: Z → Q)}.
  Context `{oQ : Order Q} `{!RingOrder oQ} `{!TotalOrder oQ}.

  Add Ring Q2 : (rings.stdlib_ring_theory Q).

  Notation DtoQ' := (DtoQ ZtoQ).
  Notation DtoQ_slow' := (DtoQ_slow ZtoQ).
  Notation QtoStdQ := (rationals_to_rationals Q StdQ).
  Notation StdQtoQ := (rationals_to_rationals StdQ Q).

  Instance: Proper ((=) ==> (=)) DtoQ_slow'.
  Proof.
    intros ? ? E.
    unfold equiv, dy_equiv in E. unfold DtoQ_slow in *.
    apply (injective QtoStdQ). 
    now rewrite 2!(equality_coincides_aux Q StdQ) in E.
  Qed.

  Global Instance: Injective DtoQ_slow'.
  Proof.
    repeat (split; try apply _).
    intros ? ? E.  
    unfold equiv, dy_equiv. unfold DtoQ_slow in *.
    apply (injective StdQtoQ).
    now rewrite <-2!(equality_coincides_aux StdQ Q).
  Qed.

  Lemma DtoQ_slow_correct x : DtoQ' x = DtoQ_slow' x.
  Proof.
    unfold DtoQ, DtoQ_slow.
    destruct x as [xm xe]. simpl. 
    case (precedes_dec 0 xe); intros E.
     now rewrite ZtoQ_shift.
    rewrite <-fields.dec_mult_inv_correct.
    rewrite int_pow_mult_inv_alt, ZtoQ_shift.
    now rewrite rings.preserves_1, left_identity.
  Qed.

  Instance: Proper ((=) ==> (=)) DtoQ'.
  Proof.
    intros x y E. rewrite 2!DtoQ_slow_correct.
    now rewrite E.
  Qed.

  Global Instance: Injective DtoQ'.
  Proof.
    repeat (split; try apply _).
    intros x y E.
    apply (injective DtoQ_slow').
    now rewrite <-2!DtoQ_slow_correct.
  Qed.

  Global Instance: SemiRing_Morphism DtoQ_slow'.
  Proof. 
    repeat (split; try apply _).
       exact DtoQ_slow_preserves_plus.
      exact DtoQ_slow_preserves_0.
     exact DtoQ_slow_preserves_mult.
    exact DtoQ_slow_preserves_1.
  Qed.

  Global Instance: SemiRing_Morphism DtoQ'.
  Proof.
    repeat (split; try apply _); intros; rewrite ?DtoQ_slow_correct.
       now apply DtoQ_slow_preserves_plus.
      now apply DtoQ_slow_preserves_0.
     now apply DtoQ_slow_preserves_mult.
    now  apply DtoQ_slow_preserves_1.
  Qed.

  Global Instance: OrderEmbedding DtoQ_slow'.
  Proof.
    repeat (split; try apply _); unfold "≤", dy_precedes, DtoQ_slow; intros x y E.
     apply (order_preserving StdQtoQ) in E.
     now rewrite <-2!(equality_coincides_aux StdQ Q) in E.
    apply (order_preserving QtoStdQ) in E.
    now rewrite 2!(equality_coincides_aux Q StdQ).
  Qed.

  Global Instance: OrderEmbedding DtoQ'.
  Proof with trivial.
    repeat (split; try apply _).
     intros. rewrite 2!DtoQ_slow_correct. now apply (order_preserving DtoQ_slow').
    intros. apply (order_preserving_back DtoQ_slow'). now rewrite <-2!DtoQ_slow_correct.
  Qed.
End embed_rationals.
  
End dyadics.
