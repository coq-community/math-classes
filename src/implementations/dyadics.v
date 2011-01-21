(** 
  The dyadic rationals are numbers of the shape [m * 2 ^ e] with [m : Z] and [e : Z] 
   for some [Integers] implementation [Z]. These numbers form a ring and can be 
   embedded into any [Rationals] implementation [Q]. 
*)

Require
  theory.integers theory.rings theory.fields theory.rationals.
Require Import
  Morphisms Ring Program RelationClasses Setoid
  abstract_algebra 
  interfaces.integers interfaces.naturals interfaces.rationals
  interfaces.additional_operations
  orders.minmax orders.integers orders.rationals
  nonneg_integers_naturals 
  theory.cut_minus theory.bit_shift theory.int_pow theory.nat_pow theory.abs. 

Record Dyadic Z := dyadic { mant: Z; expo: Z }.
Implicit Arguments dyadic [[Z]].
Implicit Arguments mant [[Z]].
Implicit Arguments expo [[Z]].

Infix "$" := dyadic (at level 80).

Section dyadics.
  Context `{Integers Z} `{!RingOrder oZ} `{!TotalOrder oZ}
    `{equiv_dec : ∀ (x y : Z), Decision (x = y)}  
    `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)}
    `{!NatPow Z (Z⁺)} 
    `{!ShiftLeft Z (Z⁺)}.

  Add Ring Z: (rings.stdlib_ring_theory Z).
  Notation Dyadic := (Dyadic Z).

  (* To speed up instance resolution we declare the following (duplicate) instances with a high priority. *)
  Instance: SemiRing (Z⁺) | 1.
  Instance: Proper ((=) ==> (=) ==> (=)) (@ring_plus (Z⁺) _) | 1. Proof. apply _. Qed.
  Instance: Proper ((=) ==> (=) ==> (=)) (@ring_mult (Z⁺) _) | 1. Proof. apply _. Qed.
  Instance: Proper ((=) ==> (=) ==> (=)) (∸) | 1. Proof. apply _. Qed.
  Instance: Proper ((=) ==> (=) ==> (=)) (≪) | 1. Proof. apply _. Qed.
  Instance: NeZero (2 : Z) | 1. Proof. apply _. Qed.

  Hint Resolve (@orders.precedes_flip Z _ _ _ _).

  (* Dirty hack to avoid having sigma times all over *)
  Program Let cut_minus_NonNeg (x y : Z) : Z⁺ := exist _ (x ∸ y) _.
  Next Obligation. apply cut_minus_nonneg. Qed.

  Infix "--" := cut_minus_NonNeg (at level 50, left associativity).

  Ltac unfold_cut_minus := unfold equiv, NonNeg_equiv, inject, NonNeg_inject, cut_minus_NonNeg; simpl.

  Instance: Proper ((=) ==> (=) ==> (=)) cut_minus_NonNeg.
  Proof. intros x1 x2 E y1 y2 F. unfold_cut_minus. apply cut_minus_proper; auto. Qed.

  Lemma shiftl_cut_minus_0 {x y n : Z} : x ≤ y → n ≪ (x -- y) = n.
  Proof. 
    intros. assert (x -- y = 0) as E. unfold_cut_minus. apply cut_minus_0. assumption.
    rewrite E. apply right_identity.
  Qed.

  (** * Equality *)
  Global Instance dy_eq: Equiv Dyadic := λ x y,
    mant x ≪ (expo x -- expo y) = mant y ≪ (expo y -- expo x).

  Instance: Reflexive dy_eq.
  Proof. intro. unfold dy_eq. reflexivity. Qed.

  Instance: Symmetric dy_eq.
  Proof. intros x y E. unfold dy_eq in *. symmetry. assumption. Qed.

  Instance: Transitive dy_eq.
  Proof with eauto; try reflexivity.
    intros [xm xe] [ym ye] [zm ze] E1 E2. unfold dy_eq in *. simpl in *.
    destruct (total_order xe ye) as [F|F];
      rewrite (shiftl_cut_minus_0 F) in E1;
      destruct (total_order ye ze) as [G|G];
      rewrite (shiftl_cut_minus_0 G) in E2... 
       (* expo x ≤ expo y, expo y ≤ expo z *)
       rewrite E1, E2. repeat rewrite <-shiftl_sum_exp.
       apply shiftl_proper... unfold_cut_minus.
       rewrite (cut_minus_0 xe). ring_simplify. 
       apply cut_minus_precedes_trans... 
       transitivity ye...
      (* expo x ≤ expo y, expo y ≤ expo z *)
      rewrite E1, <-E2. repeat rewrite <-shiftl_sum_exp. 
      apply shiftl_proper... unfold_cut_minus. 
      apply cut_minus_plus_toggle1...
     (* expo y ≤ expo x, expo y ≤ expo z *)
     apply (shiftl_inj (xe -- ye))... unfold flip.
     rewrite shiftl_order, E1, E2. repeat rewrite <-shiftl_sum_exp. 
     apply shiftl_proper... unfold_cut_minus. 
     rewrite commutativity. apply cut_minus_plus_toggle2...
    (* expo y ≤ expo x, expo z ≤ expo y *)
    rewrite <-E2, <-E1. repeat rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus.
    rewrite (cut_minus_0 ze). ring_simplify. 
    symmetry. apply cut_minus_precedes_trans... 
    transitivity ye...
  Qed.
  
  Instance: Equivalence dy_eq.
  Instance: Setoid Dyadic.

  (* Equalitity is decidable *)
  Lemma dy_eq_dec_aux (x y : Dyadic) p : 
    mant x = mant y ≪ exist _ (expo y - expo x) p ↔ x = y.
  Proof with auto.
    destruct x as [xm xe], y as [ym ye].
    assert (xe ≤ ye).
     apply rings.flip_nonneg_minus...
    split; intros E. 
     unfold equiv, dy_eq.
     rewrite E, <-shiftl_sum_exp.
     apply shiftl_proper. reflexivity.
     unfold_cut_minus.
     rewrite cut_minus_0, cut_minus_ring_minus...
     ring. 
    unfold equiv, dy_eq in E.
    apply (shiftl_inj (xe -- ye)). unfold flip.
    rewrite E, <-shiftl_sum_exp.
    apply shiftl_proper. reflexivity.
    unfold_cut_minus.
    rewrite (cut_minus_0 xe ye), (cut_minus_ring_minus ye xe)...
    ring.
  Qed.

   Lemma dy_eq_dec_aux_neg (x y : Dyadic) p : 
     mant x ≠ mant y ≪ exist _ (expo y - expo x) p ↔ x ≠ y.
   Proof. split; intros E; intro; apply E; eapply dy_eq_dec_aux; eassumption. Qed.

   Global Program Instance dy_eq_dec : ∀ (x y: Dyadic), Decision (x = y) := λ x y,
     if precedes_dec (expo x) (expo y) 
     then if equiv_dec (mant x) (mant y ≪ exist _ (expo y - expo x) _) then left _ else right _ 
     else if equiv_dec (mant x ≪ exist _ (expo x - expo y) _) (mant y) then left _ else right _.
  Next Obligation. apply rings.flip_nonneg_minus. assumption. Qed.
  Next Obligation. eapply dy_eq_dec_aux; eauto. Qed.
  Next Obligation. eapply dy_eq_dec_aux_neg; eauto. Qed.
  Next Obligation. apply rings.flip_nonneg_minus. auto. Qed.
  Next Obligation. symmetry. eapply dy_eq_dec_aux. symmetry. eassumption. Qed.
  Next Obligation. apply not_symmetry. eapply dy_eq_dec_aux_neg. apply not_symmetry. eassumption. Qed.

  Instance dyadic_proper: Proper ((=) ==> (=) ==> (=)) dyadic.
  Proof.
    intros ? ? E1 ? ? E2.
    unfold equiv, dy_eq. simpl.
    rewrite E1, E2. reflexivity.
  Qed.

  (** * Basic operations *)
  Global Program Instance dy_plus: RingPlus Dyadic := λ x y, 
    if precedes_dec (expo x) (expo y)
    then mant x + (mant y ≪ exist _ (expo y - expo x) _) $ min (expo x) (expo y)
    else (mant x ≪ exist _ (expo x - expo y) _) + mant y $ min (expo x) (expo y).
  Next Obligation. apply rings.flip_nonneg_minus. assumption. Qed.
  Next Obligation. apply rings.flip_nonneg_minus. auto. Qed.

  (* The following plus function is less efficient, because it involves computing [decide (expo x ≤ expo y)] twice.
    Yet, it is much more convinient to reason with. *)
  Definition dy_plus_slow (x y : Dyadic) : Dyadic := 
    mant x ≪ (expo x -- expo y) + mant y ≪ (expo y -- expo x) $ min (expo x) (expo y).
  
  Lemma dy_plus_slow_correct x y : dy_plus x y = dy_plus_slow x y.
  Proof with auto; try reflexivity.
    unfold dy_plus, dy_plus_slow.
    case (precedes_dec (expo x) (expo y)); intros E; 
      apply dyadic_proper;
      try apply sg_mor;
      try apply shiftl_proper...
       symmetry. apply shiftl_cut_minus_0...
      unfold_cut_minus. rewrite cut_minus_ring_minus...
     unfold_cut_minus. rewrite cut_minus_ring_minus... 
    symmetry. apply shiftl_cut_minus_0...
  Qed.

  Global Instance dy_opp: GroupInv Dyadic := λ x, -mant x $ expo x.
  Global Instance dy_mult: RingMult Dyadic := λ x y, mant x * mant y $ expo x + expo y.
  Global Instance dy_0: RingZero Dyadic := 0 $ 0.
  Global Instance dy_1: RingOne Dyadic := 1 $ 0.

  (* * General properties *)
  Lemma nonzero_mant x : x ≠ 0 ↔ mant x ≠ 0.
  Proof.
    destruct x as [xm xe].
    split; intros E F; apply E.
     unfold equiv, dy_eq. simpl in *.
     rewrite F. do 2 rewrite left_absorb. reflexivity.
    unfold equiv, dy_eq in F. simpl in *.
    rewrite left_absorb in F.
    apply stable; intros G. 
    apply (shiftl_nonzero xm (xe -- 0)); assumption.
  Qed.

  Lemma dy_plus_proper_aux n m x1 x2 y1 y2 : n ≪ (x1 -- y1) = m ≪ (y1 --x1) → 
    n ≪ (x1 -- x2 + (min x1 x2 -- min y1 y2)) = m ≪ (y1 -- y2 + (min y1 y2 -- min x1 x2)).
  Proof with auto; try reflexivity.
    intros E.
    apply (shiftl_inj (x1 -- y1)). unfold flip. 
    rewrite shiftl_order. rewrite E. 
    repeat rewrite <-shiftl_sum_exp. apply shiftl_proper...
    unfold_cut_minus.
    apply cut_minus_min4.
  Qed.

  (* * Properties of plus *)
  Instance dy_plus_slow_proper: Proper ((=) ==> (=) ==> (=)) dy_plus_slow.
  Proof with auto; try reflexivity.
    intros [x1m x1e] [y1m y1e] E1 [x2m x2e] [y2m y2e] E2.
    unfold equiv, dy_eq, dy_plus_slow in *. simpl in *.
    do 2 rewrite shiftl_sum_base. 
    repeat rewrite <-shiftl_sum_exp.
    apply sg_mor. 
     apply dy_plus_proper_aux...
    rewrite (commutativity y1e y2e), (commutativity x1e x2e).
    apply dy_plus_proper_aux...
  Qed.

  Instance dy_plus_proper: Proper ((=) ==> (=) ==> (=)) dy_plus.
  Proof.
    intros ? ? E1 ? ? E2. 
    do 2 rewrite dy_plus_slow_correct.
    apply dy_plus_slow_proper; assumption.
  Qed.

  Instance: Associative dy_plus.
  Proof with auto; try reflexivity; try ring.
    intros [xm xe] [ym ye] [zm ze]. do 4 rewrite dy_plus_slow_correct. 
    unfold equiv, dy_eq, dy_plus_slow. simpl. 
    apply shiftl_proper.
     repeat rewrite shiftl_sum_base. 
     repeat rewrite <-shiftl_sum_exp. 
     rewrite associativity.
     repeat apply sg_mor; apply shiftl_proper; unfold_cut_minus...
       apply cut_minus_min1.
      apply cut_minus_min2.
     rewrite (commutativity ye ze), (commutativity xe ye).
     symmetry. apply cut_minus_min1.
    rewrite associativity...
  Qed.

  Instance: Commutative dy_plus.
  Proof with auto; try reflexivity. 
    intros [xm xe] [ym ye]. do 2 rewrite dy_plus_slow_correct.
    unfold dy_plus, equiv, dy_eq. simpl.
    apply shiftl_proper...
     apply commutativity...
    rewrite commutativity...
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_plus).

  Lemma dyadic_left_identity (x : Dyadic) : 0 + x = x.
  Proof with auto; try reflexivity.
    destruct x as [xm xe]. rewrite dy_plus_slow_correct.
    unfold equiv, dy_eq, sg_op, dy_plus_slow. simpl.
    rewrite left_absorb, left_identity. 
    rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus.
    destruct (total_order xe 0) as [F|F].
     rewrite min_r... 
     rewrite cut_minus_rightabsorb... ring.
    rewrite min_l... 
    rewrite cut_minus_leftabsorb... ring.
  Qed.

  Program Instance: Monoid Dyadic (op:=dy_plus) (unit:=dy_0).
  Next Obligation. repeat intro. apply dyadic_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_left_identity. Qed.
  
  (* * Properties of opp *)
  Instance: Proper ((=) ==> (=)) dy_opp.
  Proof.
    intros [xm xe] [ym ye] E.
    unfold equiv, dy_eq, dy_opp in *. simpl in *.
    do 2 rewrite opp_shiftl.
    rewrite E. reflexivity.
  Qed.

  Lemma dyadic_ginv (x : Dyadic) : - x + x = 0.
  Proof.
    destruct x as [xm xe]. rewrite dy_plus_slow_correct.
    unfold equiv, dy_eq, sg_op, dy_plus_slow. simpl.
    rewrite left_absorb. rewrite shiftl_sum_base. 
    do 2 rewrite <-shiftl_sum_exp.
    rewrite opp_shiftl. ring.
  Qed.

  Program Instance: Group Dyadic.
  Next Obligation. apply dyadic_ginv. Qed.
  Next Obligation. rewrite commutativity. apply dyadic_ginv. Qed.

  Program Instance: AbGroup Dyadic.
  
  (* * Properties of mult *)
  Instance: Proper ((=) ==> (=) ==> (=)) dy_mult.
  Proof with auto; try reflexivity.
    intros [x1m x1e] [y1m y1e] E1 [x2m x2e] [y2m y2e] E2.
    unfold equiv, dy_eq, dy_mult in *. simpl in *. 
    destruct (total_order x1e y1e) as [F|F];
      destruct (total_order x2e y2e) as [G|G];
      rewrite (shiftl_cut_minus_0 F) in E1; 
      rewrite (shiftl_cut_minus_0 G) in E2...
       (* expo x ≤ expo y, expo y ≤ expo z *)
       rewrite E1, E2. 
       rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
       apply shiftl_proper... unfold_cut_minus. 
       rewrite (cut_minus_0 (x1e + x2e)). ring_simplify.
       apply cut_minus_plus_distr...
       apply semirings.plus_compat...
      (* expo x ≤ expo y, expo y ≤ expo z *)
      rewrite E1, <-E2. 
      rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
      apply shiftl_proper... unfold_cut_minus. 
      apply cut_minus_plus_toggle3...
     (* expo y ≤ expo x, expo y ≤ expo z *)
     rewrite <-E1, E2. 
     rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
     apply shiftl_proper... unfold_cut_minus. 
     symmetry. apply cut_minus_plus_toggle3...
     (* expo y ≤ expo x, expo z ≤ expo y *)
    rewrite <-E2, <-E1. 
    rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
    apply shiftl_proper... unfold_cut_minus.
    rewrite (cut_minus_0 (y1e + y2e)). ring_simplify.
    symmetry. apply cut_minus_plus_distr...
    apply semirings.plus_compat...
  Qed.

  Instance: Associative dy_mult.
  Proof.
    intros [xm xe] [ym ye] [zm ze].
    unfold ring_mult, dy_mult, equiv, dy_eq. simpl.
    apply shiftl_proper. ring. unfold_cut_minus. 
    apply cut_minus_proper; ring. 
  Qed.

  Instance: Commutative dy_mult.
  Proof.
    intros [xm xe] [ym ye]. 
    unfold ring_mult, dy_mult, equiv, dy_eq. simpl.
    apply shiftl_proper. ring. unfold_cut_minus. 
    apply cut_minus_proper; ring. 
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_mult).

  Lemma dyadic_mult_left_identity (x : Dyadic) : 1 * x = x.
  Proof.
    destruct x as [xm xe].
    unfold equiv, dy_eq, dy_mult. simpl.
    do 2 rewrite left_identity. reflexivity.
  Qed.

  Program Instance: Monoid Dyadic (op:=dy_mult) (unit:=dy_1).
  Next Obligation. repeat intro. apply dyadic_mult_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_mult_left_identity. Qed.

  Instance: CommutativeMonoid Dyadic (op:=dy_mult) (unit:=dy_1).

  Lemma dyadic_distr_l (x y z : Dyadic) : x * (y + z) = (x * y) + (x * z).
  Proof with auto; try reflexivity.
    destruct x as [xm xe], y as [ym ye], z as [zm ze].
    do 2 rewrite dy_plus_slow_correct.
    unfold equiv, dy_eq, dy_mult, dy_plus_slow. simpl.
    apply shiftl_proper...
     do 2 rewrite <-mult_shiftl.
     rewrite <-distribute_l. repeat apply sg_mor...
      apply shiftl_proper... unfold_cut_minus. apply cut_minus_plus_l_rev.
     apply shiftl_proper... unfold_cut_minus. apply cut_minus_plus_l_rev.
    unfold_cut_minus. apply cut_minus_min3.
  Qed.

  Instance: Distribute dy_mult dy_plus.
  Proof with try reflexivity.
    split; intros x y z.
    apply dyadic_distr_l.
    rewrite commutativity, (commutativity x z), (commutativity y z).
    apply dyadic_distr_l.
  Qed.

  Global Instance: Ring Dyadic.

  Global Program Instance dy_nat_pow: NatPow (Dyadic) (Z⁺) := λ x n,
    (mant x) ^ n $ 'n * expo x.
  Next Obligation with auto; try reflexivity.
    change (nat_pow_spec x n ((λ x n, mant x ^ n $ ' n * expo x) x n)).
    apply nat_pow_spec_from_properties.
      intros x1 y1 E1 x2 y2 E2. rewrite E2. clear x n x2 E2.
      assert (∀ a b, expo a ≤ expo b → a = b 
         → (mant a ^ y2 $ ' y2 * expo a) = (mant b ^ y2 $ ' y2 * expo b)).
       unfold equiv, dy_eq in E1 |- *. simpl.
       intros [am ae] [bm be] E F. destruct y1 as [ym ye]. simpl in *.
       rewrite shiftl_cut_minus_0, shiftl_correct in F...
       rewrite shiftl_cut_minus_0, shiftl_correct.
        rewrite F, nat_pow_base_mult, <-nat_pow_exp_mult.
        apply sg_mor... apply nat_pow_proper...
        unfold_cut_minus.
        rewrite commutativity.
        apply cut_minus_mult_distr_l. destruct y2...
       apply semirings.mult_compat... destruct y2...
      destruct (total_order (expo x1) (expo y1))...
      symmetry in E1 |- *...
     intros [xm xe]. simpl.
     rewrite nat_pow_0, rings.preserves_0, left_absorb...
    intros [xm xe] m. simpl.
    rewrite nat_pow_S.
    rewrite rings.preserves_plus, rings.preserves_1.
    rewrite distribute_r, left_identity...
  Qed.

  (** 
   * Embedding into the rationals
   If we already have a [Rationals] implementation [Q], then we can embed [Dyadic]
   into it. That is, we have an injective ring morphism [DtoQ : Dyadic → Q].
  *)
  Context `{Rationals Q} `{!SemiRing_Morphism (ZtoQ: Z → Q)}.
  Add Ring Q: (rings.stdlib_ring_theory Q).

  Lemma ZtoQ_shift (x : Z) (n : Z⁺) : ZtoQ (x ≪ n) = ZtoQ x * 2 ^ ('n : Z).
  Proof.
    rewrite shiftl_correct.
    rewrite rings.preserves_mult, nat_pow.preserves_nat_pow, rings.preserves_2.
    rewrite <-int_pow_nat_pow.
    rewrite <-(naturals.to_semiring_unique NonNeg_inject).
    reflexivity.
  Qed.

  Definition DtoQ_slow (x : Dyadic) : Q := ZtoQ (mant x) * 2 ^ (expo x).

  Global Instance: Proper ((=) ==> (=)) DtoQ_slow.
  Proof with auto; try reflexivity.
    assert (∀ x y, expo x ≤ expo y → x = y → DtoQ_slow x = DtoQ_slow y).
     intros [xm xe] [ym ye] E F.
     unfold DtoQ_slow in *. unfold equiv, dy_eq in F. simpl in *.
     rewrite (shiftl_cut_minus_0 E) in F.
     rewrite F. rewrite ZtoQ_shift.
     unfold inject, NonNeg_inject, cut_minus_NonNeg. simpl.
     rewrite <-associativity, <-int_pow_exp_sum.
      rewrite cut_minus_precedes...
     apply (ne_zero (2:Q)).
    intros x y F.
    destruct (total_order (expo x) (expo y))...
    symmetry in F |- *...
  Qed.

  Lemma DtoQ_slow_preserves_plus x y : DtoQ_slow (x + y) = DtoQ_slow x + DtoQ_slow y.
  Proof with auto.
    assert (∀ x y, expo x ≤ expo y → DtoQ_slow (x + y) = DtoQ_slow x + DtoQ_slow y).
     intros [xm xe] [ym ye] E.
     unfold ring_plus at 1. rewrite dy_plus_slow_correct. 
     unfold dy_plus_slow, DtoQ_slow. simpl in *.
     rewrite shiftl_cut_minus_0...
     rewrite rings.preserves_plus. rewrite ZtoQ_shift.
     unfold inject, NonNeg_inject. simpl.
     rewrite min_l...
     ring_simplify.
     rewrite <-associativity, <-int_pow_exp_sum.
      rewrite cut_minus_precedes... reflexivity.
     apply (ne_zero (2:Q)).
    destruct (total_order (expo x) (expo y)) as [E|E]...
    rewrite commutativity, (commutativity (DtoQ_slow x))...
  Qed.
  
  Lemma DtoQ_slow_preserves_0 : DtoQ_slow 0 = 0.
  Proof. 
    unfold DtoQ_slow. simpl.
    rewrite rings.preserves_0. ring.
  Qed.

  Lemma DtoQ_slow_preserves_mult x y : DtoQ_slow (x * y) = DtoQ_slow x * DtoQ_slow y.
  Proof with auto; try reflexivity.
    unfold ring_mult at 1. unfold dy_mult at 1. unfold DtoQ_slow. simpl.
    destruct x as [xn xe], y as [yn ye]. simpl.
    rewrite rings.preserves_mult.
    rewrite int_pow_exp_sum. ring.
    apply (ne_zero (2:Q)).
  Qed. 

  Lemma DtoQ_slow_preserves_1 : DtoQ_slow 1 = 1.
  Proof.
    unfold DtoQ_slow. simpl.
    rewrite int_pow_0, rings.preserves_1. ring. 
  Qed.

  Global Instance: SemiRing_Morphism DtoQ_slow.
  Proof. 
    repeat (split; try apply _).
       apply DtoQ_slow_preserves_plus.
      apply DtoQ_slow_preserves_0.
     apply DtoQ_slow_preserves_mult.
    apply DtoQ_slow_preserves_1.
  Qed.

  Global Instance: Injective DtoQ_slow.
  Proof with auto.
    split; try apply _.
    assert (∀ x y, expo x ≤ expo y → DtoQ_slow x = DtoQ_slow y → x = y).
     intros [xm xe] [ym ye] E F.
     unfold equiv, dy_eq. 
     unfold DtoQ_slow in F. simpl in *.
     apply (injective ZtoQ).
     rewrite shiftl_cut_minus_0...
     rewrite ZtoQ_shift.
     apply (rings.right_cancellation_ne_0 (.*.) (2 ^ xe)).
      apply int_pow_nonzero.
      apply (ne_zero (2 : Q)).
     unfold inject, NonNeg_inject. simpl.
     rewrite <-associativity, <-int_pow_exp_sum.
     rewrite cut_minus_precedes... 
     apply (ne_zero (2:Q)).
     intros x y F.
     destruct (total_order (expo x) (expo y)) as [E|E]...
     symmetry in F |- *...
  Qed.

  Program Definition DtoQ (x : Dyadic) : Q := 
    if precedes_dec 0 (expo x)
    then ZtoQ (mant x ≪ exist _ (expo x) _)
    else ZtoQ (mant x) // (ZtoQ (1 ≪ (exist _ (-expo x) _))).
  Next Obligation. 
    apply rings.flip_nonpos_inv.
    apply orders.precedes_flip. assumption.
  Qed.
  Next Obligation.
    apply rings.injective_not_0.
    apply (shiftl_nonzero (1:Z)).
    apply (ne_zero 1).
  Qed.

  Lemma DtoQ_slow_correct x : DtoQ x = DtoQ_slow x.
  Proof with auto; try reflexivity.
    unfold DtoQ, DtoQ_slow.
    destruct x as [xm xe]. simpl. 
    case (precedes_dec 0 xe); intros E.
     rewrite ZtoQ_shift...
    apply sg_mor...
    rewrite <-fields.dec_mult_inv_correct.
    rewrite int_pow_mult_inv_alt.
    apply fields.dec_mult_inv_proper.
    rewrite ZtoQ_shift...
    rewrite rings.preserves_1, left_identity. reflexivity.
  Qed.

  Global Instance: Proper ((=) ==> (=)) DtoQ.
  Proof.
    intros x y E. do 2 rewrite DtoQ_slow_correct.
    rewrite E. reflexivity.
  Qed.

  Global Instance: SemiRing_Morphism DtoQ.
  Proof.
    repeat (split; try apply _); intros; repeat rewrite DtoQ_slow_correct.
       apply DtoQ_slow_preserves_plus.
      apply DtoQ_slow_preserves_0.
     apply DtoQ_slow_preserves_mult.
    apply DtoQ_slow_preserves_1.
  Qed.

  Global Instance: Injective DtoQ.
  Proof with auto.
    split; try apply _.
    intros x y E.
    apply (injective DtoQ_slow).
    do 2 rewrite <-DtoQ_slow_correct. assumption.
  Qed.

  Context `{oQ : Order Q} `{!RingOrder oQ} `{!TotalOrder oQ}.
  
  (* Although the order on the dyadics can be defined without a dependency of [Q], we don't bother doing that right now. *)
  Global Instance dy_precedes: Order Dyadic := λ x y, DtoQ_slow x ≤ DtoQ_slow y.
  
  Instance: Proper ((=) ==> (=) ==> iff) dy_precedes.
  Proof.
    intros ? ? E1 ? ? E2. unfold dy_precedes. rewrite E1, E2. reflexivity.
  Qed.

  Instance: PartialOrder dy_precedes.
  Proof with trivial.
    repeat (split; try apply _); unfold dy_precedes.
      intros x. reflexivity.
     intros x y z E1 E2. transitivity (DtoQ_slow y)...
    intros x y E1 E2. apply (injective DtoQ_slow). apply (antisymmetry (≤))...
  Qed.

  Global Instance: OrderEmbedding DtoQ_slow.
  Proof.
    repeat (split; try apply _); unfold "≤", dy_precedes; trivial.
  Qed.

  Global Instance: OrderEmbedding DtoQ.
  Proof with trivial.
    repeat (split; try apply _).
     intros. do 2 rewrite DtoQ_slow_correct. apply (order_preserving DtoQ_slow)...
    intros. apply (order_preserving_back DtoQ_slow). do 2 rewrite <-DtoQ_slow_correct...
  Qed.

  Global Instance: TotalOrder dy_precedes.
  Proof with trivial.
    intros x y. destruct (total_order (DtoQ_slow x) (DtoQ_slow y)); [left | right]...
  Qed.

  Global Instance: RingOrder dy_precedes.
  Proof with trivial.
    repeat (split; try apply _).
     intros x y E.
     apply (order_preserving_back DtoQ_slow). 
     do 2 rewrite rings.preserves_plus.
     apply ringorder_plus...
    intros x E1 y E2.
    apply (order_preserving_back DtoQ_slow). 
    rewrite rings.preserves_0, rings.preserves_mult.
    apply ringorder_mult; rewrite <-(rings.preserves_0 (f:=DtoQ_slow))...
  Qed.

  Lemma nonneg_mant (x : Dyadic) : 0 ≤ x ↔ 0 ≤ mant x.
  Proof with auto.
    split; intros E.
     unfold precedes, dy_precedes, DtoQ_slow in E. simpl in *.
     apply (order_preserving_back ZtoQ).
     apply (maps.order_preserving_back_flip_gt_0 (.*.) (2 ^ (expo x))). 
      apply int_pow_nonneg. apply semirings.sprecedes_0_2.
     unfold flip. rewrite rings.preserves_0, left_absorb in E |- *...
    unfold precedes, dy_precedes, DtoQ_slow. simpl.
    apply (order_preserving ZtoQ) in E.
    apply (maps.order_preserving_flip_ge_0 (.*.) (2 ^ (expo x))) in E. 
     unfold flip in E. rewrite rings.preserves_0, left_absorb in E |- *...
    apply int_pow_nonneg. apply semirings.sprecedes_0_2.
  Qed.

  Lemma nonpos_mant (x : Dyadic) : x ≤ 0 ↔ mant x ≤ 0.
  Proof with auto.
    split; intros E.
     apply rings.flip_nonpos_inv, nonneg_mant in E.
     apply rings.flip_nonpos_inv...
    apply rings.flip_nonpos_inv, nonneg_mant.
    apply rings.flip_nonpos_inv in E...
  Qed.

  Global Program Instance dy_abs `{!Abs Z} : Abs Dyadic := λ x, abs (mant x) $ expo x.
  Next Obligation with auto; try reflexivity.
    split; intros E.
     rewrite abs_nonneg. 
      destruct x...
     apply nonneg_mant...
     rewrite abs_nonpos. 
     destruct x...
    apply nonpos_mant...
  Qed.

  Lemma dy_precedes_dec_aux (x y : Dyadic) p : 
    mant x ≤ mant y ≪ exist _ (expo y - expo x) p → x ≤ y.
  Proof with auto.
    destruct x as [xm xe], y as [ym ye].
    intros E. unfold precedes, dy_precedes, DtoQ_slow. simpl in *.
    apply (order_preserving ZtoQ) in E.
    rewrite ZtoQ_shift in E.
    setoid_replace ye with ((ye - xe) + xe) by ring.
    rewrite int_pow_exp_sum.
     rewrite associativity. 
     apply (maps.order_preserving_flip_ge_0 (.*.) (2 ^  xe))...
     apply int_pow_nonneg. apply semirings.sprecedes_0_2.
    apply (ne_zero (2:Q)).
  Qed.

  Local Obligation Tactic := idtac.
  Global Program Instance dy_precedes_dec : ∀ (x y: Dyadic), Decision (x ≤ y) := λ x y,
     if precedes_dec (expo x) (expo y) 
     then if precedes_dec (mant x) (mant y ≪ exist _ (expo y - expo x) _) then left _ else right _ 
     else if precedes_dec (mant x ≪ exist _ (expo x - expo y) _) (mant y) then left _ else right _.
  Next Obligation. intros. apply rings.flip_nonneg_minus. assumption. Qed.
  Next Obligation with eassumption. 
    intros x y E1 E2. eapply dy_precedes_dec_aux... 
  Qed.
  Next Obligation with eassumption.
    intros x y E1 E2.
    apply orders.not_precedes_sprecedes.
    apply orders.not_precedes_sprecedes in E2. apply rings.flip_inv_strict in E2.
    destruct E2 as [E2a E2b]. split.
     apply rings.flip_inv.
     eapply dy_precedes_dec_aux.
     simpl. rewrite opp_shiftl...
    intros E3. apply E2b. apply inv_proper.
    apply dy_eq_dec_aux. symmetry...
  Qed.
  Next Obligation. intros. apply rings.flip_nonneg_minus. auto. Qed.
  Next Obligation with eassumption. 
    intros x y E1 E2. 
    apply orders.sprecedes_precedes in E2. destruct E2 as [E2 | E2].
     apply orders.equiv_precedes. symmetry in E2 |- *. eapply dy_eq_dec_aux...
    apply rings.flip_inv.
    eapply dy_precedes_dec_aux.
    simpl. rewrite opp_shiftl. apply (proj1 (rings.flip_inv _ _)). eapply E2.
  Qed.
  Next Obligation with eassumption. 
    intros x y E1 E2.
    apply orders.not_precedes_sprecedes in E2. destruct E2 as [E2a E2b].
    apply orders.not_precedes_sprecedes. split.
     eapply dy_precedes_dec_aux... 
    eapply dy_eq_dec_aux_neg...
  Qed.
End dyadics.
