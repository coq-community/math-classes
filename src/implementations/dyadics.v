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
  theory.cut_minus theory.bit_shift orders.minmax
  positive_integers_naturals.

Record Dyadic Z := dyadic { mant: Z; expo: Z }.
Implicit Arguments dyadic [[Z]].
Implicit Arguments mant [[Z]].
Implicit Arguments expo [[Z]].

Infix "$" := dyadic (at level 80).
Instance: Params (@dyadic) 2.

Section dyadics.
  Context `{Integers Z}.
  Add Ring Z: (rings.stdlib_ring_theory Z).

  Context `{equiv_dec : ∀ (x y : Z), Decision (x = y)}  
    `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)}
    `{!NatPow Z (Pos Z)} 
    `{!ShiftLeft Z (Pos Z)}
    `{!RingMinus Z}.

  Let Dyadic := Dyadic Z.

  Instance: Proper ((=) ==> (=) ==> (=)) (∸). Proof. apply _. Qed.

  Hint Resolve (@orders.precedes_flip Z _ _ _ _).

  (* Dirty hack to avoid having sigma times all over *)
  Program Let cut_minus_ZPos (x y : Z) : Pos Z := exist _ (x ∸ y) _.
  Next Obligation. apply cut_minus_positive. Qed.
  Infix "--" := cut_minus_ZPos (at level 50, left associativity).

  Ltac unfold_cut_minus := unfold equiv, ZPos_equiv, cut_minus_ZPos; simpl.

  Instance: Proper ((=) ==> (=) ==> (=)) cut_minus_ZPos.
  Proof. intros x1 x2 E y1 y2 F. unfold_cut_minus. apply cut_minus_proper; auto. Qed.

  Lemma shiftl_cut_minus_0 {x y n} : x ≤ y → n ≪ (x -- y) = n.
  Proof. 
    intros. assert (x -- y = 0) as E. unfold_cut_minus. apply cut_minus_0. assumption.
    rewrite E. apply right_identity.
  Qed.

  (** * Equality *)
  Global Instance dy_eq: Equiv Dyadic := λ x y,
    mant x ≪ (expo x -- expo y) = mant y ≪ (expo y -- expo x).

  Instance: Reflexive dy_eq.
  Proof.
    intro. unfold equiv, dy_eq. reflexivity.
  Qed.

  Instance: Symmetric dy_eq.
  Proof.
    intros x y E. unfold equiv, dy_eq in *.
    rewrite E. reflexivity.
  Qed.

  Instance: Transitive dy_eq.
  Proof with eauto; try reflexivity.
    intros x y z E1 E2. unfold equiv, dy_eq in *.
    destruct (total_order (expo x) (expo y)) as [F|F];
      rewrite (shiftl_cut_minus_0 F) in E1; 
      destruct (total_order (expo y) (expo z)) as [G|G];
      rewrite (shiftl_cut_minus_0 G) in E2... 
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, E2. repeat rewrite <-shiftl_sum_exp. 
    apply shiftl_proper... unfold_cut_minus. 
    rewrite (cut_minus_0 (expo x)). ring_simplify. 
    apply cut_minus_precedes_trans... transitivity (expo y)...
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, <-E2. repeat rewrite <-shiftl_sum_exp. 
    apply shiftl_proper... unfold_cut_minus. 
    apply cut_minus_plus_toggle1...
    (* expo y ≤ expo x, expo y ≤ expo z *)
    apply (shiftl_inj (expo x -- expo y))... unfold flip.
    rewrite shiftl_order, E1, E2. repeat rewrite <-shiftl_sum_exp. 
    apply shiftl_proper... unfold_cut_minus. 
    rewrite commutativity. apply cut_minus_plus_toggle2...
    (* expo y ≤ expo x, expo z ≤ expo y *)
    rewrite <-E2, <-E1. repeat rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus. 
    rewrite (cut_minus_0 (expo z)). ring_simplify. 
    symmetry. apply cut_minus_precedes_trans... transitivity (expo y)...
  Qed.  
  
  Instance: Equivalence dy_eq.
  Instance: Setoid Dyadic.

  (* Equalitity is decidable *)
  Lemma dy_eq_dec_aux (x y : Dyadic) p : 
    mant x = mant y ≪ exist _ (expo y - expo x) p ↔ x = y.
  Proof with auto.
    pose proof (proj1 (semiring.sr_precedes_0_minus _  _) p).
    split; intros E. 
    (* → *)
    unfold equiv, dy_eq.
    rewrite E, <-shiftl_sum_exp.
    apply shiftl_proper. reflexivity.
    unfold_cut_minus.
    rewrite cut_minus_0, cut_minus_ring_minus...
    ring.
    (* ← *)
    unfold equiv, dy_eq in E.
    apply (shiftl_inj (expo x -- expo y)). unfold flip.
    rewrite E, <-shiftl_sum_exp.
    apply shiftl_proper. reflexivity.
    unfold_cut_minus.
    rewrite (cut_minus_0 (expo x) (expo y)), (cut_minus_ring_minus (expo y) (expo x))...
    ring.
  Qed.

   Lemma dy_eq_dec_aux_neg (x y : Dyadic) p : 
     mant x ≠ mant y ≪ exist _ (expo y - expo x) p ↔ x ≠ y.
   Proof. split; intros E; intro; apply E; eapply dy_eq_dec_aux; eassumption. Qed.

  Global Program Instance dy_eq_dec : ∀ (x y: Dyadic), Decision (x = y) := λ x y,
     if decide (expo x ≤ expo y) 
     then if decide (mant x = mant y ≪ exist _ (expo y - expo x) _) then left _ else right _ 
     else if decide (mant x ≪ exist _ (expo x - expo y) _ = mant y) then left _ else right _.
  Next Obligation. eapply semiring.sr_precedes_0_minus. assumption. Qed.
  Next Obligation. eapply dy_eq_dec_aux; eauto. Qed.
  Next Obligation. eapply dy_eq_dec_aux_neg; eauto. Qed.
  Next Obligation. apply semiring.sr_precedes_0_minus. auto. Qed.
  Next Obligation. symmetry. eapply dy_eq_dec_aux. symmetry. eassumption. Qed.
  Next Obligation. apply not_symmetry. eapply dy_eq_dec_aux_neg. apply not_symmetry. eassumption. Qed.

  Instance dyadic_proper: Proper ((=) ==> (=) ==> (=)) dyadic.
  Proof.
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq. simpl.
    rewrite E1, E2. reflexivity.
  Qed.

  (** * Basic operations *)
  Global Program Instance dy_plus: RingPlus Dyadic := λ x y, 
    if decide (expo x ≤ expo y)
    then mant x + (mant y ≪ exist _ (expo y - expo x) _) $ min (expo x) (expo y)
    else (mant x ≪ exist _ (expo x - expo y) _) + mant y $ min (expo x) (expo y).
  Next Obligation. apply semiring.sr_precedes_0_minus. assumption. Qed.
  Next Obligation. apply semiring.sr_precedes_0_minus. auto. Qed.

  (* The following plus function is less efficient, because it involves computing [decide (expo x ≤ expo y)] twice.
    Yet, it is much more convinient to reason with. *)
  Definition dy_plus_alt (x y : Dyadic) : Dyadic := 
    mant x ≪ (expo x -- expo y) + mant y ≪ (expo y -- expo x) $ min (expo x) (expo y).
  
  Lemma dy_plus_alt_correct x y : dy_plus x y = dy_plus_alt x y.
  Proof with auto; try reflexivity.
    unfold dy_plus, dy_plus_alt.
    case (decide (expo x ≤ expo y)); intros E; 
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
    split; intros E F; apply E. 
    unfold equiv, dy_eq. simpl.
    rewrite F. do 2 rewrite left_absorb. reflexivity.
    unfold equiv, dy_eq in F. simpl in F.
    rewrite left_absorb in F.
    apply stable; intros G. 
    apply (shiftl_nonzero (mant x) (expo x -- 0)); assumption.
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
  Instance dy_plus_alt_proper: Proper ((=) ==> (=) ==> (=)) dy_plus_alt.
  Proof with auto; try reflexivity.
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq, dy_plus_alt in *. simpl.
    do 2 rewrite shiftl_sum_base. 
    repeat rewrite <-shiftl_sum_exp.
    apply sg_mor. 
    apply dy_plus_proper_aux...
    rewrite (commutativity (expo x1) (expo x2)), (commutativity (expo y1) (expo y2)). 
    apply dy_plus_proper_aux...
  Qed.

  Instance dy_plus_proper: Proper ((=) ==> (=) ==> (=)) dy_plus.
  Proof.
    repeat intro. do 2 rewrite dy_plus_alt_correct.
    apply dy_plus_alt_proper; auto.
  Qed.

  Instance: Associative dy_plus.
  Proof with auto; try reflexivity; try ring.
    intros x y z. do 4 rewrite dy_plus_alt_correct. 
    unfold equiv, dy_eq, dy_plus_alt. simpl. 
    apply shiftl_proper...
    2: rewrite associativity...
    repeat rewrite shiftl_sum_base. 
    repeat rewrite <-shiftl_sum_exp. 
    rewrite associativity.
    repeat apply sg_mor; apply shiftl_proper; unfold_cut_minus...
    apply cut_minus_min1.
    apply cut_minus_min2.
    rewrite (commutativity (expo y) (expo z)), (commutativity (expo x) (expo y)).
    symmetry. apply cut_minus_min1.
  Qed.

  Instance: Commutative dy_plus.
  Proof with auto; try reflexivity. 
    repeat intro. do 2 rewrite dy_plus_alt_correct.
    unfold dy_plus, equiv, dy_eq. simpl.
    apply shiftl_proper...
    apply commutativity...
    rewrite commutativity...
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_plus).

  Lemma dyadic_left_identity (x : Dyadic) : 0 + x = x.
  Proof with auto; try reflexivity.
    rewrite dy_plus_alt_correct.
    unfold equiv, dy_eq, sg_op, dy_plus_alt. simpl.
    rewrite left_absorb, left_identity. rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus.
    destruct (total_order (expo x) 0) as [F|F].
    rewrite min_r; auto. 2: apply _. rewrite cut_minus_rightabsorb... ring.
    rewrite min_l... rewrite cut_minus_leftabsorb... ring.
  Qed.

  Program Instance: Monoid Dyadic (op:=dy_plus) (unit:=dy_0).
  Next Obligation. repeat intro. apply dyadic_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_left_identity. Qed.
  
  (* * Properties of opp *)
  Instance: Proper ((=) ==> (=)) dy_opp.
  Proof.
    intros x y E.
    unfold equiv, dy_eq, dy_opp in *. simpl.
    do 2 rewrite opp_shiftl.
    rewrite E. reflexivity.
  Qed.

  Lemma dyadic_ginv (x : Dyadic) : - x + x = 0.
  Proof.
    rewrite dy_plus_alt_correct.
    unfold equiv, dy_eq, sg_op, dy_plus_alt. simpl.
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
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq, dy_mult in *. simpl. 
    destruct (total_order (expo x1) (expo y1)) as [F|F];
      destruct (total_order (expo x2) (expo y2)) as [G|G];
      rewrite (shiftl_cut_minus_0 F) in E1; 
      rewrite (shiftl_cut_minus_0 G) in E2...
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, E2. 
    rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
    apply shiftl_proper... unfold_cut_minus. 
    rewrite (cut_minus_0 (expo x1 + expo x2)). ring_simplify.
    apply cut_minus_plus_distr...
    apply semiring.sr_precedes_plus_compat...
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
    rewrite (cut_minus_0 (expo y1 + expo y2)). ring_simplify.
    symmetry. apply cut_minus_plus_distr...
    apply semiring.sr_precedes_plus_compat...
  Qed.

  Instance: Associative dy_mult.
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq. simpl.
   apply shiftl_proper. ring. unfold_cut_minus. apply cut_minus_proper; ring. 
  Qed.

  Instance: Commutative dy_mult.
  Proof.
    repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq. simpl.
    apply shiftl_proper. ring. unfold_cut_minus. apply cut_minus_proper; ring. 
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_mult).

  Lemma dyadic_mult_left_identity (x : Dyadic) : 1 * x = x.
  Proof with try reflexivity.
    unfold equiv, dy_eq, dy_mult. simpl.
    rewrite left_identity. rewrite left_identity...
  Qed.

  Program Instance: Monoid Dyadic (op:=dy_mult) (unit:=dy_1).
  Next Obligation. repeat intro. apply dyadic_mult_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_mult_left_identity. Qed.

  Instance: CommutativeMonoid Dyadic (op:=dy_mult) (unit:=dy_1).

  Lemma dyadic_distr_l (x y z : Dyadic) : x * (y + z) = (x * y) + (x * z).
  Proof with auto; try reflexivity.
    do 2 rewrite dy_plus_alt_correct.
    unfold equiv, dy_eq, dy_mult, dy_plus_alt; simpl.
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

  (** 
   * Embedding into the rationals
   If we already have a [Rationals] implementation [Q], then we can embed [Dyadic]
   into it. That is, we have an injective ring morphism [DtoQ : Dyadic → Q].
  *)
  Context `{Rationals Q}.
  Add Field Q: (fields.stdlib_field_theory Q).

  (* We don't make (Z >-> Q) a coercion because it could be computationally expensive
   and we want to see where it's called. *)
  Context `{!Ring_Morphism (ZtoQ: Z → Q)}.
  
  (* We use binary division because that might have a more efficient implementation. *)
  Context `{fd : !FieldDiv Q}.

  Program Definition EtoQ (n : Pos Z) : { z : Q | z ≠ 0 } := ZtoQ (1 ≪ n).
  Next Obligation with intuition.
    intros E.
    apply (shiftl_nonzero 1 n).
     apply (ne_zero 1).
    apply (injective ZtoQ).
    rewrite rings.preserves_0...
  Qed.

  Global Instance EtoQ_proper: Proper ((=) ==> (=)) EtoQ.
  Proof.
    intros x y E.
    unfold EtoQ. unfold equiv, sig_equiv, sig_relation. simpl.
    rewrite E. reflexivity.
  Qed.
 
  Program Definition DtoQ (d: Dyadic): Q := 
    if decide (0 ≤ expo d)
    then ZtoQ (mant d ≪ exist _ (expo d) _)
    else ZtoQ (mant d) // (EtoQ (exist _ (-expo d) _)).
  Next Obligation. 
   apply semiring.sr_precedes_0_flip. 
   rewrite rings.inv_involutive. 
   apply orders.precedes_flip. assumption.
  Qed.

  Definition DtoQ_alt (d: Dyadic): Q := ZtoQ (mant d ≪ (expo d -- 0)) // EtoQ (0 -- expo d).

  Global Instance: Proper ((=) ==> (=)) DtoQ_alt.
  Proof with auto; try reflexivity.
    intros x y E.
    unfold DtoQ_alt, EtoQ.
    do 2 rewrite fields.field_div_correct.
    apply fields.equal_quotients. simpl.
    do 2 rewrite <-rings.preserves_mult.
    apply sm_proper.
    do 2 rewrite mult_shiftl.
    do 2 rewrite right_identity.
    unfold equiv, dy_eq in E.
    destruct (total_order (expo x) (expo y)) as [F|F]; rewrite (shiftl_cut_minus_0 F) in E.
     rewrite E. do 3 rewrite <-shiftl_sum_exp.
     apply shiftl_proper... 
     unfold_cut_minus. ring_simplify. apply cut_minus_zeros_precedes...
    rewrite <-E. do 3 rewrite <-shiftl_sum_exp.
    apply shiftl_proper... 
    unfold_cut_minus. symmetry. ring_simplify. apply cut_minus_zeros_precedes...
  Qed.
  
  Lemma DtoQ_alt_correct x : DtoQ x = DtoQ_alt x.
  Proof with auto; try reflexivity.
    unfold DtoQ, DtoQ_alt. 
    case (decide (0 ≤ expo x)); intros E.
     rewrite fields.field_div_correct.
     setoid_replace (// EtoQ (0 -- expo x)) with 1.
     rewrite right_identity.
     apply sm_proper. apply shiftl_proper... 
     unfold_cut_minus. rewrite cut_minus_rightidentity...
     assert (EtoQ (0 -- expo x) = 1) as F.
      unfold EtoQ, equiv, sig_equiv, sig_relation. simpl.
      rewrite shiftl_cut_minus_0... apply rings.preserves_1.
     rewrite F. rewrite <-rings.mult_1_l. apply fields.mult_inverse'.
    rewrite shiftl_cut_minus_0... 
    apply fields.field_div_proper...
    unfold EtoQ, equiv, sig_equiv, sig_relation. simpl.
    apply sm_proper. apply shiftl_proper...
    unfold_cut_minus.
    rewrite cut_minus_ring_inv...
  Qed.

  Global Instance: Proper ((=) ==> (=)) DtoQ.
  Proof.
    intros x y E. do 2 rewrite DtoQ_alt_correct.
    rewrite E. reflexivity.
  Qed.

  Lemma EtoQ_plus_mult x y :  EtoQ (x + y) = (EtoQ x) * (EtoQ y).
  Proof.
    intros.
    unfold equiv, sig_equiv, sig_relation, EtoQ. simpl.
    rewrite <-rings.preserves_mult.
    rewrite <-mult_shiftl_1.
    rewrite shiftl_sum_exp.
    reflexivity.
  Qed.

  Lemma EtoQ_zero_one : EtoQ 0 = 1.
  Proof.
    unfold equiv, sig_equiv, sig_relation, EtoQ. simpl.
    rewrite right_identity.
    rewrite rings.preserves_1.
    reflexivity.
  Qed.

  Lemma EtoQ_quotients a b c d : 
    ZtoQ a // EtoQ b + ZtoQ c // EtoQ d = ZtoQ (a ≪ d + c ≪ b) // EtoQ (b + d).
  Proof.
    rewrite rings.preserves_plus.
    do 3 rewrite fields.field_div_correct.
    rewrite fields.quotients. simpl.
    repeat rewrite <-rings.preserves_mult.
    repeat rewrite <-mult_shiftl_1.
    rewrite EtoQ_plus_mult. 
    reflexivity.
  Qed.

  Lemma DtoQ_preserves_plus x y : DtoQ (x + y) = DtoQ x + DtoQ y.
  Proof. 
    unfold ring_plus at 1. 
    rewrite dy_plus_alt_correct. do 3 rewrite DtoQ_alt_correct. 
    unfold dy_plus_alt, DtoQ_alt. simpl.
    rewrite EtoQ_quotients. 
    do 2 rewrite fields.field_div_correct.
    apply fields.equal_quotients. 
    unfold EtoQ. simpl.
    do 2 rewrite <-rings.preserves_mult.
    apply sm_proper.
    do 2 rewrite <-mult_shiftl_1.
    do 3 rewrite shiftl_sum_base.
    repeat rewrite <-shiftl_sum_exp.
    apply sg_mor; apply shiftl_proper; try reflexivity; unfold_cut_minus; 
      destruct (total_order (expo x) (expo y)) as [F|F]. 
       rewrite (cut_minus_0 _ _ F), (min_l _ _ F). ring.
      rewrite (min_r _ _ F). 
      symmetry. rewrite associativity, <-cut_minus_zeros_precedes. ring. assumption.
     rewrite (min_l _ _ F).
     symmetry. rewrite associativity, <-cut_minus_zeros_precedes. ring. assumption.
    rewrite (cut_minus_0 _ _ F), (min_r _ _ F). ring.
  Qed.
  
  Lemma DtoQ_preserves_0 : DtoQ 0 = 0.
  Proof. 
    rewrite DtoQ_alt_correct. unfold DtoQ_alt. simpl.
    apply fields.field_div_0_l.
    rewrite left_absorb.
    rewrite rings.preserves_0. reflexivity.
  Qed.
  
  Lemma DtoQ_preserves_group_inv x : DtoQ (-x) = -DtoQ x.
  Proof. 
    do 2 rewrite DtoQ_alt_correct. unfold DtoQ_alt. simpl.
    do 2 rewrite fields.field_div_correct.
    rewrite opp_shiftl, preserves_inv.
    ring.
  Qed.

  Lemma DtoQ_preserves_mult x y : DtoQ (x * y) = DtoQ x * DtoQ y.
  Proof with auto; try reflexivity.
    do 3 rewrite DtoQ_alt_correct. 
    unfold ring_mult at 1. unfold dy_mult at 1.
    unfold DtoQ_alt. simpl.
    rewrite mult_shiftl_1, (mult_shiftl_1 (mant x)), (mult_shiftl_1 (mant y)).
    do 4 rewrite rings.preserves_mult.
    assert (∀ (a b c : Q) d, (a * b * c) // d = (a * b) * (c // d)) as E1.
     intros. do 2 rewrite fields.field_div_correct. ring.
    assert (∀ (a b d e : Q) c f, (a * b) // c * (d * e) // f = (a * d) * ((b * e) // (c * f))) as E2.
     intros. do 3 rewrite fields.field_div_correct. rewrite <-fields.mult_inv_distr. ring.
    rewrite E1, E2. apply sg_mor... clear E1 E2.
    do 2 rewrite fields.field_div_correct.
    apply fields.equal_quotients. simpl.
    do 4 rewrite <-rings.preserves_mult.
    apply sm_proper.
    do 3 rewrite <-mult_shiftl_1. 
    repeat rewrite <-shiftl_sum_exp.
    rewrite <-mult_shiftl_1, <-shiftl_sum_exp.
    apply shiftl_proper...
    unfold_cut_minus.
    repeat rewrite <-cut_minus_zero_plus_toggle. ring.
  Qed. 

  Lemma DtoQ_preserves_1 : DtoQ 1 = 1.
  Proof.
    rewrite DtoQ_alt_correct. 
    unfold DtoQ_alt, EtoQ. simpl. 
    apply fields.field_div_diag. reflexivity.
  Qed.

  Instance: Ring_Morphism DtoQ.
  Proof. 
    repeat (split; try apply _).
    exact DtoQ_preserves_plus.
    exact DtoQ_preserves_0.
    exact DtoQ_preserves_group_inv.
    exact DtoQ_preserves_mult.
    exact DtoQ_preserves_1.
  Qed.

  Instance: Injective DtoQ.
  Proof with auto.
    split; try apply _.
    intros x y E.
    unfold equiv, dy_eq. 
    do 2 rewrite DtoQ_alt_correct in E. 
    unfold DtoQ_alt, EtoQ in E. 
    do 2 rewrite fields.field_div_correct in E.
    apply fields.equal_quotients in E. simpl in E.
    do 2 rewrite <-rings.preserves_mult in E.
    do 2 rewrite <-mult_shiftl_1 in E.
    do 2 rewrite <-shiftl_sum_exp in E.
    apply (injective ZtoQ) in E.
    destruct (total_order (expo x) (expo y)) as [F|F]; rewrite (shiftl_cut_minus_0 F).
     apply (shiftl_inj (expo x -- 0 + (0 -- expo y))). unfold flip.
     rewrite E, <-shiftl_sum_exp. apply shiftl_proper. reflexivity.
     unfold_cut_minus. rewrite <-cut_minus_zeros_precedes... ring.
    apply (shiftl_inj (expo y -- 0 + (0 -- expo x))). unfold flip.
    rewrite <-E, <-shiftl_sum_exp. apply shiftl_proper. reflexivity.
    unfold_cut_minus. symmetry. 
    rewrite <-cut_minus_zeros_precedes... ring.
  Qed.

End dyadics.
