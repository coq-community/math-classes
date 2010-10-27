Require rings.
Require Import
  Morphisms Ring Program RelationClasses
  interfaces.integers interfaces.naturals
  abstract_algebra 
  canonical_names 
  interfaces.bit_shift
  rationals
  theory.integers.

Section dyadics.
  Context Z N `{Integers Z} `{Naturals N} `{sl : !ShiftLeft Z N}.
  
  Add Ring Z: (rings.stdlib_ring_theory Z).
  Add Ring N: (rings.stdlib_semiring_theory N).

  Record Dyadic := dyadic { mant: Z; expo: N }.

  Global Instance dy_eq: Equiv Dyadic := λ x y,
    mant y ≪ expo x = mant x ≪ expo y.
  
  Global Instance dy_eq_dec (x y: Dyadic): Decision (x = y).
  Proof. 
    unfold equiv, dy_eq. apply _. 
  Defined.

  Global Instance dy_mult: RingMult Dyadic := λ x y, dyadic 
    (mant x * mant y) 
    (expo x + expo y).

  Global Instance dy_plus: RingPlus Dyadic := λ x y, dyadic
    (mant y ≪ expo x + mant x ≪ expo y)
    (expo x + expo y).

  Global Instance dy_opp: GroupInv Dyadic := λ x, dyadic (- mant x) (expo x).
  Global Instance dy_0: RingZero Dyadic := dyadic 0 0.
  Global Instance dy_1: RingOne Dyadic := dyadic 1 0.

  Global Instance: Reflexive (_ : Equiv Dyadic).
  Proof.
    intro. unfold equiv, dy_eq. reflexivity.
  Qed.

  Global Instance: Symmetric (_ : Equiv Dyadic).
  Proof.
    intros x y E. unfold equiv, dy_eq in *. rewrite E. reflexivity.
  Qed.

  (* Without this Instance many rewrites result in a loop... *)
  Instance: Proper ((=) ==> (=) ==> (=)) (@shiftl Z N _ _ _ _ _ _). 
  Proof.  apply _. Qed.

  Global Instance: Transitive (_ : Equiv Dyadic).
  Proof with eauto; try reflexivity.
    intros x y z E1 E2. unfold equiv, dy_eq in *.
    apply shiftl_inj with (expo y).
    unfold flip. 
    rewrite shiftl_order. Timeout 5 rewrite E2. 
    rewrite (shiftl_order _ (expo z) (expo y)). rewrite <-E1. 
    rewrite shiftl_order...
    (* transitivity (mant y ≪ expo z ≪ expo x). 
    apply shiftl_proper... 
    rewrite (shiftl_order (mant y)).
    transitivity (mant x ≪ expo y ≪ expo z).
    apply shiftl_proper...
    apply shiftl_order. *)
  Qed.

  Global Instance: Equivalence (_ : Equiv Dyadic).
  Global Instance: Setoid Dyadic.
 
  (* the Timeouts are present to detect possible hangs caused by rewrite *)
  Global Instance: Associative (_ : RingPlus Dyadic).
  Proof with auto; try ring.
    repeat intro. unfold dy_plus, equiv, dy_eq. simpl. 
    apply shiftl_proper...
    Timeout 5 repeat rewrite shiftl_sum_exp.
    Timeout 5 repeat rewrite shiftl_sum_base.
    Timeout 5 rewrite associativity.
    Timeout 5 rewrite (shiftl_order (mant z) (expo x) (expo y)).
    Timeout 5 rewrite (shiftl_order (mant y) (expo x) (expo z))...
  Qed.

  Global Instance: Commutative dy_plus.
  Proof with ring. 
    repeat intro. 
    unfold dy_plus, equiv, dy_eq. simpl. 
    apply shiftl_proper... 
  Qed. 

  Global Instance: Proper ((=) ==> (=) ==> (=)) (_ : RingPlus Dyadic).
  Proof with try reflexivity; auto.
    intros x1 y1 E1 x2 y2 E2. unfold equiv, dy_eq in *. unfold dy_plus. simpl.
    Timeout 5 repeat rewrite shiftl_sum_base.
    Timeout 10 repeat rewrite shiftl_sum_exp.
    apply sg_mor.
    rewrite shiftl_order_4a. rewrite E2. rewrite shiftl_order_4b...
    rewrite shiftl_order_4b. rewrite E1. rewrite (shiftl_order (mant x1))...
    (*  assert (mant y2 ≪ expo y1 ≪ expo x1 ≪ expo x2 = mant x2 ≪ expo y2 ≪ expo y1 ≪ expo x1) as E3.
      Timeout 5 rewrite (shiftl_order _ (expo x1) (expo x2))...
      Timeout 5 rewrite (shiftl_order _ (expo y1) (expo x2))...
    rewrite E3. clear E3.
    Timeout 5 rewrite (shiftl_order _ (expo y1) (expo x1)).
    Timeout 5 rewrite (shiftl_order _ (expo y1) (expo y2))...
    Timeout 5 rewrite (shiftl_order _ (expo y2) (expo x1))...
    assert (mant y1 ≪ expo y2 ≪ expo x1 ≪ expo x2 = mant x1 ≪ expo y1 ≪ expo y2 ≪ expo x2) as E3.
      apply shiftl_proper; try reflexivity.
      Timeout 5 rewrite (shiftl_order _ (expo y2) (expo x1))...
    rewrite E3. clear E3.
    Timeout 5 rewrite (shiftl_order _ (expo y2) (expo x2))...
    Timeout 5 rewrite (shiftl_order _ (expo y1) (expo x2))... *)
  Qed.

  Global Instance: SemiGroup Dyadic (op:=(_ : RingPlus Dyadic)).

  Lemma dyadic_left_identity (x : Dyadic) : 0 + x = x.
  Proof with try reflexivity.
    unfold equiv, dy_eq, sg_op, dy_plus. simpl.
    rewrite left_identity. rewrite right_identity. rewrite left_absorb. rewrite right_identity...
    (* rewrite shiftl_sum_exp.
    apply shiftl_proper...
    rewrite right_identity, left_absorb, right_identity... *)
  Qed.

  Global Program Instance: Monoid Dyadic (op:=(_ : RingPlus Dyadic)) (unit:=(_ : RingZero Dyadic)).
  Next Obligation. repeat intro. apply dyadic_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_left_identity. Qed.

  Global Instance: Proper ((=) ==> (=)) (_: GroupInv Dyadic).
  Proof.
    intros x y E.
    unfold equiv, dy_eq, dy_opp in *. simpl.
    do 2 rewrite opp_shiftl.
    rewrite E. reflexivity.
  Qed.

  Lemma dyadic_ginv (x : Dyadic) : - x + x = 0.
  Proof with try reflexivity.
    unfold equiv, dy_eq, sg_op, dy_plus. simpl.
    rewrite left_absorb, right_identity.
    rewrite <- shiftl_sum_base.
    assert (mant x + - mant x = 0) as E by ring. rewrite E.
    rewrite left_absorb...
    (* assert ((mant x + - mant x) ≪ expo x = 0 ≪ expo x) as E.
      apply shiftl_proper... ring.  
    rewrite E. clear E.
    rewrite left_absorb... *)
  Qed.

  Global Program Instance: Group Dyadic.
  Next Obligation. apply dyadic_ginv. Qed.
  Next Obligation. rewrite commutativity. apply dyadic_ginv. Qed.

  Global Program Instance: AbGroup Dyadic.

  Global Instance: Associative (_: RingMult Dyadic).
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq.
   simpl. apply shiftl_proper; ring.
  Qed.

  Global Instance: Commutative (_: RingMult Dyadic).
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq.
   simpl. apply shiftl_proper; ring.
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> (=)) (_: RingMult Dyadic).
  Proof with intuition.
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq, dy_mult in *.  simpl.
    repeat rewrite shiftl_sum_exp.
    rewrite shiftl_order.
    rewrite <- mult_shiftl. rewrite E2. rewrite mult_shiftl.
    rewrite (commutativity (mant x1) (mant x2)).
    rewrite <-(mult_shiftl (mant x2) (mant x1)). rewrite <-E1. rewrite mult_shiftl.
    rewrite shiftl_order. rewrite commutativity...
  Qed.

  Global Instance: SemiGroup Dyadic (op:=(_: RingMult Dyadic)).

  Lemma dyadic_mult_left_identity (x : Dyadic) : 1 * x = x.
  Proof with try reflexivity.
    unfold equiv, dy_eq, sg_op, dy_plus. simpl.
    rewrite left_identity. rewrite left_identity... 
    (* intro; unfold equiv, dy_eq, sg_op, dy_mult; simpl.
    rewrite 
    rewrite shiftl_sum_exp.
    apply shiftl_proper...
    rewrite left_identity, right_identity... *)
  Qed.

  Global Program Instance: Monoid Dyadic (op:=(_: RingMult Dyadic)) (unit:=(_: RingOne Dyadic)).
  Next Obligation. repeat intro. apply dyadic_mult_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_mult_left_identity. Qed.

  Global Instance: CommutativeMonoid Dyadic (op:=(_: RingMult Dyadic)) (unit:=(_: RingOne Dyadic)).

  Global Instance: Distribute (_: RingMult Dyadic) (_: RingPlus Dyadic).
  Proof with try reflexivity.
    split; intros x y z; unfold equiv, dy_eq, dy_mult, dy_plus; simpl.

    repeat rewrite shiftl_sum_exp.
    apply shiftl_proper...
    rewrite shiftl_order. repeat apply shiftl_proper...
    rewrite distribute_l.
    repeat rewrite shiftl_sum_base.
    repeat rewrite mult_shiftl.
    rewrite (shiftl_order _ (expo x) (expo y)). rewrite (shiftl_order _ (expo x) (expo z))...

    repeat rewrite shiftl_sum_exp.
    apply shiftl_proper... apply shiftl_proper...
    rewrite distribute_r.
    repeat rewrite shiftl_sum_base. 
    apply sg_mor.
    rewrite (commutativity (mant y ≪ expo x)). rewrite mult_shiftl.
    rewrite (commutativity (mant z)). rewrite <-shiftl_order_4b...
    rewrite (commutativity (mant x ≪ expo y)). rewrite mult_shiftl.
    rewrite (commutativity (mant z)). rewrite (shiftl_order _ (expo z) (expo x))... 
  Qed.

  Global Instance: Ring Dyadic.

  (* now if we already have a rationals implementation... *)
  Context `{Rationals Q} (ZtoQ: Z → Q) `{!Ring_Morphism ZtoQ} `{FieldDiv Q}.

  (* We don't make (Z >-> Q) a coercion because it could be computationally expensive
   and we want to see where it's called. *)
  Require Import theory.rings.
  Program Definition inject (d: Dyadic): Q := ZtoQ (mant d) * // ZtoQ ((1+1) ≪ expo d).
  Next Obligation with auto.
   intro.
   apply (shiftl_nonzero (1+1) (expo d)). 
   exact two_nonzero.
   apply (injective ZtoQ).
   rewrite preserves_0...
  Qed.

  Instance: Proper ((=) ==> (=)) inject.
  Proof with try apply _.
   intros x y E.
   unfold inject. 
   apply theory.fields.equal_quotients. simpl.
   do 2 rewrite shiftl_sum_base.
   do 2 rewrite <- preserves_mult.
   do 2 rewrite distribute_l.
   do 2 rewrite mult_shiftl.
   do 2 rewrite right_identity.
   unfold equiv, dy_eq in E. rewrite E.
   reflexivity.
  Qed.

  Lemma inject_0: inject 0 = 0.
  Proof. unfold inject. simpl. rewrite preserves_0. apply left_absorb. Qed.

  Instance: Ring_Morphism inject.
  Proof with auto.
    repeat (split; try apply _).
    intros x y.
    unfold inject. simpl. 
  Admitted.

  Instance: Injective inject.
  Proof with auto.
   repeat intro.
   unfold equiv, dy_eq.
  Admitted. (*
   apply (injective ZtoQ).
   
   apply (theory.fields.equal_quotients) in H5.
   simpl in H5.
   unfold den in H5.
   unfold compose in H5.
   rewrite <- mult_shiftl_1.
   rewrite <- (mult_shiftl_1 (num x)).
   apply (theory.fields.equal_quotients) in H4.
   do 2 rewrite preserves_mult.
   symmetry. assumption.
  Qed.*)

  

  


End contents.