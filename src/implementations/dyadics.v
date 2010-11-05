(** 
  The dyadic rationals are numbers of the shape
  [z # 2 ^ n] with [z : Z] and [n : N] for some [Integers] implementation [Z] and
  [Naturals] implementation [N]. These numbers form a ring and can be embedded
  into any [Rationals] implementation [Q]. 
*)

Require Import
  Morphisms Ring Program RelationClasses
  abstract_algebra 
  interfaces.integers interfaces.naturals interfaces.rationals
  interfaces.additional_operations theory.additional_operations
  theory.integers theory.rings theory.fields.

Section dyadics.
  Context `{Integers Z} `{Naturals N}.
  Add Ring Z: (rings.stdlib_ring_theory Z).
  Add Ring N: (rings.stdlib_semiring_theory N).

  Context `{!NatPow Z N} `{sl : !ShiftLeft Z N}.

  (** * Definition *)
  Record Dyadic := dyadic { mant: Z; expo: N }.
  Infix "#" := dyadic (at level 80).

  (** * Equality *)
  Global Instance dy_eq: Equiv Dyadic := λ x y,
    mant y ≪ expo x = mant x ≪ expo y.
  
  Global Instance dy_eq_dec (x y: Dyadic): Decision (x = y).
  Proof. 
    unfold equiv, dy_eq. apply _. 
  Defined.

  Global Instance: Reflexive dy_eq.
  Proof.
    intro. unfold equiv, dy_eq. reflexivity.
  Qed.

  Global Instance: Symmetric dy_eq.
  Proof.
    intros x y E. unfold equiv, dy_eq in *. 
    rewrite E. reflexivity.
  Qed.

  Global Instance: Transitive dy_eq.
  Proof with eauto; try reflexivity.
    intros x y z E1 E2. unfold equiv, dy_eq in *.
    apply shiftl_inj with (expo y).
    unfold flip. 
    rewrite shiftl_order. Timeout 5 rewrite E2. 
    rewrite (shiftl_order _ (expo z) (expo y)). rewrite <-E1. 
    rewrite shiftl_order...
  Qed.

  Global Instance: Equivalence dy_eq.
  Global Instance: Setoid Dyadic.
 
  (** * Basic operations *)
  Global Instance dy_mult: RingMult Dyadic := λ x y,  
    mant x * mant y # expo x + expo y.

  Global Instance dy_plus: RingPlus Dyadic := λ x y,
    mant y ≪ expo x + mant x ≪ expo y # expo x + expo y.

  Global Instance dy_opp: GroupInv Dyadic := λ x, -mant x # expo x.
  Global Instance dy_0: RingZero Dyadic := 0 # 0.
  Global Instance dy_1: RingOne Dyadic := 1 # 0.

  (* the Timeouts are present to detect possible hangs caused by rewrite *)
  Global Instance: Associative dy_plus.
  Proof with try ring; try reflexivity.
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

  Global Instance: Proper ((=) ==> (=) ==> (=)) dy_plus.
  Proof with try reflexivity; auto.
    intros x1 y1 E1 x2 y2 E2. unfold equiv, dy_eq in *. unfold dy_plus. simpl.
    Timeout 5 repeat rewrite shiftl_sum_base.
    Timeout 10 repeat rewrite shiftl_sum_exp.
    apply sg_mor.
    rewrite shiftl_order_4a. rewrite E2. rewrite shiftl_order_4b...
    rewrite shiftl_order_4b. rewrite E1. rewrite (shiftl_order (mant x1))...
  Qed.

  Global Instance: SemiGroup Dyadic (op:=dy_plus).

  Lemma dyadic_left_identity (x : Dyadic) : 0 + x = x.
  Proof with try reflexivity.
    unfold equiv, dy_eq, sg_op, dy_plus. simpl. 
    rewrite left_identity. rewrite right_identity. rewrite left_absorb. rewrite right_identity...
  Qed.

  Global Program Instance: Monoid Dyadic (op:=dy_plus) (unit:=dy_0).
  Next Obligation. repeat intro. apply dyadic_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_left_identity. Qed.

  Global Instance: Proper ((=) ==> (=)) dy_opp.
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
  Qed.

  Global Program Instance: Group Dyadic.
  Next Obligation. apply dyadic_ginv. Qed.
  Next Obligation. rewrite commutativity. apply dyadic_ginv. Qed.

  Global Program Instance: AbGroup Dyadic.

  Global Instance: Associative dy_mult.
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq.
   simpl. apply shiftl_proper; ring.
  Qed.

  Global Instance: Commutative dy_mult.
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq.
   simpl. apply shiftl_proper; ring.
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> (=)) dy_mult.
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

  Global Instance: SemiGroup Dyadic (op:=dy_mult).

  Lemma dyadic_mult_left_identity (x : Dyadic) : 1 * x = x.
  Proof with try reflexivity.
    unfold equiv, dy_eq, sg_op, dy_plus. simpl.
    rewrite left_identity. rewrite left_identity... 
  Qed.

  Global Program Instance: Monoid Dyadic (op:=dy_mult) (unit:=dy_1).
  Next Obligation. repeat intro. apply dyadic_mult_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_mult_left_identity. Qed.

  Global Instance: CommutativeMonoid Dyadic (op:=dy_mult) (unit:=dy_1).

  Global Instance: Distribute dy_mult dy_plus.
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

  (** 
   * Embedding into the rationals
   If we already have a [Rationals] implementation [Q], then we can embed [Dyadic]
   into it. That is, we have an injective ring morphism [DtoQ : Dyadic → Q].
  *)
  Context `{Rationals Q}.
  Add Field Q: (stdlib_field_theory Q).

  (* We don't make (Z >-> Q) a coercion because it could be computationally expensive
   and we want to see where it's called. *)
  Context (ZtoQ: Z → Q) `{!Ring_Morphism ZtoQ}.
  
  (* We use binary division because that might have a more efficient implementation. *)
  Context `{fd : !FieldDiv Q}.

  Program Definition EtoQ (n : N) : { z : Q | z ≠ 0 } := ZtoQ (1 ≪ n).
  Next Obligation with intuition.
    intros E.
    apply (shiftl_nonzero 1 n).
    intro E2. symmetry in E2. apply (zero_ne_one E2).
    apply (injective ZtoQ).
    rewrite preserves_0...
  Qed.

  Global Instance EtoQ_proper: Proper ((=) ==> (=)) EtoQ.
  Proof.
    intros x y E.
    unfold EtoQ. unfold equiv, sig_equiv, sig_relation. simpl.
    rewrite E. reflexivity.
  Qed.
 
  Definition DtoQ (d: Dyadic): Q := ZtoQ (mant d) / EtoQ (expo d).

  Global Instance: Proper ((=) ==> (=)) DtoQ.
  Proof with try apply _.
    intros x y E.
    unfold DtoQ, EtoQ.
    do 2 rewrite field_div_correct.
    apply equal_quotients. simpl.
    do 2 rewrite <- preserves_mult.
    do 2 rewrite mult_shiftl.
    do 2 rewrite right_identity.
    unfold equiv, dy_eq in E. rewrite E.
    reflexivity.
  Qed.

  Lemma EtoQ_plus_mult x y :  EtoQ (x + y) = (EtoQ x) * (EtoQ y).
  Proof.
    intros.
    unfold equiv, sig_equiv, sig_relation, EtoQ. simpl.
    rewrite <-preserves_mult.
    rewrite <-mult_shiftl_1.
    rewrite shiftl_sum_exp.
    reflexivity.
  Qed.

  Lemma EtoQ_zero_one : EtoQ 0 = 1.
  Proof.
    unfold equiv, sig_equiv, sig_relation, EtoQ. simpl.
    rewrite right_identity.
    rewrite preserves_1.
    reflexivity.
  Qed.

  Lemma DtoQ_quotients a b c d : 
    ZtoQ a / EtoQ b + ZtoQ c / EtoQ d = ZtoQ (a ≪ d + c ≪ b) / EtoQ (b + d).
  Proof.
    rewrite preserves_plus.
    do 3 rewrite field_div_correct.
    rewrite quotients. simpl.
    repeat rewrite <-preserves_mult.
    repeat rewrite <-mult_shiftl_1.
    rewrite EtoQ_plus_mult. 
    reflexivity.
  Qed.

  Lemma DtoQ_preserves_plus x y : DtoQ (x + y) = DtoQ x + DtoQ y.
  Proof.
    unfold ring_plus at 1. unfold dy_plus at 1.
    unfold DtoQ. simpl.
    rewrite (commutativity (mant y ≪ expo x) _).
    symmetry. apply DtoQ_quotients.
  Qed.
  
  Lemma DtoQ_preserves_zero : DtoQ 0 = 0.
  Proof. 
    unfold DtoQ. simpl.
    rewrite field_div_correct. 
    rewrite preserves_0. ring.
  Qed.
  
  Lemma DtoQ_preserves_group_inv x : DtoQ (-x) = -DtoQ x.
  Proof. 
    unfold DtoQ. simpl.
    do 2 rewrite field_div_correct.
    rewrite preserves_inv. ring.
  Qed.

  Lemma DtoQ_preserves_mult x y : DtoQ (x * y) = DtoQ x * DtoQ y.
  Proof. 
    unfold ring_mult at 1. unfold dy_mult at 1.
    unfold DtoQ. simpl.
    do 3 rewrite field_div_correct. 
    rewrite preserves_mult.
    rewrite EtoQ_plus_mult. 
    rewrite <-mult_inv_distr.
    ring.
  Qed.

  Lemma DtoQ_preserves_one : DtoQ 1 = 1.
  Proof. 
    unfold DtoQ. simpl.
    rewrite field_div_correct.
    rewrite preserves_1. rewrite EtoQ_zero_one.
    apply mult_inverse'.
  Qed.

  Instance: Ring_Morphism DtoQ.
  Proof. 
    repeat (split; try apply _).
    exact DtoQ_preserves_plus.
    exact DtoQ_preserves_zero.
    exact DtoQ_preserves_group_inv.
    exact DtoQ_preserves_mult.
    exact DtoQ_preserves_one.
  Qed.

  Instance: Injective DtoQ.
  Proof with auto.
    split; try apply _.
    intros x y E.
    unfold equiv, dy_eq. unfold DtoQ in E. unfold EtoQ in E.
    do 2 rewrite field_div_correct in E.
    apply equal_quotients in E. simpl in E.
    do 2 rewrite <-preserves_mult in E.
    do 2 rewrite <-mult_shiftl_1 in E.
    symmetry. apply (injective ZtoQ)...
  Qed.

End dyadics.
