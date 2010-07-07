
Require Import
  Unicode.Utf8 Program Ring
  Morphisms
  naturals integers rationals
  abstract_algebra rings canonical_names.

Section nat_pow.

  Context `{Monoid M (op := o: RingMult M) (unit := u: RingOne M)}.

  Definition nat_pow (m: M): nat → M
    := nat_rect (λ _ => M) mon_unit (λ _ => sg_op m).

  Global Instance: Proper ((=) ==> (=) ==> (=)) nat_pow.
  Proof with try reflexivity.
   intros x y E a ? [].
   induction a; simpl...
   rewrite IHa, E...
  Qed.

End nat_pow.

Lemma nat_pow_nonzero `{IntegralDomain R} (n: R) (m: nat): n ≠ 0 → nat_pow n m ≠ 0.
Proof. pose proof (intdom_nozeroes R n). induction m; firstorder. Qed.  

Lemma nat_pow_exp_sum `{SemiRing R} (n: R) (x y: nat): nat_pow n (x + y) = nat_pow n x * nat_pow n y.
Proof.
 induction x; simpl.
  symmetry.
  apply left_identity.
 rewrite IHx. apply associativity.
Qed.

Section shift_left.

  Context `{SemiRing A} `{Naturals B}.

  Add Ring A: (stdlib_semiring_theory A).
  Add Ring B: (stdlib_semiring_theory B).

  Class ShiftLeft: Type := shiftl: A → B → A.

  Infix "≪" := shiftl (at level 33, left associativity).

  Context `{ShiftLeft}.

  Class WithShiftLeft: Prop :=
    shiftl_correct: forall a b, a ≪ b = a * nat_pow (1+1) (naturals_to_semiring B nat b).

  Context `{WithShiftLeft}.

  Global Instance shiftl_proper: Proper ((=) ==> (=) ==> (=)) shiftl.
  Proof. intros ?? E ?? F. do 2 rewrite shiftl_correct. rewrite E, F. reflexivity. Qed.

  Global Instance: LeftAbsorb shiftl 0.
  Proof. intro. rewrite shiftl_correct. ring. Qed.

  Global Instance: RightIdentity shiftl 0.
  Proof. intro. rewrite shiftl_correct. rewrite preserves_0. simpl. apply right_identity. Qed.

  Lemma shiftl_order x y z: x ≪ y ≪ z  = x ≪ z ≪ y.
  Proof. do 4 rewrite shiftl_correct. ring. Qed.

  Lemma mult_shiftl x y z: x * (y ≪ z) = (x * y) ≪ z.
  Proof. do 2 rewrite shiftl_correct. ring. Qed.

  Lemma mult_shiftl_1 x y: x ≪ y = x * (1 ≪ y).
  Proof. do 2 rewrite shiftl_correct. ring. Qed.

  Lemma shiftl_sum_base x y z: (x + y) ≪ z  = x ≪ z + y ≪ z.
  Proof. do 3 rewrite shiftl_correct. ring. Qed.

  Lemma shiftl_sum_exp x y z: x ≪ (y + z) = x ≪ y ≪ z.
  Proof. do 3 rewrite shiftl_correct. rewrite preserves_plus, nat_pow_exp_sum. ring. Qed.

  Lemma shiftl_nonzero `{GroupInv A} `{IntegersToRing A} `{!Integers A} x y: x ≠ 0 → x ≪ y ≠ 0.
  Proof with intuition.
   intros. rewrite shiftl_correct.
   intro.
   apply (no_zero_divisors x).
   split...
   exists (nat_pow (1+1) (naturals_to_semiring B nat y)).
   split.
    apply nat_pow_nonzero.
    apply two_nonzero.
   assumption.
  Qed.

  Lemma shiftl_inj `{GroupInv A} `{IntegersToRing A} `{!Integers A} b: Injective (flip shiftl b).
    (* todo: we don't want to mention the first two parameters here *)
  Proof.
   constructor. 2: constructor; apply _.
   intros ?? E. unfold flip in E. do 2 rewrite shiftl_correct in E.
   apply mult_injective with (nat_pow (1 + 1) (naturals_to_semiring B nat b)).
    apply nat_pow_nonzero, two_nonzero.
   rewrite commutativity, E. ring.
  Qed.

  Lemma opp_shiftl `{GroupInv A} `{!Ring A} x y: (-x) ≪ y = -(x ≪ y).
  Proof.
   do 2 rewrite shiftl_correct.
   rewrite ring_opp_mult. symmetry. rewrite ring_opp_mult.
   ring.
  Qed.

End shift_left.
  (* todo: move reasoning about bit shifts and powers of two into dedicated module *)

Infix "≪" := shiftl (at level 33, left associativity). (* todo: avoid this repetition *)

Implicit Arguments ShiftLeft [].
Instance: Params (@shiftl) 3.

Section contents.

  Context `{Integers Z} `{Naturals N} `{!ShiftLeft Z N} `{!WithShiftLeft}.
    (* todo: we don't want to mention the ShiftLeft operation here *)

  Add Ring Z: (stdlib_ring_theory Z).
  Add Ring N: (stdlib_semiring_theory N).

(*
  Definition pow2 := shiftl 1.

  Lemma pow2_ok n: pow2 n = nat_pow (1+1) (naturals_to_semiring N nat n).
  Proof. unfold pow2. rewrite shiftl_ok, left_identity. reflexivity. Qed.

  Lemma pow2_0: pow2 0 = 1.
  Proof. rewrite pow2_ok, preserves_0. reflexivity. Qed.

  Lemma pow2_nonzero n: pow2 n ≠ 0.
  Proof. unfold pow2. rewrite pow2_ok. apply nat_pow_nonzero, two_nonzero. Qed.
*)

  Record Dyadic := dyadic { num: Z; den_exp: N }.

  Let den := shiftl (1:Z) ∘ den_exp.

  (* operations on Dyadic: *)

  Instance dy_eq: Equiv Dyadic := λ x y =>
    num y ≪ den_exp x = num x ≪ den_exp y.
      (* alternative: shift only one of the two to line up with the other *)

  Instance dy_eq_dec (x y: Dyadic): Decision (x = y).
  Proof. unfold equiv, dy_eq. apply _. Defined.
  Instance dy_mult: RingMult Dyadic := λ x y => dyadic (num x * num y) (den_exp x + den_exp y).
  Instance dy_plus: RingPlus Dyadic := λ x y => dyadic
    (num y ≪ den_exp x + num x ≪ den_exp y)
    (den_exp x + den_exp y).
  Instance dy_opp: GroupInv Dyadic := λ x => dyadic (- num x) (den_exp x).
  Instance dy_0: RingZero Dyadic := dyadic 0 0.
  Instance dy_1: RingOne Dyadic := dyadic 1 0.

  (* eq is nice, giving us a setoid: *)

  Instance: Setoid Dyadic.
  Proof with intuition.
   constructor; intro; unfold equiv, dy_eq...
   apply shiftl_inj with (den_exp y).
   unfold flip.
   rewrite shiftl_order.
   transitivity (num y ≪ den_exp z ≪ den_exp x).
    apply shiftl_proper...
   rewrite (shiftl_order (num y)).
   transitivity (num x ≪ den_exp y ≪ den_exp z).
    apply shiftl_proper...
   apply shiftl_order.
  Qed. (* todo: cleanup. get rewrite to work properly *)

  (* plus is nice, giving us a monoid *)

  Instance: Associative (_: RingPlus Dyadic).
  Proof with intuition.
   repeat intro. unfold dy_plus, equiv, dy_eq. simpl.
   repeat rewrite shiftl_sum_exp.
   repeat apply shiftl_proper...
   repeat rewrite shiftl_sum_base.
   rewrite associativity.
   rewrite (shiftl_order (num z) (den_exp x) (den_exp y)).
   rewrite (shiftl_order (num y) (den_exp x) (den_exp z))...
  Qed. (* todo: too slow *)

  Instance: Commutative dy_plus.
  Proof. repeat intro. unfold dy_plus, equiv, dy_eq. simpl. apply shiftl_proper; ring. Qed. 

  Instance: Proper (dy_eq ==> dy_eq ==> dy_eq) dy_plus.
  Proof with intuition.
   unfold dy_eq, dy_plus. intros x x' E y y' E'. simpl.
   repeat rewrite shiftl_sum_base.
   repeat rewrite shiftl_sum_exp.
   rewrite (shiftl_order _ (den_exp x) (den_exp y)).
   rewrite (shiftl_order _ (den_exp x') (den_exp y)).
   rewrite (shiftl_order _ (den_exp y') (den_exp x)).
   rewrite E', E.
  Admitted. (* hangs:
   repeat rewrite <- shiftl_sum_exp.
   apply (_: Proper ((=) ==> (=) ==> (=)) ring_plus); apply shiftl_proper; ring.
  Qed. *)

  Instance: SemiGroup Dyadic (op:=dy_plus).

  Instance: Monoid Dyadic (op:=dy_plus) (unit:=dy_0).
  Proof with intuition.
   constructor...
    intro. unfold equiv, dy_eq, sg_op, dy_plus. simpl.
    rewrite right_identity, left_absorb, left_identity, right_identity...
   intro. unfold equiv, dy_eq, sg_op, dy_plus. simpl.
   rewrite right_identity, left_absorb, left_identity, right_identity...
  Qed. (* todo: make a tactic that applies absorption and identity laws *)

  (* mult is nice, giving us a monoid *)

  Instance: Associative (_: RingMult Dyadic).
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq.
   simpl. apply shiftl_proper; ring.
  Qed.

  Instance: Commutative (_: RingMult Dyadic).
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq.
   simpl. apply shiftl_proper; ring.
  Qed.

  Instance: Proper (dy_eq ==> dy_eq ==> dy_eq) (_: RingMult Dyadic).
  Proof with intuition.
   unfold dy_eq, dy_mult. intros x x' E y y' E'. simpl.
   rewrite shiftl_sum_exp.
   repeat rewrite shiftl_sum_base.
   repeat rewrite shiftl_sum_exp.
   rewrite (shiftl_order _ (den_exp x) (den_exp y)).
   rewrite <- mult_shiftl.
   rewrite E'.
   rewrite mult_shiftl.
   rewrite (commutativity (num x') (num y)).
   rewrite (shiftl_order _ (den_exp y') (den_exp x)).
   rewrite <- mult_shiftl.
   rewrite E.
   rewrite mult_shiftl.
   rewrite (commutativity (num y) (num x))...
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_mult).

  Instance: Monoid Dyadic (op:=dy_mult) (unit:=dy_1).
  Proof with intuition.
   constructor; [apply _ | |]; intro; unfold equiv, dy_eq, sg_op, dy_mult; simpl.
    do 2 rewrite left_identity...
   do 2 rewrite right_identity...
  Qed.

  Instance: Proper (dy_eq ==> dy_eq) dy_opp.
   unfold dy_eq.
   repeat intro.
   unfold dy_opp.
   simpl.
   do 2 rewrite opp_shiftl.
   rewrite H3.
   reflexivity.
  Qed.

  Instance: Group Dyadic (op:=dy_plus) (unit:=dy_0).
   constructor; try apply _; unfold sg_op, dy_plus, equiv, dy_eq;
    simpl; intro;
    rewrite left_absorb;
    rewrite right_identity;
    rewrite <- shiftl_sum_base;
    [rewrite ginv_r | rewrite ginv_l];
    rewrite left_absorb;
    reflexivity.
  Qed.

  Instance: Ring Dyadic.
  Proof with intuition.
   repeat (constructor; try apply _).
    intros.
    unfold dy_mult, dy_plus, equiv, dy_eq.
    simpl.
    repeat rewrite shiftl_sum_exp.
    rewrite distribute_l.
    repeat rewrite shiftl_sum_base.
    rewrite mult_shiftl.
    rewrite mult_shiftl.
    apply (_: Proper ((=)==>(=)==>(=)) (_: RingPlus Z)).
     apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
     rewrite shiftl_order.
     apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
     apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
     rewrite shiftl_order...
    apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
    rewrite shiftl_order.
    apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
    apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
    rewrite shiftl_order.
    apply (_: Proper ((=)==>(=)==>(=)) shiftl)...
   intros.
   unfold dy_mult, dy_plus, equiv, dy_eq.
   simpl.
   repeat rewrite shiftl_sum_exp.
   rewrite distribute_r.
   repeat rewrite shiftl_sum_base.
   rewrite (commutativity (num a ≪ den_exp b)).
   rewrite (commutativity (num b ≪ den_exp a)).
   rewrite mult_shiftl.
   rewrite mult_shiftl.
   rewrite (shiftl_order _ (den_exp c) (den_exp a)).
   rewrite (shiftl_order _ (den_exp c) (den_exp a)).
   rewrite (commutativity (num b)).
   rewrite (commutativity (num a))...
  Qed. (* todo: way too long *)

  (* now if we already have a rationals implementation... *)

  Context
    `{Rationals Q}
    `{!Ring_Morphism (ZtoQ: Z → Q)}. (* specialization of integers_to_ring Z Q *)

  (* We don't make (Z >-> Q) a coercion because it could be computationally expensive
   and we want to see where it's called. *)

  (* we can easily inject: *)

  Program Definition inject (d: Dyadic): Q := ZtoQ (num d) * // ZtoQ (den d).

  Next Obligation. Proof with intuition.
   intro.
   apply (@shiftl_nonzero Z _ _ _ _ _ _ N _ _ _ _ _ _ 1 (den_exp d)).
     (* todo: pretty version too slow *)
    intro. apply (@zero_ne_one Z _ _ _ _).
    symmetry...
   apply (injective ZtoQ).
   rewrite preserves_0...
  Qed.

  Instance: Proper ((=) ==> (=))%signature inject.
  Proof with try apply _.
   repeat intro.
   apply theory.fields.equal_quotients. simpl.
   unfold den, compose.
   do 2 rewrite <- preserves_mult.
   do 2 rewrite mult_shiftl.
   do 2 rewrite right_identity.
   unfold equiv, dy_eq in H5.
   rewrite H5.
   reflexivity.
  Qed. (* todo: clean up *)

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

  Lemma inject_0: inject 0 = 0.
  Proof. unfold inject. simpl. rewrite preserves_0. apply left_absorb. Qed.

  Instance: Ring_Morphism inject.
  Admitted.

  (* the hybrid data type: *)

  Definition Hybrid := sum Dyadic Q.

  Definition hybrid_Q (h: Hybrid): Q := match h with inl x => inject x | inr x => x end.

  (* operations on Hybrid: *)

  Instance: GroupInv Hybrid := λ x =>
    match x with
    | inl d => inl (-d)
    | inr q => inr (-q)
    end.

  Instance: Equiv Hybrid := λ x y =>
    match x, y with
    | inl d, inl e => d = e
    | inr p, inr q => p = q
    | inl d, inr q => inject d = q (* or something more clever *)
    | inr q, inl d => q = inject d
    end.

  Instance: RingMult Hybrid := λ x y =>
    match x, y with
    | inl d, inl e => inl (d * e)
    | inr p, inr q => inr (p * q)
    | inl d, inr q => inr (inject d * q)
    | inr q, inl d => inr (q * inject d)
    end.

  Instance: RingPlus Hybrid := λ x y =>
    match x, y with
    | inl d, inl e => inl (d + e)
    | inr p, inr q => inr (p + q)
    | inl d, inr q => inr (inject d + q)
    | inr q, inl d => inr (q + inject d)
    end.

  Instance: RingZero Hybrid := inl 0.
  Instance: RingOne Hybrid := inl 1.

  Program Instance: MultInv Hybrid := inr ∘ mult_inv ∘ hybrid_Q.

  Next Obligation.
   destruct x.
    simpl.
    intro.
    apply H4.
    unfold equiv. simpl.
    admit. (*
    apply (injective inject).
    rewrite inject_0.
    assumption. *)
   unfold equiv in H4. simpl in H4.
   admit. (*
   rewrite inject_0 in H4.
   assumption. *)
  Qed.

  Instance: Π x y: Hybrid, Decision (x = y).
  Admitted.

  (* structures on Hybrid: *)

  (*
  Instance: Rationals Hybrid.
  Admitted.
  *)

End contents.
