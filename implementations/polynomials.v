Require Import
  Coq.Lists.List
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.vectorspace
  MathClasses.theory.rings
  Ring.
Import ListNotations.

Section contents.
  Context R `{Ring R}.
  Add Ring R: (stdlib_ring_theory R).

  Definition poly := list R.

  Coercion poly_constant (c : R) : poly := [c].

  Global Instance poly_zero: Zero poly := [].
  Global Instance poly_one: One poly := poly_constant 1.

  Definition all (l: list Prop): Prop := fold_left and l True.
  Lemma all_cons P Ps: all (P::Ps) ↔ P ∧ all Ps.
  Proof.
    unfold all.
    revert P; generalize True as Q.
    induction Ps as [|P' Ps IH]; intros.
    { cbn; tauto. }
    change (fold_left and (P' :: Ps) (Q ∧ P) ↔ P ∧ fold_left and (P'::Ps) Q).
    rewrite !IH.
    transitivity (P' ∧ (P ∧ fold_left and Ps Q)); try tauto.
    now rewrite <- (IH Q P).
  Qed.
  Arguments all: simpl never.

  Definition poly_eq_zero: poly → Prop := all ∘ map ((=) 0).
  Corollary poly_eq_zero_cons x p: poly_eq_zero (x::p) ↔ x = 0 ∧ poly_eq_zero p.
  Proof.
    unfold poly_eq_zero, compose; cbn; rewrite all_cons.
    intuition now symmetry.
  Qed.

  Lemma poly_eq_zero_ind (P: poly → Prop) (case_nil: P [])
        (casecons: ∀ x p, x = 0 → poly_eq_zero p → P p → P (x::p))
        p: poly_eq_zero p → P p.
  Proof.
    induction p as [|x p IH]; auto.
    intros [??]%poly_eq_zero_cons.
    eauto.
  Qed.

  Global Instance poly_eq: Equiv poly :=
    fix F p q :=
    match p, q with
    | [], _ => poly_eq_zero q
    | _, [] => poly_eq_zero p
    | h :: t, h' :: t' => h = h' ∧ F t t'
    end.

  Lemma poly_eq_p_zero p: (p = 0) ↔ poly_eq_zero p.
  Proof. now destruct p. Qed.

  Instance: Reflexive poly_eq.
  Proof with intuition. repeat intro. induction x... split... Qed.

  Lemma poly_eq_cons :
    ∀ (a b : R) (p q : poly), (a = b /\ poly_eq p q) <-> poly_eq (a :: p) (b :: q).
  Proof. easy. Qed.

  Lemma poly_eq_ind (P: poly → poly → Prop)
        (case_0: ∀ p p', poly_eq_zero p → poly_eq_zero p' → P p p')
        (case_cons: ∀ x x' p p', x = x' → p = p' → P p p' → P (x::p) (x'::p'))
        p: ∀ p', p = p' → P p p'.
  Proof.
    induction p as [|x p IH]; intros [|x' p'] eqxy.
    1,2,3: now apply case_0.
    destruct eqxy.
    apply case_cons; auto.
  Qed.

  Lemma poly_eq_zero_trans p q: poly_eq_zero p → poly_eq_zero q → p = q.
  Proof.
    revert q.
    induction p as [|x p IH]; intros ? eqp eqq; auto.
    destruct q as [|y q]; auto.
    rewrite poly_eq_zero_cons in *.
    rewrite <- poly_eq_cons.
    destruct eqp as [-> ?], eqq as [-> ?]; split; eauto.
    now apply IH.
  Qed.

  Instance: Symmetric poly_eq.
  Proof.
    intros p p' eqp.
    pattern p, p'; apply poly_eq_ind; auto; clear p p' eqp.
    - now intros; apply poly_eq_zero_trans.
    - intros ???? eqx eqp IH.
      rewrite <- poly_eq_cons; auto.
  Qed.

  Instance poly_eq_zero_proper: Proper (poly_eq ==> iff) poly_eq_zero.
  Proof.
    apply proper_sym_impl_iff.
    { apply _. }
    red; refine (poly_eq_ind _ _ _).
    - intros; hnf; auto.
    - unfold impl; intros ???? eqx eqp IH.
      rewrite !poly_eq_zero_cons, eqx; tauto.
  Qed.

  Instance: Transitive poly_eq.
  Proof.
    intros ??? eqxy; revert z.
    pattern x, y; refine (poly_eq_ind _ _ _ x y eqxy); clear x y eqxy.
    { intros x y x0 y0 z eqz.
      apply poly_eq_zero_trans; auto.
      now rewrite <- eqz. }
    intros ???? eqx eqp IH z eqz.
    destruct z as [|x'' p''].
    { eapply poly_eq_zero_proper; eauto.
      now split. }
    destruct eqz as [eqx' eqp']; split; eauto.
  Qed.

  Global Instance: Setoid poly.
  Proof. split; try apply _. Qed.

  Global Instance: Plus poly := fix F p q :=
    match p, q with
    | [], _ => q
    | _, [] => p
    | h :: t, h' :: t' => h + h' :: F t t'
    end.

  Lemma poly_eq_zero_plus_l p q: poly_eq_zero p → p + q = q.
  Proof.
    intro eqp; revert q.
    induction eqp as [|x p eqx eqp IH] using poly_eq_zero_ind.
    { easy. }
    intros [|y q].
    { cbn -[poly_eq_zero].
      rewrite poly_eq_zero_cons; auto. }
    cbn; split; auto.
    ring [eqx].
  Qed.

  Instance plus_commutative: Commutative (+).
  Proof with (try easy); cbn.
    intro.
    induction x as [|x p IH]; intros [|y q]...
    split; auto; ring.
  Qed.

  Corollary poly_eq_zero_plus_r p q: poly_eq_zero q → p + q = p.
  Proof.
    rewrite commutativity.
    apply poly_eq_zero_plus_l.
  Qed.

  Corollary poly_eq_zero_plus p q: poly_eq_zero p → poly_eq_zero q → poly_eq_zero (p+q).
  Proof.
    intro.
    rewrite <- !poly_eq_p_zero; intro.
    now rewrite poly_eq_zero_plus_l.
  Qed.

  Global Instance poly_plus_proper: Proper (poly_eq ==> poly_eq ==> poly_eq) (+).
  Proof.
    unfold Proper, respectful.
    refine (poly_eq_ind _ _ _).
    { intros p p' zp zp' q q' eqq.
      rewrite !poly_eq_zero_plus_l; auto. }
    intros ???? eqx eqp IH.
    refine (poly_eq_ind _ _ _).
    { intros q q' zq zq'.
      rewrite !poly_eq_zero_plus_r; auto.
      cbn; auto. }
    intros y y' q q' eqy eqq _.
    cbn; split; eauto.
    ring [eqx eqy].
  Qed.

  Instance plus_associative: Associative (+).
  Proof with try easy.
    do 2 red; induction x as [|x p IH]...
    intros [|y q]...
    intros [|z r]...
    cbn; split; auto.
    ring.
  Qed.

  Instance plus_left_id: LeftIdentity (+) 0.
  Proof. now intro; rewrite poly_eq_zero_plus_l. Qed.
  Instance plus_right_id: RightIdentity (+) 0.
  Proof. now intro; rewrite poly_eq_zero_plus_r. Qed.

  Instance poly_plus_monoid: Monoid poly.
  Proof. repeat (split; try apply _). Qed.

  Global Instance: Negate poly := map (-).

  Lemma poly_negate_zero p: poly_eq_zero p ↔ poly_eq_zero (-p).
  Proof.
    induction p as [|x p IH].
    { easy. }
    cbn.
    rewrite !poly_eq_zero_cons, IH.
    enough (x = 0 ↔ -x = 0) by tauto.
    split; intro eq0; ring [eq0].
  Qed.

  Instance poly_negate_proper: Proper (poly_eq ==> poly_eq) (-).
  Proof.
    refine (poly_eq_ind _ _ _).
    { now intros ?? ->%poly_negate_zero%poly_eq_p_zero ->%poly_negate_zero%poly_eq_p_zero. }
    intros ???? eqx eqp IH.
    cbn; split; eauto.
  Qed.

  Instance poly_negate_l: LeftInverse (+) (-) 0.
  Proof.
    intro; rewrite poly_eq_p_zero.
    induction x as [|x p IH]; cbn.
    { easy. }
    rewrite poly_eq_zero_cons; split; auto.
    ring.
  Qed.

  Instance poly_negate_r: RightInverse (+) (-) 0.
  Proof. now intro; rewrite commutativity, left_inverse. Qed.

  Instance poly_plus_abgroup: AbGroup poly.
  Proof. repeat (split; try apply _). Qed.

  Global Instance: ScalarMult R poly := fix F c q :=
    match q with
    | [] => 0
    | d :: q1 => c*d :: F c q1
    end.

  Lemma poly_scalar_mult_0_r q c: poly_eq_zero q → poly_eq_zero (c · q).
  Proof.
    induction q as [|x q IH].
    { easy. }
    cbn.
    rewrite !poly_eq_zero_cons.
    intros [-> ?]; split; auto.
    ring.
  Qed.

  Instance poly_scalar_mult_proper: Proper ((=) ==> (=) ==> (=)) (·).
  Proof.
    intros c c' eqc p p' eqp.
    revert p p' eqp; refine (poly_eq_ind _ _ _).
    { now intros; apply poly_eq_zero_trans; apply poly_scalar_mult_0_r. }
    intros ???? eqx eqp IH.
    split; auto; cbn.
    ring [eqx eqc].
  Qed.

  Lemma poly_scalar_mult_1_r x: x · 1 = [x].
  Proof. cbn; split; [ring|easy]. Qed.
  Instance poly_scalar_mult_1_l: LeftIdentity (·) 1.
  Proof.
    red; induction y as [|y p IH]; [easy|cbn].
    split; auto; ring.
  Qed.

  Instance poly_scalar_mult_dist_l: LeftHeteroDistribute (·) (+) (+).
  Proof.
    intros a p.
    induction p as [|x p IH]; intros [|y q]; [easy..|cbn].
    split; auto; ring.
  Qed.
  Instance poly_scalar_mult_dist_r: RightHeteroDistribute (·) (+) (+).
  Proof.
    intros a b x.
    induction x as [|x p IH]; [easy|cbn].
    split; auto; ring.
  Qed.
  Instance poly_scalar_mult_assoc: HeteroAssociative (·) (·) (·) (.*.).
  Proof.
    intros a b x.
    induction x as [|p x IH]; [easy|cbn].
    split; auto; ring.
  Qed.

  Lemma poly_scalar_mult_0_l q c: c = 0 → poly_eq_zero (c · q).
  Proof.
    intros ->.
    induction q as [|x q IH]; [easy|cbn].
    rewrite poly_eq_zero_cons; split; auto.
    ring.
  Qed.

  Global Instance: Mult poly := fix F p q :=
    match p with
    | [] => 0
    | c :: p1 => c · q + (0 :: F p1 q)
    end.

  Lemma poly_mult_0_l p q: poly_eq_zero p → poly_eq_zero (p * q).
  Proof.
    induction 1 using poly_eq_zero_ind; [easy|cbn].
    apply poly_eq_zero_plus.
    - now apply poly_scalar_mult_0_l.
    - rewrite poly_eq_zero_cons; auto.
  Qed.

  Lemma poly_mult_0_r p q: poly_eq_zero q → poly_eq_zero (p * q).
  Proof.
    induction p as [|x p IH]; [easy|cbn].
    intro eq0.
    apply poly_eq_zero_plus.
    - now apply poly_scalar_mult_0_r.
    - rewrite poly_eq_zero_cons; auto.
  Qed.

  Instance poly_mult_proper: Proper ((=) ==> (=) ==> (=)) (.*.).
  Proof.
    refine (poly_eq_ind _ _ _).
    { intros ?? zp zp' q q' eqq.
      now apply poly_eq_zero_trans; apply poly_mult_0_l. }
    intros ???? eqx eqp IH q q' eqq.
    cbn.
    apply poly_plus_proper.
    { now rewrite eqx, eqq. }
    split; auto.
    now apply IH.
  Qed.

  Instance poly_mult_left_distr: LeftDistribute (.*.) (+).
  Proof.
    intros p q r.
    induction p as [|x p IH]; [easy|cbn].
    rewrite (distribute_l x q r ).
    rewrite <- !associativity; apply poly_plus_proper; [easy|].
    rewrite associativity, (commutativity (0::p*q)), <- associativity.
    apply poly_plus_proper; [easy|].
    cbn; split; [ring|easy].
  Qed.

  Lemma poly_mult_cons_r p q x: p * (x::q) = x · p + (0 :: p * q).
  Proof.
    induction p as [|y p IH]; cbn; auto.
    split; auto.
    rewrite IH, !associativity, (commutativity (y · q)).
    split; try easy.
    ring.
  Qed.

  Instance poly_mult_comm: Commutative (.*.).
  Proof.
    intros p.
    induction p as [|x p IH].
    { cbn; intro.
      now apply poly_mult_0_r. }
    intros [|y q]; cbn.
    { rewrite poly_eq_zero_cons; split; auto.
      now apply poly_mult_0_r. }
    split. 1: ring.
    rewrite !poly_mult_cons_r, !associativity.
    apply poly_plus_proper.
    { apply commutativity. }
    rewrite <- poly_eq_cons; split; auto.
    apply IH.
  Qed.

  Instance poly_mult_right_distr: RightDistribute (.*.) (+).
  Proof.
    intros p q r.
    now rewrite commutativity, distribute_l, !(commutativity r).
  Qed.

  Instance poly_mult_1_l: LeftIdentity (.*.) 1.
  Proof.
    intro; cbn.
    rewrite poly_scalar_mult_1_l, poly_eq_zero_plus_r; auto.
    now split.
  Qed.

  Instance poly_mult_1_r: RightIdentity (.*.) 1.
  Proof.
    intro; rewrite commutativity; apply left_identity.
  Qed.

  Instance poly_mult_assoc: Associative (.*.).
  Proof with (try easy); cbn.
    intros x.
    induction x as [|x p IH]...
    intros q r; cbn.
    rewrite distribute_r.
    apply poly_plus_proper; cbn -[poly_eq].
    { clear IH.
      induction q as [|y q IH]...
      rewrite distribute_l, <- associativity.
      apply poly_plus_proper...
      split; auto.
      ring. }
    assert (0 · r = 0) as ->.
    { now rewrite poly_eq_p_zero; apply poly_scalar_mult_0_l. }
    cbn; split; eauto.
    now rewrite IH.
  Qed.

  Global Instance poly_ring: Ring poly.
  Proof. repeat (split; try apply _). Qed.

  Global Instance poly_module : @Module R poly Ae Aplus Amult Azero Aone Anegate
                                               poly_eq (+) 0 (-) (·).
  Proof. split; apply _. Qed.
End contents.

(*

Section test.

  Context `{Ring R} (x y: poly (poly (poly (poly R)))).

  Goal x + y == x * y.
    set (d := Plus_instance_0 ).
    set (u := Mult_instance_0).
    set (t := poly (poly R)).
    unfold poly_zero.

*)
