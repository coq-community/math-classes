Set Automatic Introduction.
Set Automatic Coercions Import.

Require Import
 Relation_Definitions Morphisms Program Ring
 abstract_algebra peano_naturals theory.rings orders.semigroup
 theory.ua_transference.
Require Export
 interfaces.naturals.

Lemma to_semiring_involutive N `{Naturals N} N2 `{Naturals N2}: ∀ a: N,
 naturals_to_semiring N2 N (naturals_to_semiring N N2 a) = a.
Proof.
  intros a.
  pose proof (proj2 (@categories.initials_unique' (variety.Object semiring.theory)
    _ _ _ _ _ (semiring.object N) (semiring.object N2) _ naturals_initial _ naturals_initial) tt a) as P.
  apply P. (* todo: separate pose necessary due to Coq bug *)
Qed.

Lemma to_semiring_unique `{Naturals N} `{SemiRing SR} (f: N → SR) `{!SemiRing_Morphism f}:
 ∀ x, f x = naturals_to_semiring N SR x.
Proof.
 intros. symmetry.
 pose proof (@semiring.mor_from_sr_to_alg _ _ _ (semiring.variety N) _ _ _ (semiring.variety SR) (λ _, f) _).
 set (@variety.arrow semiring.theory _ _ _ (semiring.variety N) _ _ _ (semiring.variety SR) (λ _, f) _).
 apply (naturals_initial _ a tt x).
Qed.

Lemma to_semiring_unique' `{Naturals N} `{SemiRing SR} (f g: N → SR) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} :
  f = g.
Proof.
  intro.
  rewrite (to_semiring_unique f).
  rewrite (to_semiring_unique g).
  reflexivity.
Qed.

Lemma morphisms_involutive `{Naturals N} `{Naturals N2} (f: N → N2) (g: N2 → N) 
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} : ∀ a, f (g a) = a.
Proof.
 intros.
 rewrite (to_semiring_unique g).
 rewrite (to_semiring_unique f).
 apply (to_semiring_involutive _ _).
Qed.

Lemma to_semiring_twice N `{Naturals N} N2 `{Naturals N2} SR `{SemiRing SR} x : 
  naturals_to_semiring N2 SR (naturals_to_semiring N N2 x) = naturals_to_semiring N SR x.
Proof.
  replace (naturals_to_semiring N2 SR (naturals_to_semiring N N2 x))
    with ((naturals_to_semiring N2 SR  ∘ naturals_to_semiring N N2) x) by reflexivity.
  apply to_semiring_unique; apply _.
Qed.

Lemma to_semiring_self `{Naturals N} x : x = naturals_to_semiring N N x.
Proof.
  replace x with (id x) by auto.
  apply to_semiring_unique; apply _.
Qed.

Lemma to_semiring_injective `{Naturals N} `{SemiRing A}  
   (f: A → N) (g: N → A) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}: Injective g.
Proof.
  constructor. 2: constructor; apply _.
  intros x y E.
  rewrite <- (to_semiring_unique' (f ∘ g) id x).
  rewrite <- (to_semiring_unique' (f ∘ g) id y).
  unfold compose. rewrite E. reflexivity.
Qed.

Instance naturals_to_naturals_injective `{Naturals N} `{Naturals N2} (f: N → N2) `{!SemiRing_Morphism f}: 
  Injective f.
Proof. 
  apply to_semiring_injective with (naturals_to_semiring N2 N); apply _. 
Qed.

Section retract_is_nat.
  Context `{Naturals N} `{SemiRing SR}.
  Context (f : N → SR) `{!Inverse f} `{!Surjective f} `{!SemiRing_Morphism f} `{!SemiRing_Morphism (inverse f)}.

  (* If we make this an instance, then instance resolution will result in an infinite loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR := λ R _ _ _ _ , naturals_to_semiring N R ∘ inverse f.

  Section for_another_semiring.
    Context `{SemiRing R}.

    Instance: SemiRing_Morphism (naturals_to_semiring N R ∘ inverse f).

    Context (h :  SR → R) `{!SemiRing_Morphism h}. 
     
    Lemma same_morphism: naturals_to_semiring N R ∘ inverse f = h.
    Proof with auto.
      intro x.
      pose proof (to_semiring_unique (h ∘ f)) as E.
      unfold compose in *.
      rewrite <-E. apply sm_proper. 
      apply jections.surjective_applied.
    Qed.
  End for_another_semiring.

  (* If we make this an instance, then instance resulution will result in an infinite loop *)
  Program Definition retract_is_nat: @Naturals SR _ _ _ _ _ retract_is_nat_to_sr. 
  Proof. 
    esplit. (* for some reason split doesn't work... *)
    intros. apply natural_initial. intros.
    apply same_morphism. auto. 
  Qed.
End retract_is_nat.

Section borrowed_from_nat.
  Context `{Naturals N}.

  Import universal_algebra.
  Import notations.

  Lemma induction
    (P: N → Prop) `{!Proper (equiv ==> iff)%signature P}:
    P 0 → (∀ n, P n → P (1 + n)) → ∀ n, P n.
  Proof with auto.
   intros.
   rewrite <- (to_semiring_involutive _ nat n).
   set (m := naturals_to_semiring _ nat n). (* This [set] is suddenly needed in 12609... Todo: File a ticket. *)
   induction m.
    change (P (naturals_to_semiring nat _ (0:nat))).
    rewrite preserves_0...
   change (P (naturals_to_semiring nat _ (1 + m))).
   rewrite preserves_plus, preserves_1...
  Qed.

  Lemma from_nat_stmt:
    ∀ (s: Statement varieties.semiring.theory) (w : Vars varieties.semiring.theory (varieties.semiring.object N) nat),
     (∀ v: Vars varieties.semiring.theory (varieties.semiring.object nat) nat,
       eval_stmt varieties.semiring.theory v s) → eval_stmt varieties.semiring.theory w s.
  Proof.
   pose proof (@naturals_initial nat _ _ _ _ _ _ _) as AI.
   pose proof (@naturals_initial N _ _ _ _ _ _ _) as BI.
   intros s w ?.
   apply (transfer_statement _ (@categories.initials_unique' semiring.Object _ _ _ _ _
     (semiring.object nat) (semiring.object N) _ AI _ BI)).
   intuition.
  Qed.

  Variables (x y z: N).

  Let three_vars (_: unit) v := match v with 0%nat => x | 1%nat => y | _ => z end.
  Let two_vars (_: unit) v := match v with 0%nat => x | _ => y end.
  Let no_vars (_: unit) (v: nat) := 0.

  Local Notation x' := (Var varieties.semiring.sig _ 0 tt).
  Local Notation y' := (Var varieties.semiring.sig _ 1 tt).
  Local Notation z' := (Var varieties.semiring.sig _ 2%nat tt).

  (* Some clever autoquoting tactic might make what follows even more automatic. *)
  (* The ugly [pose proof ... . apply that_thing.]'s are because of Coq bug 2185. *)

  Global Instance: LeftCancellation (=) (λ x, True) (+).
  Proof.
   intros u _ v w.
    pose proof (from_nat_stmt (x' + y' === x' + z' -=> y' === z')
      (λ _ d, match d with 0%nat => u | 1%nat => v | _ => w end)) as P.
    simpl in P.
    apply P. intro. simpl. apply Plus.plus_reg_l.
  Qed.

  Global Instance: LeftCancellation (=) (λ x, x ≠ 0) ring_mult.
  Proof.
   intros u E v w.
    pose proof (from_nat_stmt ((x' === 0 -=> Ext _ False) -=> x' * y' === x' * z' -=> y' === z')
     (λ _ d, match d with 0%nat => u | 1%nat => v | _ => w end)) as P.
    apply P. intro. simpl. apply Mult_mult_reg_l. assumption.
  Qed.

  Global Instance: ZeroNeOne N.
  Proof.
   pose proof (from_nat_stmt (0 === 1 -=> Ext _ False) no_vars) as P.
   apply P. discriminate.
  Qed.

  Global Instance: ZeroNeTwo N.
  Proof.
   pose proof (from_nat_stmt (0 === 2 -=> Ext _ False) no_vars) as P.
   apply P. discriminate.
  Qed.

  Lemma zero_sum: x + y = 0 → x = 0 ∧ y = 0.
  Proof.
   pose proof (from_nat_stmt (x' + y' === 0 -=> Conj _ (x' === 0) (y' === 0)) two_vars) as P.
   apply P. intro. simpl. apply Plus.plus_is_O.
  Qed.
  
  Lemma one_sum: x + y = 1 → (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1).
  Proof. 
   pose proof (from_nat_stmt (x' + y' === 1 -=> Disj _ (Conj _ (x' === 1) (y' === 0)) (Conj _ (x' === 0) (y' === 1))) two_vars) as P.
   apply P. intros. simpl. intros. edestruct Plus.plus_is_one; eauto.
  Qed.

  Lemma nz_mult_nz: y ≠ 0 → x ≠ 0 → y * x ≠ 0.
  Proof.
   pose proof (from_nat_stmt ((y' === 0 -=> Ext _ False) -=>
     (x' === 0 -=> Ext _ False) -=> (y' * x' === 0 -=> Ext _ False)) two_vars) as P.
   unfold not. apply P. intro. simpl. apply Mult_nz_mult_nz.
  Qed.
End borrowed_from_nat.

Section contents.
  Context `{Naturals N}.
  Add Ring N: (stdlib_semiring_theory N).

  Lemma nz_one_plus_zero x : 1 + x ≠ 0.
  Proof.
    intro E.
    destruct (zero_sum 1 x E). 
    apply zero_ne_one. symmetry. auto.
  Qed.  

  Obligation Tactic := idtac.
  Global Program Instance: ∀ x y: N, Decision (x = y) | 10 := λ x y,
    match Peano_dec.eq_nat_dec (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y) with
    | left E => left _
    | right E => right _
    end.
 
  Next Obligation.
   intros.
   rewrite <- (to_semiring_involutive _ nat x), <- (to_semiring_involutive _ nat y).
   rewrite E. reflexivity.
  Qed.

  Next Obligation.
   intros x y ? E ? F. apply E. rewrite F. reflexivity.
  Qed.

  Global Instance: ZeroProduct N.
  Proof with intuition.
   intros a b E.
   destruct (decide (a = 0))...
   destruct (decide (b = 0))...
   exfalso. apply (nz_mult_nz b a)...
  Qed.

  (* NatDistance instances are all equivalent, because their behavior is fully
   determined by the specification. *)

  Program Lemma nat_distance_unique_respectful {a b: NatDistance N}:
    ((=) ==> (=) ==> (=))%signature a b.
  Proof with intuition.
   intros ? ? x1 y1 E x2 y2 F.
   destruct a as [z1 [A|A]], b as [z2 [B|B]]; simpl.
   apply (left_cancellation (+) x1)... rewrite A, E, B...
   destruct (zero_sum z1 z2).
     apply (left_cancellation (+) x1)...
     rewrite associativity, A, F, B, E. ring.
     transitivity 0...
   destruct (zero_sum z1 z2).
     rewrite commutativity.
     apply (left_cancellation (+) y1)...
     rewrite associativity, B, <-F, A, E. ring.
     transitivity 0...
   apply (left_cancellation (+) x2)...
   rewrite A, E, F, B...
  Qed.

  Lemma nat_distance_unique {a b: NatDistance N} x: a x = b x.
  Proof. intro. apply nat_distance_unique_respectful; reflexivity. Qed.

  Global Instance nat_distance_proper `{!NatDistance N}: Proper ((=) ==> (=) ==> (=)) (λ x y: N, ` (nat_distance x y)).
    (* Program *should* allow us to write plain nat_distance instead of the
       above eta, like in nat_distance_unique_respectful. Matthieu confirms it's a bug. *)
  Proof. apply nat_distance_unique_respectful. Qed.

  Global Program Instance: NatDistance N | 10 := λ x y: N,
    naturals_to_semiring _ N (proj1_sig (nat_distance (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y))).
      (* Removing the proj1_sig here results in an explosion of proof obligations. Todo: investigate. *)
  Next Obligation.
   intros x y.
   destruct nat_distance as [z [F|F]]; simpl.
   left.
    rewrite <- (to_semiring_involutive N nat y).
    rewrite <- F.
    rewrite preserves_sg_op.
    rewrite (to_semiring_involutive N nat).
    reflexivity.
   right.
    rewrite <- (to_semiring_involutive N nat x).
    rewrite <- F.
    rewrite preserves_sg_op.
    rewrite (to_semiring_involutive N nat).
    reflexivity.
  Qed.

End contents.
