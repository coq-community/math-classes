Set Automatic Introduction.
Set Automatic Coercions Import.

Require Import
 Relation_Definitions Morphisms Program Ring
 abstract_algebra peano_naturals theory.rings orders.semigroup
 theory.ua_transference.
Require Export
 interfaces.naturals.

Lemma to_semiring_unique `{Naturals N} SR `{SemiRing SR} (f: N → SR) {h: SemiRing_Morphism f}:
 ∀ x, f x = naturals_to_semiring N SR x.
Proof.
 intros. symmetry.
 pose proof (@semiring.mor_from_sr_to_alg _ _ _ (semiring.variety N) _ _ _ (semiring.variety SR) (λ _, f) _).
 set (@variety.arrow semiring.theory _ _ _ (semiring.variety N) _ _ _ (semiring.variety SR) (λ _, f) _).
 apply (naturals_initial _ a tt x).
Qed.

Lemma to_semiring_unique' `{Naturals N} `{SemiRing SR} (f g: N → SR):
 SemiRing_Morphism f → SemiRing_Morphism g → f = g.
Proof.
 intros. intro.
 rewrite (to_semiring_unique _ f _).
 rewrite (to_semiring_unique _ g _).
 reflexivity.
Qed.

Lemma to_semiring_involutive A `{Naturals A} B `{Naturals B}: ∀ a: A,
 naturals_to_semiring B A (naturals_to_semiring A B a) = a.
Proof.
 intros.
 pose proof (proj2 (@categories.initials_unique' (variety.Object semiring.theory)
   _ _ _ _ _ (semiring.object A) (semiring.object B) _ naturals_initial _ naturals_initial) tt a).
 apply H1. (* todo: separate pose necessary due to Coq bug *)
Qed.

Lemma morphisms_involutive `{Naturals A} `{Naturals B} (f: A → B) (g: B → A)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}:
    ∀ a, f (g a) = a.
Proof.
 intros.
 rewrite (to_semiring_unique _ g _).
 rewrite (to_semiring_unique _ f _).
 apply (to_semiring_involutive _ _).
Qed.

Lemma to_semiring_twice `{Naturals A} `{Naturals B} `{SemiRing SR} x : 
  naturals_to_semiring B SR (naturals_to_semiring A B x) = naturals_to_semiring A SR x.
Proof.
  replace (naturals_to_semiring B SR (naturals_to_semiring A B x))
    with ((naturals_to_semiring B SR  ∘ naturals_to_semiring A B) x) by reflexivity.
  apply to_semiring_unique; apply _.
Qed.

Lemma to_semiring_self `{Naturals A} x : x = naturals_to_semiring A A x.
Proof.
  replace x with (id x) by auto.
  apply to_semiring_unique; apply _.
Qed.

Instance: Params (@natural_precedes) 8.
Instance: Params (@precedes) 2.

Lemma preserves_naturals_order_back `{Naturals A} `{Naturals B} (f: A → B) `{!SemiRing_Morphism f} (x y: A): 
  f x ≤ f y → x ≤ y.
Proof.
 intros.
 pose proof (_: Proper ((=) ==> (=) ==> iff) precedes).
 pose proof (naturals_to_semiring_mor B A _).
 rewrite <- (morphisms_involutive (naturals_to_semiring _ _) f y).
 rewrite <- (morphisms_involutive (naturals_to_semiring _ _) f x).
 apply preserves_sg_order. apply _.
 assumption.
Qed.

Lemma preserves_naturals_order `{Naturals A} `{Naturals B} (f: A → B) `{!SemiRing_Morphism f} (x y: A): 
  x ≤ y ↔ f x ≤ f y.
Proof.
 split. apply preserves_sg_order. apply _.
 apply preserves_naturals_order_back. apply _.
Qed.

Section contents.

Context `{Naturals N}.

Section retract_is_nat.
  Context `{SemiRing SR} .
  Context (f : N → SR) (g : SR → N) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}.
  Context (f_retraction_g : ∀ x : SR, f (g x) = x).

  (* If we make this an instance, then instance resulution will result in an infinite loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR := λ R _ _ _ _ , naturals_to_semiring N R ∘ g.

  Section for_another_semiring.
    Context `{SemiRing R}.

    Instance: SemiRing_Morphism (naturals_to_semiring N R ∘ g).
    Context (h :  SR → R) `{!SemiRing_Morphism h}. 
     
    Lemma same_morphism: naturals_to_semiring N R ∘ g = h.
    Proof with auto.
      intro x. 
      rewrite <-f_retraction_g at 2.
      assert (H3:=to_semiring_unique R (h ∘ f)).
      unfold compose in *. 
      unfold equiv in H3. unfold ext_eq in H3. rewrite H3. 
      apply reflexivity.
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

Add Ring N: (stdlib_semiring_theory N).

Let hint0 := naturals_to_semiring_mor N nat _.
Let hint1 := naturals_to_semiring_mor nat N _.

Section borrowed_from_nat.

  Import universal_algebra.
  Import notations.

  Global Instance: TotalOrder (natural_precedes (N:=N)).
  Proof.
   intros x y. 
   destruct (total_order (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y)); [left | right];
    rewrite <- preserves_naturals_order in H0; try apply _; assumption. 
  Qed.

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

  Global Instance: ∀ x: N, Injective (ring_plus x).
  Proof.
   intros u.
   constructor.
    intros v w.
    pose proof (from_nat_stmt (x' + y' === x' + z' -=> y' === z')
      (λ _ d, match d with 0%nat => u | 1%nat => v | _ => w end)) as P.
    simpl in P.
    apply P. intro. simpl. apply Plus.plus_reg_l.
   constructor; apply _.
  Qed.

  Global Instance mult_injective: ∀ x: N, x ≠ 0 → Injective (ring_mult x).
  Proof.
   intros u E.
   constructor.
    intros v w.
    pose proof (from_nat_stmt ((x' === 0 -=> Ext _ False) -=> x' * y' === x' * z' -=> y' === z')
     (λ _ d, match d with 0%nat => u | 1%nat => v | _ => w end)) as P.
    apply P. intro. simpl. apply Mult_mult_reg_l. assumption.
   constructor; apply _.
  Qed.

  Global Instance: ZeroNeOne N.
  Proof.
   pose proof (from_nat_stmt (0 === 1 -=> Ext _ False) no_vars).
   apply H0. discriminate.
  Qed.

  Lemma zero_sum: x + y = 0 → x = 0 ∧ y = 0.
  Proof.
   pose proof (from_nat_stmt (x' + y' === 0 -=> Conj _ (x' === 0) (y' === 0)) two_vars).
   apply H0. intro. simpl. apply Plus.plus_is_O.
  Qed.

  Lemma nz_mult_nz: y ≠ 0 → x ≠ 0 → y * x ≠ 0.
  Proof.
   pose proof (from_nat_stmt ((y' === 0 -=> Ext _ False) -=>
     (x' === 0 -=> Ext _ False) -=> (y' * x' === 0 -=> Ext _ False)) two_vars).
   unfold not. apply H0. intro. simpl. apply Mult_nz_mult_nz.
  Qed.

End borrowed_from_nat.

  Global Instance: AntiSymmetric natural_precedes.
   intros x y [v A] [w B].
   rewrite <- A in *. clear A.
   change (x + v + w = x) in B.
   change (x = x + v).
   rewrite <- associativity in B.
   assert (v + w = 0) as C.
    apply (injective (ring_plus x)). rewrite plus_0_r. assumption.
   destruct (zero_sum v w C) as [D _]. rewrite D.
   ring.
  Qed.

  Global Instance: PartialOrder natural_precedes.

  Obligation Tactic := idtac.

  Global Program Instance: ∀ x y: N, Decision (x ≤ y) | 10 :=
    λ x y,
    match decide (natural_precedes (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y)) with
    | left E => left _
    | right E => right _
    end.

  Next Obligation.
   intros.
   apply (preserves_naturals_order (naturals_to_semiring N nat) x y).
   assumption. 
  Qed.

  Next Obligation.
   intros x y _ E _ ?. apply E.
   apply (preserves_naturals_order (naturals_to_semiring N nat) x y).
   assumption. 
  Qed.

  Global Program Instance: ∀ x y: N, Decision (x = y) | 10 :=
    λ x y,
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

  Lemma le_mult_compat_inv_l (x x' y: N): y ≠ 0 → x * y ≤ x' * y → x ≤ x'.
  Proof.
   destruct (total_order x x') as [|[z E]]. intuition.
   rewrite <- E. clear E x.
   unfold precedes, natural_precedes, orders.semigroup.sg_precedes.
   intros ne [v F]. exists 0.
   apply (mult_injective y ne).
   destruct (zero_sum (z * y) v) as [A _].
    apply (injective (ring_plus (x' * y))). 
    change ((x' + z) * y + v = x' * y) in F.
    rewrite <- F at 2. ring.
   change (y * (x' + z + 0) = y * x').
   ring_simplify. rewrite (commutativity y z), A. ring.
  Qed.

  (* NatDistance instances are all equivalent, because their behavior is fully
   determined by the specification. *)

  Program Lemma nat_distance_unique_respectful {a b: NatDistance N}:
    ((=) ==> (=) ==> (=))%signature a b.
  Proof with intuition.
   repeat intro.
   destruct a, b.
   simpl.
   destruct o as [A | A], o0 as [B | B].
      apply (injective (ring_plus x)).
      rewrite A, H0, B...
     destruct (zero_sum x1 x2).
      apply (injective (ring_plus x)).
      rewrite associativity, A, H1, B, H0. ring.
     transitivity 0...
    destruct (zero_sum x1 x2).
     rewrite commutativity.
     apply (injective (ring_plus y)).
     rewrite associativity, B, <- H1, A, H0. ring.
    transitivity 0...
   apply (injective (ring_plus x0)).
   rewrite A, H1, B...
  Qed.

  Lemma nat_distance_unique' {a b: NatDistance N} x: a x = b x.
  Proof. intro. apply nat_distance_unique_respectful; reflexivity. Qed.

  Global Instance nat_distance_proper `{!NatDistance N}: Proper ((=) ==> (=) ==> (=)) (λ x y: N, ` (nat_distance x y)).
    (* Program *should* allow us to write plain nat_distance instead of the
       above eta, like in nat_distance_unique_respectful. Matthieu confirms it's a bug. *)
  Proof. apply nat_distance_unique_respectful. Qed.

  Global Program Instance: NatDistance N | 10 := λ x y: N,
    naturals_to_semiring _ N (proj1_sig (nat_distance (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y))).
      (* Removing the proj1_sig here results in an explosion of proof obligations. Todo: investigate. *)
  Next Obligation.
   intros.
   destruct nat_distance. simpl.
   destruct o; [left | right].
    rewrite <- (to_semiring_involutive N nat y).
    rewrite <- H0.
    rewrite preserves_sg_op.
    rewrite (to_semiring_involutive N nat).
    reflexivity.
   rewrite <- (to_semiring_involutive N nat x).
   rewrite <- H0.
   rewrite preserves_sg_op.
   rewrite (to_semiring_involutive N nat).
   reflexivity.
  Qed.

End contents.
