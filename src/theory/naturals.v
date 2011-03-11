Require Import
 workaround_tactics
 Relation_Definitions Morphisms Program Ring
 abstract_algebra peano_naturals theory.rings
 categories.variety theory.ua_transference.
Require Export
 interfaces.naturals.

Lemma to_semiring_involutive N `{Naturals N} N2 `{Naturals N2}: ∀ a: N,
 naturals_to_semiring N2 N (naturals_to_semiring N N2 a) = a.
Proof.
  intros a.
  apply_simplified (proj2 (@categories.initials_unique' (variety.Object semiring.theory)
    _ _ _ _ _ (semiring.object N) (semiring.object N2) _ naturals_initial _ naturals_initial) tt a).
  (* todo: separate pose necessary due to Coq bug *)
Qed.

Lemma to_semiring_unique `{Naturals N} `{SemiRing SR} (f: N → SR) `{!SemiRing_Morphism f}:
 ∀ x, f x = naturals_to_semiring N SR x.
Proof.
 intros. symmetry.
 pose proof (@semiring.mor_from_sr_to_alg _ _ _ (semiring.variety N) _ _ _ (semiring.variety SR) (λ _, f) _).
 set (@variety.arrow semiring.theory _ _ _ (semiring.variety N) _ _ _ (semiring.variety SR) (λ _, f) _).
 apply (naturals_initial _ a tt x).
Qed.

Lemma to_semiring_unique_alt `{Naturals N} `{SemiRing SR} (f g: N → SR) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x :
  f x = g x.
Proof.
  rewrite (to_semiring_unique f).
  now rewrite (to_semiring_unique g).
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
  apply (to_semiring_unique _).
Qed.

Lemma to_semiring_self `{Naturals N} x : x = naturals_to_semiring N N x.
Proof.
  replace x with (id x) by auto.
  apply (to_semiring_unique _).
Qed.

Lemma to_semiring_injective `{Naturals N} `{SemiRing A}  
   (f: A → N) (g: N → A) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}: Injective g.
Proof with intuition.
  constructor. 2: constructor; apply _.
  intros x y E.
  rewrite <- (to_semiring_unique_alt (f ∘ g) id x)...
  rewrite <- (to_semiring_unique_alt (f ∘ g) id y)...
  unfold compose. now rewrite E.
Qed.

Instance naturals_to_naturals_injective `{Naturals N} `{Naturals N2} (f: N → N2) `{!SemiRing_Morphism f}:
  Injective f.
Proof.
  apply to_semiring_injective with (naturals_to_semiring N2 N); apply _.
Qed.

Section retract_is_nat.
  Context `{Naturals N} `{SemiRing SR} `{oSR : Order SR} `{!SemiRingOrder oSR} `{!TotalOrder oSR}.
  Context (f : N → SR) `{inv_f : !Inverse f} `{!Surjective f} `{!SemiRing_Morphism f} `{!SemiRing_Morphism (f⁻¹)}.

  (* If we make this an instance, then instance resolution will often loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR := λ R _ _ _ _ , naturals_to_semiring N R ∘ f⁻¹.

  Section for_another_semiring.
    Context `{SemiRing R}.

    Instance: SemiRing_Morphism (naturals_to_semiring N R ∘ f⁻¹).

    Context (h :  SR → R) `{!SemiRing_Morphism h}. 
     
    Lemma same_morphism: naturals_to_semiring N R ∘ f⁻¹ = h.
    Proof.
      intros x y F. rewrite <-F.
      transitivity ((h ∘ (f ∘ f⁻¹)) x).
       symmetry. apply (to_semiring_unique (h ∘ f)).
      unfold compose. now rewrite jections.surjective_applied.
    Qed.
  End for_another_semiring.

  (* If we make this an instance, then instance resolution will often loop *)
  Program Definition retract_is_nat: Naturals SR (U:=retract_is_nat_to_sr). 
  Proof. 
    esplit; try apply _. (* for some reason split doesn't work... *)
    intros. apply natural_initial. intros.
    now apply same_morphism.
  Qed.
End retract_is_nat.

Section contents.
Context `{Naturals N}.

Section borrowed_from_nat.
  Import universal_algebra.
  Import notations.

  Lemma induction
    (P: N → Prop) `{!Proper ((=) ==> iff) P}:
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

  Let three_vars (x y z : N) (_: unit) v := match v with 0%nat => x | 1%nat => y | _ => z end.
  Let two_vars (x y : N) (_: unit) v := match v with 0%nat => x | _ => y end.
  Let no_vars (_: unit) (v: nat) := 0.

  Local Notation x' := (Var varieties.semiring.sig _ 0 tt).
  Local Notation y' := (Var varieties.semiring.sig _ 1 tt).
  Local Notation z' := (Var varieties.semiring.sig _ 2%nat tt).

  (* Some clever autoquoting tactic might make what follows even more automatic. *)
  (* The ugly [pose proof ... . apply that_thing.]'s are because of Coq bug 2185. *)

  Global Instance: ∀ z : N, LeftCancellation (+) z.
  Proof.
    intros x y z.
    apply_simplified (from_nat_stmt (x' + y' === x' + z' -=> y' === z') (three_vars x y z)).
    intro. simpl. apply Plus.plus_reg_l.
  Qed.

  Global Instance: ∀ z : N, RightCancellation (+) z.
  Proof. intro. apply right_cancel_from_left. Qed.

  Global Instance: ∀ z : N, PropHolds (z ≠ 0) → LeftCancellation (.*.) z.
  Proof.
    intros z E x y.
    apply_simplified (from_nat_stmt ((z' === 0 -=> Ext _ False) -=> z' * x' === z' * y' -=> x' === y') (three_vars x y z)).
    intro. simpl. now apply nat_mult_mult_reg_l. easy.
  Qed.

  Global Instance: ∀ z : N, PropHolds (z ≠ 0) → RightCancellation (.*.) z.
  Proof. intros ? ?. apply right_cancel_from_left. Qed.

  Global Instance: PropHolds ((1:N) ≠ 0).
  Proof.
    pose proof (from_nat_stmt (1 === 0 -=> Ext _ False) no_vars) as P.
    now apply P.
  Qed.

  Lemma zero_sum x y : x + y = 0 → x = 0 ∧ y = 0.
  Proof.
    apply_simplified (from_nat_stmt (x' + y' === 0 -=> Conj _ (x' === 0) (y' === 0)) (two_vars x y)).
    intro. simpl. apply Plus.plus_is_O.
  Qed.
  
  Lemma one_sum x y : x + y = 1 → (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1).
  Proof. 
   apply_simplified (from_nat_stmt (x' + y' === 1 -=> Disj _ (Conj _ (x' === 1) (y' === 0)) (Conj _ (x' === 0) (y' === 1))) (two_vars x y)).
   intros. simpl. intros. edestruct Plus.plus_is_one; eauto.
  Qed.

  Global Instance: ZeroProduct N.
  Proof.
    intros x y.
    apply_simplified (from_nat_stmt (x' * y' === 0 -=>Disj _ (x' === 0) (y' === 0)) (two_vars x y)).
    intros ? E. destruct (Mult.mult_is_O _ _ E); intuition.
  Qed.
End borrowed_from_nat.

Lemma nz_one_plus_zero x : 1 + x ≠ 0.
Proof.
  intro E.
  destruct (zero_sum 1 x E).
  now apply (ne_0 1).
Qed.

Global Program Instance: ∀ x y: N, Decision (x = y) | 10 := λ x y,
  match decide (naturals_to_semiring _ nat x = naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation.
  rewrite <- (to_semiring_involutive _ nat x), <- (to_semiring_involutive _ nat y).
  now rewrite E.
Qed.

Next Obligation.
  intros F. apply E. now rewrite F.
Qed.

End contents.
