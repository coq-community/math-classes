(* General results about arbitrary integer implementations. *)
Require Export
 interfaces.integers.
Require
 theory.naturals.
Require Import
 RelationClasses Morphisms Ring Program Setoid
 interfaces.naturals abstract_algebra orders.semiring theory.rings
 natpair_integers workaround_tactics.

(* Any two integer implementations are trivially isomorphic because of their initiality,
 but it's nice to have this stated in terms of integers_to_ring being self-inverse: *)

Lemma to_ring_involutive `{Integers Int} Int2 `{Integers Int2}: ∀ a : Int,
  integers_to_ring Int2 Int (integers_to_ring Int Int2 a) = a.
Proof.
 intros.
 destruct (@categories.initials_unique' _ _ _ _ _ _ (ring.object Int) (ring.object Int2) _
   integers_initial _ integers_initial) as [_ P].
 apply (P tt a).
Qed.

Lemma to_ring_unique `{Integers Int} `{Ring R} (f: Int → R) {h: Ring_Morphism f}:
  ∀ x, f x = integers_to_ring Int R x.
Proof.
  intros. symmetry.
  pose proof (ring.encode_morphism_and_ops (f:=f)).
  set (@variety.arrow ring.theory _ _ _ (ring.encode_variety_and_ops _) _ _ _ (ring.encode_variety_and_ops _) (λ _, f) _).
  exact (integers_initial _ a tt x).
Qed.

Lemma to_ring_unique' `{Integers Int} `{Ring R} (f g: Int → R) `{!Ring_Morphism f} `{!Ring_Morphism g}:
  f = g.
Proof.
  intro.
  rewrite (to_ring_unique f), (to_ring_unique g).
  reflexivity.
Qed.

(* A ring morphism from integers to another ring is injective if there's an injection in the other direction: *)
Lemma to_ring_injective `{Integers Int} `{Ring R} (f: R → Int) (g: Int → R) `{!Ring_Morphism f} `{!Ring_Morphism g}: 
  Injective g.
Proof.
  constructor. 2: constructor; apply _.
  intros x y E.
  rewrite <- (to_ring_unique' (f ∘ g) id x).
  rewrite <- (to_ring_unique' (f ∘ g) id y).
  unfold compose. rewrite E. reflexivity.
Qed.

Instance integers_to_integers_injective `{Integers Int} `{Integers Int2} (f: Int → Int2) `{!Ring_Morphism f}: 
  Injective f.
Proof. 
  apply to_ring_injective with (integers_to_ring Int2 Int); apply _. 
Qed.

Instance naturals_to_integers_injective `{Integers Int} `{Naturals N}: Injective (naturals_to_semiring N Int).
Proof.
  constructor; try apply _.
  intros x y E.
  rewrite <- (plus_0_r x), <- (plus_0_r y).
  change (NtoZ N x = NtoZ N y).
  do 2 rewrite <- (NtoZ_uniq N).
  do 2 rewrite <- (naturals.to_semiring_unique (integers_to_ring Int (Z N) ∘ naturals_to_semiring N Int)).
  unfold compose. rewrite E. reflexivity.
Qed.

Section retract_is_int.
  Context `{Integers Int} `{Ring Int2}.
  Context (f : Int → Int2) `{!Inverse f} `{!Surjective f} `{!Ring_Morphism f} `{!Ring_Morphism (inverse f)}.

  (* If we make this an instance, then instance resolution will result in an infinite loop *)
  Definition retract_is_int_to_ring : IntegersToRing Int2 := λ R _ _ _ _ _, integers_to_ring Int R ∘ inverse f.

  Section for_another_ring.
    Context `{Ring R}.

    Instance: Ring_Morphism (integers_to_ring Int R ∘ inverse f).
    Context (h :  Int2 → R) `{!Ring_Morphism h}. 
      
    Lemma same_morphism: integers_to_ring Int R ∘ inverse f = h.
    Proof with auto.
      intro x.
      pose proof (to_ring_unique (h ∘ f)) as E.
      unfold compose in *.
      rewrite <-E. apply sm_proper. 
      apply jections.surjective_applied.
    Qed.
  End for_another_ring.
  
  (* If we make this an instance, then instance resolution will result in an infinite loop *)
  Program Definition retract_is_int: @Integers Int2 _ _ _ _ _ _ retract_is_int_to_ring. 
  Proof.
    esplit. (* for some reason split doesn't work... *)
    apply integer_initial. intros. 
    unfold integers_to_ring, retract_is_int_to_ring. 
    apply same_morphism. assumption.
  Qed.
End retract_is_int.

Section contents.
  Context `{Integers Int} `{!RingMinus Int}.
  Add Ring Int: (stdlib_ring_theory Int).

  Hint Immediate @neg_sr_precedes_pos @preserves_0 @sr_preserves_nonneg @zero_sr_precedes_nat.
  Hint Resolve @neg_sr_precedes_pos @preserves_0 @sr_preserves_nonneg @zero_sr_precedes_nat.

  Instance: AntiSymmetric (sr_precedes (R:=Int)).
  Proof with ring.
   intros x y [v p] [w q]. rewrite <- p in *.
   destruct (theory.naturals.zero_sum v w) as [B _].
    apply naturals_to_integers_injective.
    rewrite preserves_plus, preserves_0.
    apply (left_cancellation (+) x); trivial.
    rewrite <- q at 2...
   rewrite B, preserves_0...
  Qed.

  Global Instance: PartialOrder (sr_precedes (R:=Int)).

    Global Program Instance: ∀ x y: Int, Decision (x = y) | 10 := λ x y,
    match decide (integers_to_ring _ (Z nat) x = integers_to_ring _ (Z nat) y) with
    | left E => left _
    | right E => right _
    end.

  Next Obligation. rewrite <- (to_ring_involutive (Z nat) x), <- (to_ring_involutive (Z nat) y), E. reflexivity. Qed.
  Next Obligation. intro U. apply E. rewrite U. reflexivity. Qed.

  Global Instance: ZeroNeOne Int.
  Proof with auto.
   intros E.
   apply (@zero_ne_one nat _ _ _ _).
   apply (injective (naturals_to_semiring nat Int)). 
   rewrite preserves_0, preserves_1...
  Qed.

  Lemma abs_uniq `{Naturals N} (a a': IntAbs Int N): ∀ z: Int, proj1_sig (a z) = proj1_sig (a' z).
  Proof with eauto.
   intros. destruct a, a'. simpl.
   apply (injective (naturals_to_semiring N Int)).
   destruct o as [A | A], o0 as [B | B]; rewrite <- A in B; clear A.
      symmetry...
     apply (antisymmetry (≤)). rewrite <- B...
     apply <- sr_precedes_flip. rewrite B...
    apply (antisymmetry (≤)).
     apply <- sr_precedes_flip. rewrite <- B...
    rewrite B...
   apply (injective group_inv). symmetry...
  Qed.

  Obligation Tactic := idtac.
  
  Global Program Instance slow_int_abs `{Naturals N}: IntAbs Int N | 10 :=
    λ x, exist _ (proj1_sig (int_abs_sig (Z N) N (integers_to_ring Int (Z N) x))) _.

  Next Obligation.
   intros.
   destruct int_abs_sig as [x0 [M | M]]; simpl; [left | right].
    rewrite <- (to_ring_involutive (Z N) x), <- M.
    symmetry.
    apply_simplified (naturals.to_semiring_unique (integers_to_ring (Z N) Int ∘ naturals_to_semiring N (Z N))).
   rewrite <- (to_ring_involutive (Z N) x), <- M.
   rewrite preserves_inv. 
   apply inv_proper. symmetry.
   apply_simplified (naturals.to_semiring_unique (integers_to_ring (Z N) Int ∘ naturals_to_semiring N (Z N))).
  Qed.

  (* Properties of int_abs *)
  Section int_abs.
  Context `{Naturals N} `{!IntAbs Int N}.

  Lemma abs_nat (n: N): int_abs Int N (naturals_to_semiring N Int n) = n.
  Proof with eauto.
   unfold int_abs.
   apply (injective (naturals_to_semiring N Int)).
   destruct int_abs_sig as [x [A | B]]... simpl.
   apply (antisymmetry (≤)).
    apply <- sr_precedes_flip. rewrite B...
   rewrite <- B...
  Qed. 
  
  Lemma abs_opp_nat (n: N): int_abs Int N (- naturals_to_semiring N Int n) = n.
  Proof with eauto.
   apply (injective (naturals_to_semiring N Int)). 
   unfold int_abs. 
   destruct int_abs_sig as [x [A | B]]; simpl.
    apply (antisymmetry (≤)). rewrite A...
    apply <- sr_precedes_flip. rewrite <- A...
   apply (injective group_inv)...
  Qed. 
  
  Lemma neg_is_pos (x y: N) : 
    - naturals_to_semiring N Int x = naturals_to_semiring N Int y → x = 0 ∧ y = 0.
  Proof with eauto.
   intro E.
   split; apply (injective (naturals_to_semiring N Int)); apply (antisymmetry (≤)).
      apply <- sr_precedes_flip. rewrite E...
     rewrite preserves_0...
    rewrite <- E...
   rewrite preserves_0...
  Qed. 
  
  Global Instance int_abs_proper: Proper ((=) ==> (=)) (int_abs Int N).
  Proof with eauto; try reflexivity.
   intros z z' E.
   unfold int_abs.
   destruct int_abs_sig as [x o], int_abs_sig as [x' o'].
   simpl. rewrite E in o. clear E z.
   apply (injective (naturals_to_semiring N Int)).
   destruct o as [A|A], o' as [C|C]; rewrite <- C in A; clear C z'...
     destruct (neg_is_pos _ _ (symmetry A)) as [B C]. rewrite B, C...
    destruct (neg_is_pos _ _ A) as [B C]. rewrite B, C...
   apply (injective group_inv)...
  Qed.

  Lemma abs_nat' `{Naturals N'} (n: N') : 
    int_abs Int N (naturals_to_semiring N' Int n) = naturals_to_semiring N' N n.
  Proof with eauto.
   unfold int_abs. destruct int_abs_sig. simpl.
   apply (injective (naturals_to_semiring N Int)).
   posed_rewrite (naturals.to_semiring_unique (naturals_to_semiring N Int ∘ naturals_to_semiring N' N) n).
   destruct o as [E|E]...
   apply (antisymmetry (≤)).
    apply <- sr_precedes_flip. rewrite E...
   rewrite <- E...
  Qed.

  Lemma naturals_to_semiring_neg x : 0 ≤ - naturals_to_semiring N Int x → x = 0.
  Proof with auto.
    intros E. 
    apply (injective (naturals_to_semiring N Int)).
    apply (antisymmetry (≤)).
    apply <- sr_precedes_flip. rewrite preserves_0. rewrite opp_0...
    rewrite preserves_0. apply zero_sr_precedes_nat.
  Qed.

  Lemma abs_nonneg x : 0 ≤ x → naturals_to_semiring N Int (int_abs Int N x) = x.
  Proof with auto.
    intros E. 
    unfold int_abs. destruct int_abs_sig as [z Ez]. simpl.
    destruct Ez as [? | Ez]... rewrite <-Ez in E.
    rewrite <-Ez. rewrite (naturals_to_semiring_neg z E).
    rewrite preserves_0. ring.
  Qed.

  Lemma abs_nonneg_plus x y : 
    0 ≤ x → 0 ≤ y → int_abs Int N (x + y) = int_abs Int N x + int_abs Int N y.
  Proof with auto.
    intros Ex Ey.
    apply (injective (naturals_to_semiring N Int)). 
    rewrite preserves_plus.
    repeat rewrite abs_nonneg...
    reflexivity. 
    apply sr_precedes_nonneg_plus_compat...
  Qed.

  Lemma abs_0 : int_abs Int N 0 = 0.
  Proof with auto.
    apply (injective (naturals_to_semiring N Int)). 
    rewrite abs_nonneg... 
    symmetry. apply preserves_0.
    reflexivity.
  Qed.

  Lemma abs_nonneg_mult x y : 
    0 ≤ x → 0 ≤ y → int_abs Int N (x * y) = int_abs Int N x * int_abs Int N y.
  Proof with auto.
    intros Ex Ey.
    apply (injective (naturals_to_semiring N Int)). 
    rewrite preserves_mult.
    repeat rewrite abs_nonneg...
    reflexivity. 
    apply sr_precedes_nonneg_mult_compat...
  Qed.

  Lemma abs_1 : int_abs Int N 1 = 1.
  Proof with auto.
    apply (injective (naturals_to_semiring N Int)). 
    rewrite abs_nonneg... 
    symmetry. apply preserves_1.
    apply sr_precedes_0_1.
  Qed.

  Lemma abs_opp z : int_abs Int N (- z) = int_abs Int N z.
  Proof.
   unfold int_abs at 2.
   destruct int_abs_sig as [x [E | E]]; simpl; rewrite <- E. apply abs_opp_nat.
   rewrite inv_involutive.
   apply abs_nat.
  Qed.
  
  End int_abs.

  Lemma induction
    (P: Int → Prop) `{!Proper (equiv ==> iff)%signature P}:
    P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → (∀ n, n ≤ 0 → P n → P (n - 1)) → ∀ n, P n.
  Proof with auto.
    intros P0 Psuc1 Psuc2 n.
    destruct (int_abs_sig Int nat n) as [m [E|E]].
     rewrite <-E. clear E. pattern m. 
     apply naturals.induction; clear m.
       intros ? ? E. rewrite E. tauto.
      rewrite preserves_0...
     intros m E. 
     rewrite preserves_plus, preserves_1.
     apply Psuc1... apply zero_sr_precedes_nat.
    rewrite <-E. clear E. pattern m. 
    apply naturals.induction; clear m.
      intros ? ? E. rewrite E. tauto.
     rewrite preserves_0, rings.opp_0...
    intros m E. 
    rewrite preserves_plus, preserves_1.
    rewrite plus_opp_distr, commutativity, <-rings.ring_minus_correct.
    apply Psuc2...
    apply sr_precedes_0_flip, zero_sr_precedes_nat...
  Qed.

  Lemma biinduction
    (P: Int → Prop) `{!Proper (equiv ==> iff)%signature P}:
    P 0 → (∀ n, P n ↔ P (1 + n)) → ∀ n, P n.
  Proof with auto.
    intros P0 Psuc. apply induction...
    firstorder.
    intros. apply Psuc. setoid_replace (1+(n-1)) with n by ring...
  Qed.

  Hint Immediate zero_sr_precedes_nat opp_0 inv_involutive.
  Hint Resolve opp_0.
  (* todo: move *)

  Lemma eq_opp_self (z: Int) (E: z = -z): z = 0.
  Proof with auto.
   assert (∀ n: nat, naturals_to_semiring nat Int n = - naturals_to_semiring nat Int n →
       naturals_to_semiring nat Int n = 0) as P.
    intros n E'. apply (antisymmetry precedes)...
    rewrite E'. apply -> sr_precedes_0_flip...
   destruct (int_abs_sig Int nat z) as [x [A | A]]; rewrite <- A in *; rewrite P...
    reflexivity.
   rewrite E. symmetry...
  Qed.

  Global Instance zero_product: ZeroProduct Int.
  Proof with auto.
   intros x y E.
   destruct (int_abs_sig Int nat x) as [x0 o], (int_abs_sig Int nat y) as [x1 o0].
   assert (x0 * x1 = 0) as U.
    apply (injective (naturals_to_semiring _ _)).
    rewrite preserves_mult, preserves_0.
    rewrite <- ring_opp_mult_opp.
    destruct o as [E1|E1], o0 as [E2|E2]; rewrite E1, E2...
      rewrite ring_opp_mult_opp, E. ring.
     rewrite <- ring_distr_opp_mult, E. ring.
    transitivity (-(x * y)). ring. rewrite E...
   set (naturals_to_semiring nat Int) in *.
   destruct o as [E1|E1]; rewrite <- E1 in E |- *; clear E1 x;
    destruct o0 as [E2|E2]; rewrite <- E2 in E |- *; clear E2 y;
      destruct (zero_product x0 x1 U) as [E3|E3]; rewrite E3; rewrite preserves_0;
       [left | right | left | right | left | right | left | right]; ring.
  Qed.

  Instance: NoZeroDivisors Int.
  Proof. intros ? [? [? [? d]]]. destruct (zero_product _ _ d); intuition. Qed.

  Global Instance: IntegralDomain Int.

  Global Instance: ZeroNeTwo Int.
  Proof.
   intro E. unfold "2" in E. 
   apply zero_ne_one.
   symmetry. apply eq_opp_self.
   apply (left_cancellation (+) 1); trivial.
   rewrite <-E. ring.
  Qed.

End contents.

Section preservation. 
  Context `{Integers A} `{Integers B} (f: A → B) `{!Ring_Morphism f}.

  Section with_naturals. 
    Context `{Naturals N}.

    Local Coercion NA := naturals_to_semiring N A.
    Local Coercion NB := naturals_to_semiring N B.

    Lemma preserves_abs `{!IntAbs A N} `{!IntAbs B N} a : f (int_abs A N a) = int_abs B N (f a).
    Proof with eauto; try apply _.
      assert (∀ (x y: N), - NB y = f x → f x = y); unfold NA, NB in *.
      intros x y P.
      apply (antisymmetry (≤)).
        rewrite <-P. apply neg_sr_precedes_pos.
      transitivity (0:B).
        apply sr_precedes_flip.
        rewrite P, opp_0. apply sr_preserves_nonneg...
      apply sr_preserves_nonneg... 
      unfold int_abs at 1. destruct int_abs_sig as [x [P|P]]; simpl; rewrite <- P; clear P a.
      unfold int_abs. destruct int_abs_sig as [x0 [P|P]]; simpl... symmetry...
      rewrite preserves_inv, abs_opp. 
      unfold int_abs. destruct int_abs_sig as [x0 [P|P]]; simpl...
      symmetry...
    Qed.

  End with_naturals.

  Lemma preserve_sr_order (x y: A): x ≤ y → f x ≤ f y.
  Proof. intros [z p]. 
   exists (int_abs _ _ (f (naturals_to_semiring nat A z))).
   rewrite <- preserves_abs.
   rewrite <- p, preserves_sg_op, abs_nat. reflexivity.
  Qed.

End preservation.

Section int_order. 
  Context `{Integers Int}.

  Add Ring Int2: (stdlib_ring_theory Int).

  Global Instance: TotalOrder (sr_precedes (R:=Int)).
  Proof with auto; try apply _.
   intros x y.
   rewrite <- (to_ring_involutive (Z nat) x), <- (to_ring_involutive (Z nat) y).
   destruct (total_order (integers_to_ring Int (Z nat) x) (integers_to_ring Int (Z nat) y));
     [left | right]; apply (preserve_sr_order _)...
  Qed.

  Global Program Instance: ∀ x y: Int, Decision (x ≤ y) | 10 := λ x y,
   match decide (integers_to_ring Int (Z nat) x ≤ integers_to_ring Int (Z nat) y) with
   | left E => left _
   | right E => right _
   end.

  Next Obligation.
   change (x ≤ y). rewrite <- (to_ring_involutive (Z nat) x), <- (to_ring_involutive (Z nat) y).
   apply (preserve_sr_order _). assumption.
  Qed. 

  Next Obligation.
   intro. apply E. apply (preserve_sr_order _). assumption.
  Qed.

End int_order.
