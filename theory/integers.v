Set Automatic Introduction.

Require Export
 interfaces.integers.
Require
 theory.naturals.
Require Import
 RelationClasses Morphisms Ring
 interfaces.naturals abstract_algebra orders.semiring theory.rings natpair_integers.

Hint Immediate @neg_precedes_pos @preserves_0 @preserves_nonneg @zero_sr_precedes_nat.
Hint Resolve @neg_precedes_pos @preserves_0 @preserves_nonneg @zero_sr_precedes_nat.
Hint Unfold precedes integer_precedes.

Lemma iso_ints `{Integers A} B `{Integers B}: forall a: A,
  integers_to_ring B A (integers_to_ring A B a) == a.
Proof with auto.
 intros.
 pose proof (@integers_initial A _ _ _ _ _ _ _ _ (ring_as_ua.object A) cat_id tt a).
 set (comp (integers_to_ring_arrow (ring_as_ua.object A)) (integers_to_ring_arrow (ring_as_ua.object B))).
 pose proof (@integers_initial A _ _ _ _ _ _ _ _ (ring_as_ua.object A) a0 tt a).
 simpl in *.
 rewrite <- H4...
Qed.

Section contents.

  Context `{Integers Int}.

  Add Ring Int: (stdlib_ring_theory Int).

  Let itoZnat_mor := integers_to_ring_mor (Z nat).
    (* a hint to help class resolution/eauto *)

  Lemma integers_to_ring_unique R `{Ring R} (f: Int -> R) {h: Ring_Morphism f}:
   forall x, f x == integers_to_ring Int R x.
  Proof.
   intros. symmetry.
   set (a := @ring_as_ua.arrow_from_morphism_from_instance_to_object Int _ _ _ _ _ _ _ (ring_as_ua.object R) f h).
   apply (integers_initial (ring_as_ua.object R) a tt x).
  Qed.

  Lemma integers_to_ring_unique' R `{Ring R} (f g: Int -> R) {h: Ring_Morphism f} {u: Ring_Morphism g}:
   forall x, f x == g x.
  Proof.
   intros.
   rewrite (integers_to_ring_unique R f), (integers_to_ring_unique R g).
   reflexivity.
  Qed.

  Lemma int_to_ring_injective `{Ring A}  
   (f: A -> Int) (g: Int -> A) `{!Ring_Morphism f} `{!Ring_Morphism g}: Injective g.
  Proof with auto.
   intros x y E.
   rewrite <- (integers_to_ring_unique' Int (fun v => f (g v)) id x).
   rewrite <- (integers_to_ring_unique' Int (fun v => f (g v)) id y).
   rewrite E. reflexivity.
  Qed.

  Global Instance int_to_int_injective `{Integers B} (f: Int -> B) `{!Ring_Morphism f}: Injective f.
  Proof. apply int_to_ring_injective with (integers_to_ring B Int); apply _. Qed.

  Global Program Instance: forall x y: Int, Decision (x == y) | 10 :=
    match decide (integers_to_ring _ (Z nat) x == integers_to_ring _ (Z nat) y) with
    | left E => left _
    | right E => right _
    end.

  Next Obligation. rewrite <- (iso_ints (Z nat) x), <- (iso_ints (Z nat) y), E. reflexivity. Qed.
  Next Obligation. intro U. apply E. rewrite U. reflexivity. Qed.

  Global Instance naturals_to_integers_injective `{Naturals N}: Injective (naturals_to_semiring N Int).
  Proof.
   intros x y E.
   rewrite <- (plus_0_r x), <- (plus_0_r y).
   change (NtoZ N x == NtoZ N y).
   do 2 rewrite <- (NtoZ_uniq N).
   do 2 rewrite <- (theory.naturals.to_semiring_unique (Z N) (fun x => integers_to_ring Int (Z N) (naturals_to_semiring N Int x))).
   set (itoZN_mor := integers_to_ring_mor (Z N)).
   rewrite E. reflexivity.
  Qed.

  Instance: AntiSymmetric integer_precedes.
  Proof with ring.
   intros x y [v p] [w q]. rewrite <- p in *.
   destruct (theory.naturals.zero_sum v w) as [B _].
    apply naturals_to_integers_injective.
    rewrite preserves_plus, preserves_0.
    apply (injective (ring_plus x)).
    rewrite <- q at 2...
   rewrite B, preserves_0...
  Qed.

  Global Instance: PartialOrder integer_precedes.

  Global Instance: ZeroNeOne Int.
  Proof with auto.
   intros E.
   apply (@zero_ne_one nat _ _ _ _).
   apply (injective (naturals_to_semiring nat Int)). 
   rewrite preserves_0, preserves_1...
  Qed.

  Lemma abs_uniq `{Naturals N} (a a': IntAbs Int N): forall z: Int, proj1_sig (a z) == proj1_sig (a' z).
  Proof with eauto.
   intros. destruct a. destruct a'. simpl.
   apply (injective (naturals_to_semiring N Int)).
   destruct o; destruct o0; rewrite <- H3 in H4; clear H3.
      symmetry...
     apply (antisymmetry integer_precedes). rewrite <- H4...
     apply <- precedes_flip. rewrite H4...
    apply (antisymmetry integer_precedes).
     apply <- precedes_flip. rewrite <- H4...
    rewrite H4...
   apply (injective group_inv). symmetry...
  Qed.

  Lemma abs_nat `{Naturals N} `{!IntAbs Int N} (n: N): int_abs' Int N (naturals_to_semiring N Int n) == n.
  Proof with eauto.
   unfold int_abs'.
   apply (injective (naturals_to_semiring N Int)).
   destruct int_abs as [x [A | B]]... simpl.
   apply (antisymmetry integer_precedes).
    apply <- precedes_flip. rewrite B...
   rewrite <- B...
  Qed. 
  
  Lemma abs_opp_nat `{Naturals N} `{!IntAbs Int N} (n: N): int_abs' Int N (- naturals_to_semiring N Int n) == n.
  Proof with eauto.
   apply (injective (naturals_to_semiring N Int)). 
   unfold int_abs'. 
   destruct int_abs as [x [A | B]]; simpl.
    apply (antisymmetry integer_precedes). rewrite A...
    apply <- precedes_flip. rewrite <- A...
   apply (injective group_inv)...
  Qed. 
  
  Lemma neg_is_pos `{Naturals N} (x y: N): - naturals_to_semiring N Int x == naturals_to_semiring N Int y -> x == 0 /\ y == 0.
  Proof with eauto.
   intro E.
   split; apply (injective (naturals_to_semiring N Int)); apply (antisymmetry integer_precedes).
      apply <- precedes_flip. rewrite E...
     rewrite preserves_0...
    rewrite <- E...
   rewrite preserves_0...
  Qed. 
  
  Global Instance int_abs'_proper `{Naturals N} `{!IntAbs Int N}: Proper (equiv ==> equiv) (int_abs' Int N).
  Proof with eauto; try reflexivity.
   intros z z' E.
   unfold int_abs'.
   destruct int_abs as [x o].
   destruct int_abs as [x' o'].
   simpl. rewrite E in o. clear E z.
   apply (injective (naturals_to_semiring N Int)).
   destruct o as [A|A]; destruct o' as [C|C]; rewrite <- C in A; clear C z'...
     destruct (neg_is_pos _ _ (symmetry A)) as [B C]. rewrite B, C...
    destruct (neg_is_pos _ _ A) as [B C]. rewrite B, C...
   apply (injective group_inv)...
  Qed.
  
  Lemma abs_nat' `{Naturals N} `{Naturals N'} `{!IntAbs Int N} (n: N'): int_abs' Int N (naturals_to_semiring N' Int n) == naturals_to_semiring N' N n.
  Proof with eauto.
   unfold int_abs'. destruct int_abs. simpl.
   apply (injective (naturals_to_semiring N Int)).
   pose proof (theory.naturals.to_semiring_unique Int (fun x => naturals_to_semiring N Int (naturals_to_semiring N' N x)) n) as A.
   rewrite A. (* todo: the separate pose is due to a Coq bug *)
   destruct o...
   apply (antisymmetry integer_precedes).
    apply <- precedes_flip. rewrite H5...
   rewrite <- H5...
  Qed.

  Lemma abs_opp `{Naturals N} `{!IntAbs Int N} z: int_abs' Int N (- z) == int_abs' Int N z.
  Proof.
   unfold int_abs' at 2.
   destruct int_abs as [x [E | E]]; simpl; rewrite <- E. apply abs_opp_nat.
   rewrite inv_involutive.
   apply abs_nat.
  Qed.
  
  Obligation Tactic := idtac.
  
  Global Program Instance slow_int_abs `{Naturals N}: IntAbs Int N | 10 :=
    fun x => exist _ (proj1_sig (int_abs (Z N) N (integers_to_ring Int (Z N) x))) _.
  
  Next Obligation.
   intros.
   destruct int_abs as [x0 [M | M]]; simpl; [left | right].
    rewrite <- (iso_ints (Z N) x), <- M.
    symmetry.
    apply (theory.naturals.to_semiring_unique Int (fun x => integers_to_ring _ _  (_ x))).
   rewrite <- (iso_ints (Z N) x), <- M.
   rewrite preserves_inv. 
   apply inv_proper. symmetry.
   apply (theory.naturals.to_semiring_unique Int (fun x => integers_to_ring _ _ (_ x))).
  Qed.
  
Hint Immediate zero_sr_precedes_nat opp_0 inv_involutive.
Hint Resolve opp_0.

  Lemma eq_opp_self (z: Int) (E: z == -z): z == 0.
  Proof with auto.
   assert (forall n: nat, naturals_to_semiring nat Int n == - naturals_to_semiring nat Int n ->
       naturals_to_semiring nat Int n == 0) as P.
    intros n E'. apply (antisymmetry precedes)...
    rewrite E'. apply -> precedes_0_flip...
   destruct (int_abs Int nat z) as [x [A | A]]; rewrite <- A in *; rewrite P...
    reflexivity.
   rewrite E. symmetry...
  Qed.
  
  Global Instance zero_product: ZeroProduct Int.
  Proof with auto.
   intros x y E.
   destruct (int_abs Int nat x) as [x0 o].
   destruct (int_abs Int nat y) as [x1 o0].
   assert (x0 * x1 == 0) as U.
    apply (injective (naturals_to_semiring _ _)).
    rewrite preserves_mult, preserves_0.
    rewrite <- ring_opp_mult_opp.
    destruct o; destruct o0; rewrite H1, H2...
      rewrite ring_opp_mult_opp, E. ring.
     rewrite <- ring_distr_opp_mult, E. ring.
    transitivity (-(x * y)). ring. rewrite E...
   set (naturals_to_semiring nat Int) in *.
   destruct o; rewrite <- H1 in E |- *; clear H1 x;
    destruct o0; rewrite <- H1 in E |- *; clear H1 y;
      destruct (zero_product x0 x1 U); rewrite H1; rewrite preserves_0;
       [left | right | left | right | left | right | left | right]; ring.
  Qed.
  
  Global Instance mult_injective (x: Int): ~ x == 0 -> Injective (ring_mult x).
  Proof with intuition.
   intros E y z U.
   destruct (zero_product x (y + - z))...
    rewrite distribute_l, U. ring.
   apply equal_by_zero_sum...
  Qed.
  
End contents.

Section preservation. Context `{Integers A} `{Integers B} (f: A -> B) `{!Ring_Morphism f}.

  Let hint: SemiRing A := _.
  Let hint'': SemiRing_Morphism f := _.

  Section with_naturals. Context `{Naturals N}.

    Local Coercion NA := naturals_to_semiring N A.
    Local Coercion NB := naturals_to_semiring N B.

    Lemma preserves_abs `{!IntAbs A N} `{!IntAbs B N}:
      forall a, f (int_abs' A N a) == int_abs' B N (f a).
    Proof with eauto; try apply _.
     pose proof (@neg_precedes_pos B _ _ _ _ _ _ _ N) as U.
     assert (forall (x0 x: N), - NB x0 == f x -> f x == x0); unfold NA, NB in *.
      intros x0 x P.
      apply (antisymmetry integer_precedes).
       apply <- (@precedes_flip B _ _ _ _ _ _ _).
       rewrite <- P, inv_involutive...
      transitivity (0:B)...
      apply <- (precedes_flip (naturals_to_semiring N B x0) 0).
      rewrite P, opp_0...
     intro.
     unfold int_abs' at 1. destruct int_abs as [x [P|P]]; simpl; rewrite <- P; clear P a.
      unfold int_abs'. destruct int_abs as [x0 [P|P]]; simpl...
      rewrite <- P. reflexivity.
     rewrite preserves_inv, abs_opp.
     unfold int_abs'. destruct int_abs as [x0 [P|P]]; simpl...
     symmetry...
    Qed.

  End with_naturals.

  Lemma preserve_sr_order (x y: A): sr_precedes x y -> sr_precedes (f x) (f y).
  Proof. intros [z p]. 
   unfold sr_precedes. 
   exists (int_abs' _ _ (f (naturals_to_semiring nat A z))).
   rewrite <- preserves_abs.
   rewrite <- p, preserves_sg_op, abs_nat. reflexivity.
  Qed.

End preservation.

Section more. Context `{Integers Int}.

  Add Ring Int2: (stdlib_ring_theory Int).

  Global Instance: TotalOrder (_: Order Int).
  Proof with auto; try apply _.
   intros x y.
   rewrite <- (iso_ints (Z nat) x), <- (iso_ints (Z nat) y).
   destruct (total_order (integers_to_ring Int (Z nat) x) (integers_to_ring Int (Z nat) y));
       [left | right]; apply preserve_sr_order...
  Qed.

  Global Program Instance: forall x y: Int, Decision (x <= y) | 10 :=
   match decide (integers_to_ring Int (Z nat) x <= integers_to_ring Int (Z nat) y) with
   | left E => left _
   | right E => right _
   end.

  Next Obligation.
   change (x <= y). rewrite <- (iso_ints (Z nat) x), <- (iso_ints (Z nat) y).
   apply preserve_sr_order. apply _. assumption.
  Qed. 

  Next Obligation.
   intro. apply E. apply preserve_sr_order. apply _. assumption.
  Qed.

  Global Instance le_mult_compat_r (x: Int) (xnonneg: 0 <= x): Proper (integer_precedes ==> integer_precedes) (ring_mult x).
  Proof.
   intros y y'.
   destruct xnonneg as [z E]. rewrite <- E. clear E x.
   intros [x E]. rewrite <- E. clear E y'. 
   rewrite plus_0_l, distribute_l.
   exists (z * x).
   rewrite preserves_mult.
   reflexivity.
  Qed.

    (* todo: by generalizing [Injective] to work with signatures, we should be able to write the following as an inverse proper thingy *)
  Lemma le_mult_compat_inv_l (x x' y: Int): 1 <= y -> x * y <= x' * y -> x <= x'.
  Proof with auto.
   intros H1 [u H2].
   destruct (total_order x x') as [P | [x0 P]]...
   exists 0.
   rewrite <- P in *. clear P x.
   cut (x0 == 0). intro E. rewrite E, preserves_0. ring.
   rename u into x.
   assert (naturals_to_semiring nat Int x0 * y + naturals_to_semiring nat Int x == 0).
    ring_simplify in H2.
    apply (injective (ring_plus (x' * y))). rewrite <- H2 at 2. ring.
   clear H2. 
   destruct H1. rewrite <- H1 in *. clear H1 y.
   destruct (theory.naturals.zero_sum x0 (x0 * x1 + x))...
   apply (injective (naturals_to_semiring nat Int)).
   rewrite preserves_0.
   rewrite <- H3.
   rewrite preserves_plus, preserves_plus, preserves_mult.
   ring.
  Qed.

End more.
