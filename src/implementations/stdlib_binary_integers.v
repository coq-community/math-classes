(* nasty because Zplus depends on Pminus which is a bucket of FAIL *)
Require 
  interfaces.naturals theory.naturals peano_naturals theory.shiftl.
Require Import
  BinInt Morphisms Ring Program Arith ZBinary
  abstract_algebra interfaces.integers
  theory.categories theory.rings 
  stdlib_binary_positives stdlib_binary_naturals
  interfaces.additional_operations
  nonneg_integers_naturals.

(* canonical names: *)
Instance Z_equiv: Equiv BinInt.Z := eq.
Instance Z_plus: RingPlus BinInt.Z := BinInt.Zplus.
Instance Z_0: RingZero BinInt.Z := BinInt.Z0.
Instance Z_1: RingOne BinInt.Z := BinInt.Zpos BinPos.xH.
Instance Z_mult: RingMult BinInt.Z := BinInt.Zmult.
Instance Z_opp: GroupInv BinInt.Z := BinInt.Zopp.
  (* some day we'd like to do this with [Existing Instance] *)

Instance: Ring Z.
Proof.
  repeat (split; try apply _); repeat intro.
            now apply Zplus_assoc.
           now apply Zplus_0_r.
          now apply Zplus_opp_l.
         now apply Zplus_opp_r.
        now apply Zplus_comm.
       now apply Zmult_assoc.
      now apply Zmult_1_l.
     now apply Zmult_1_r.
    now apply Zmult_comm.
   now apply Zmult_plus_distr_r.
  now apply Zmult_plus_distr_l.
Qed.

(* misc: *)
Instance: ∀ x y : Z, Decision (x = y) := ZArith_dec.Z_eq_dec.

Add Ring Z: (stdlib_ring_theory BinInt.Z).

Definition map_Z `{RingPlus R} `{RingZero R} `{RingOne R} `{GroupInv R} (z: Z): R :=
  match z with
  | Z0 => 0
  | Zpos p => map_pos p
  | Zneg p => - map_pos p
  end.

Instance: IntegersToRing Z := λ B _ _ _ _ _, @map_Z B _ _ _ _.

Section for_another_ring.
  Context `{Ring R}.

  Add Ring R: (stdlib_ring_theory R).

  Lemma preserves_Zplus x y: map_Z (x + y) = map_Z x + map_Z y.
  Proof with try reflexivity; try assumption; try ring.
   destruct x as [| x | x ]; simpl...
    destruct y as [| y | y]; simpl...
     apply preserves_Pplus.
    case_eq (Pcompare x y Eq); intros E; simpl.
      rewrite (Pcompare_Eq_eq _ _ E)...
     rewrite preserves_Pminus...
    apply preserves_Pminus.
    unfold Plt.
    rewrite (ZC1 _ _ E)...
   destruct y as [| y | y ]; simpl...
    case_eq (Pcompare x y Eq); intros E; simpl.
      rewrite (Pcompare_Eq_eq _ _ E)...
     rewrite preserves_Pminus...
    rewrite preserves_Pminus...
    unfold Plt.
    rewrite (ZC1 _ _ E)...
   rewrite preserves_Pplus...
  Qed.

  Lemma preserves_Zmult x y: map_Z (x * y) = map_Z x * map_Z y.
  Proof with try reflexivity; try ring.
   destruct x; simpl; intros...
    destruct y; simpl...
     apply preserves_Pmult.
    rewrite preserves_Pmult...
   destruct y; simpl...
    rewrite preserves_Pmult...
   rewrite preserves_Pmult...
  Qed.

  Instance: Proper ((=) ==> (=)) map_Z.
  Proof. unfold equiv, Z_equiv. repeat intro. subst. reflexivity. Qed.

  Hint Resolve preserves_Zplus preserves_Zmult.
  Hint Constructors Monoid_Morphism SemiGroup_Morphism.

  Global Instance map_Z_ring_mor: SemiRing_Morphism map_Z.
  Proof. repeat (constructor; auto with typeclass_instances; try reflexivity; try apply _). Qed.

  Section with_another_morphism.
    Context map_Z' `{!SemiRing_Morphism (map_Z': Z → R)}.

    Let agree_on_0: map_Z Z0 = map_Z' Z0.
    Proof. symmetry. apply preserves_0. Qed.

    Let agree_on_1: map_Z 1%Z = map_Z' 1%Z.
    Proof. symmetry. apply preserves_1. Qed.

    Let agree_on_positive p: map_Z (Zpos p) = map_Z' (Zpos p).
    Proof with try reflexivity.
     induction p; simpl.
       rewrite IHp.
       rewrite xI_in_ring_terms.
       rewrite agree_on_1.
        rewrite <-2!preserves_sg_op...
      rewrite IHp.
      rewrite xO_in_ring_terms.
      rewrite <- preserves_sg_op...
     apply agree_on_1.
    Qed.

    Let agree_on_negative p: map_Z (Zneg p) = map_Z' (Zneg p).
    Proof with try reflexivity.
     intros.
     replace (Zneg p) with (- (Zpos p))...
     rewrite 2!preserves_opp.
     rewrite <- agree_on_positive...
    Qed.

    Lemma same_morphism: integers_to_ring Z R = map_Z'.
    Proof.
     intros [].
       intros y E. rewrite <- E.
       apply agree_on_0.
      intros p y E. rewrite <- E.
      apply agree_on_positive.
     intros p y E. rewrite <- E.
     apply agree_on_negative.
    Qed.

  End with_another_morphism.
End for_another_ring.

Instance: Initial (ring.object Z).
Proof.
  apply integer_initial. intros. apply same_morphism. auto.
Qed.
Instance: Integers Z.

Instance: Order Z := Zle.

Instance: RingOrder Zle.
Proof.
  repeat (split; try apply _).
    exact Zorder.Zle_antisym.
   intros x y E. now apply Zorder.Zplus_le_compat_l.
  intros x E y F. now apply Zorder.Zmult_le_0_compat.
Qed.

Instance: TotalOrder Zle.
Proof with intuition. 
  intros x y.
  destruct (Zorder.Zle_or_lt x y)...
  right. apply Zorder.Zlt_le_weak...
Qed.

Lemma Zlt_coincides x y : (x < y)%Z ↔ x < y.
Proof with trivial.
  split.
   intro. split. apply Zorder.Zlt_le_weak... now apply Zorder.Zlt_not_eq.
  intros [E1 E2]. destruct (Zorder.Zle_lt_or_eq _ _ E1)... now destruct E2.
Qed.

(* * Embedding of the Peano naturals into [Z] *)
Instance inject_nat_Z: Coerce nat Z := Z_of_nat.

Instance: SemiRing_Morphism Z_of_nat.
Proof.
  repeat (split; try apply _).
   exact Znat.inj_plus.
  exact Znat.inj_mult.
Qed.

Program Instance: IntAbs Z nat := Zabs_nat.
Next Obligation.
  rewrite <-(naturals.to_semiring_unique Z_of_nat).
  rewrite Zabs.inj_Zabs_nat.
  destruct (total_order 0 x).
   left. 
   now apply Z.abs_eq.
  right.
  rewrite Z.abs_neq. now apply opp_involutive. easy.
Qed.

(* * Embedding N into Z *)
Instance inject_N_Z: Coerce BinNat.N Z := Z_of_N.

Instance: SemiRing_Morphism Z_of_N.
 Proof.
   repeat (split; try apply _).
   exact Znat.Z_of_N_plus.
  exact Znat.Z_of_N_mult.
Qed.

Program Instance: IntAbs Z BinNat.N := Zabs_N.
Next Obligation.
  rewrite <-(naturals.to_semiring_unique Z_of_N).
  rewrite Znat.Z_of_N_abs.
  destruct (total_order 0 x).
   left. 
   now apply Z.abs_eq.
  right.
  rewrite Z.abs_neq. now apply opp_involutive. easy.
Qed.

(* Efficient nat_pow *)
Program Instance Z_pow: Pow Z (Z⁺) := Z.pow.

Instance: NatPowSpec Z (Z⁺) Z_pow.
Proof.
  split; unfold pow, Z_pow.
    intros x1 y1 E1 [x2 Ex2] [y2 Ey2] E2.
    unfold equiv, sig_equiv in E2.
    simpl in *. now rewrite E1, E2.
   intros. now apply Z.pow_0_r.
  intros x n.
  rewrite preserves_plus, preserves_1.  
  rewrite <-(Z.pow_1_r x) at 2. apply Z.pow_add_r.
   auto with zarith.
  now destruct n.
Qed.

(* Efficient shiftl *)
Program Instance Z_shiftl: ShiftL Z (Z⁺) := Z.shiftl.

Instance: ShiftLSpec Z (Z⁺) Z_shiftl.
Proof.
  apply shiftl.shiftl_spec_from_nat_pow.
  intros x [n En].
  apply Z.shiftl_mul_pow2.
  now apply En.
Qed.

Program Instance: Abs Z := Zabs.
Next Obligation.
  split; intros E.
   now apply Z.abs_eq.
  now apply Z.abs_neq.
Qed.
