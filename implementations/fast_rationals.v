Require
  MathClasses.theory.shiftl MathClasses.theory.int_pow.
Require Import
  Coq.QArith.QArith Coq.Numbers.Rational.BigQ.BigQ
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.integers MathClasses.interfaces.rationals MathClasses.interfaces.additional_operations
  MathClasses.implementations.fast_naturals MathClasses.implementations.fast_integers MathClasses.implementations.field_of_fractions MathClasses.implementations.stdlib_rationals.
Require Export
  MathClasses.implementations.QType_rationals.

Module Import BigQ_Rationals := QType_Rationals BigQ.

(* Embedding of [bigZ] into [bigQ] *)
Instance inject_bigZ_bigQ: Cast bigZ bigQ := BigQ.Qz.
Instance inject_bigN_bigQ: Cast bigN bigQ := cast bigZ bigQ ∘ cast bigN bigZ.
Instance inject_Z_bigQ: Cast Z bigQ := cast bigZ bigQ ∘ cast Z bigZ.

Instance: Proper ((=) ==> (=)) inject_bigZ_bigQ.
Proof. intros x y E. unfold_equiv. unfold Qeq. simpl. now rewrite E. Qed.
Instance: SemiRing_Morphism inject_bigZ_bigQ.
Proof. repeat (split; try apply _). Qed.

Instance: SemiRing_Morphism inject_bigN_bigQ.
Proof. unfold inject_bigN_bigQ. apply _. Qed.
Instance: SemiRing_Morphism inject_Z_bigQ.
Proof. unfold inject_Z_bigQ. apply _. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) BigQ.Qq.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  do 4 red. simpl.
  case_eq (BigN.eqb x2 BigN.zero); intros Ex2; case_eq (BigN.eqb y2 BigN.zero); intros Ey2.
     reflexivity.
    rewrite E2 in Ex2. edestruct eq_true_false_abs; eassumption.
   rewrite E2 in Ex2. edestruct eq_true_false_abs; eassumption.
  simpl. do 3 red in E1. do 3 red in E2. now rewrite E1, E2.
Qed.

(* Why is the below not in the stdlib? *)
Lemma bigQ_div_bigQq (n : bigZ) (d : bigN) :
  BigQ.Qq n d = 'n / 'd.
Proof.
  change (n # d == 'n / (BigQ.Qz (BigZ.Pos d)))%bigQ.
  unfold BigQ.div, BigQ.inv.
  case_eq (BigZ.zero ?= BigZ.Pos d)%bigZ; intros Ed.
    transitivity BigQ.zero; [| ring].
    do 2 red. simpl.
    case_eq (BigN.eqb d BigN.zero); intros Ed2; [reflexivity |].
    rewrite BigZ.spec_compare in Ed.
    destruct (proj2 (not_true_iff_false _) Ed2).
    apply BigN.eqb_eq. symmetry. now apply Zcompare_Eq_eq.
   unfold BigQ.mul. simpl. rewrite right_identity. reflexivity.
  destruct (BigZ.compare_spec BigZ.zero (BigZ.Pos d)); try discriminate.
  destruct (orders.lt_not_le_flip 0 ('d : bigZ)); trivial.
  now apply nat_int.to_semiring_nonneg.
Qed.

Lemma bigQ_div_bigQq_alt (n : bigZ) (d : bigN) :
  BigQ.Qq n d = 'n / 'cast bigN bigZ d.
Proof. apply bigQ_div_bigQq. Qed.

(* Embedding of [bigQ] into [Frac bigZ] *)
Instance inject_bigQ_frac_bigZ: Cast bigQ (Frac bigZ) := λ x,
  match x with
  | BigQ.Qz n => 'n
  | BigQ.Qq n d =>
     match decide_rel (=) ('d : bigZ) 0 with
     | left _ => 0
     | right E => frac n ('d) E
     end
  end.

Lemma inject_bigQ_frac_bigZ_correct:
 cast bigQ (Frac bigZ) = rationals_to_frac bigQ bigZ.
Proof.
  intros x y E. rewrite <-E. clear y E.
  destruct x as [n|n d].
   rapply (integers.to_ring_unique_alt
     (cast bigZ (Frac bigZ)) (rationals_to_frac bigQ bigZ ∘ cast bigZ bigQ)).
  unfold cast at 1. simpl.
  rewrite bigQ_div_bigQq_alt.
  rewrite rings.preserves_mult, dec_fields.preserves_dec_recip.
  case (decide_rel (=) ('d : bigZ) 0); intros Ed.
   rewrite Ed. rewrite !rings.preserves_0. rewrite dec_recip_0.
   now rewrite rings.mult_0_r.
  rewrite 2!(integers.to_ring_twice _ _ (cast bigZ (Frac bigZ))).
  now rewrite Frac_dec_mult_num_den at 1.
Qed.

Instance: Injective inject_bigQ_frac_bigZ.
Proof. rewrite inject_bigQ_frac_bigZ_correct. apply _. Qed.

Instance: SemiRing_Morphism inject_bigQ_frac_bigZ.
Proof.
  eapply rings.semiring_morphism_proper.
   apply inject_bigQ_frac_bigZ_correct.
  apply _.
Qed.

(* Efficient shiftl on [bigQ] *)
Instance bigQ_shiftl: ShiftL bigQ bigZ := λ x k,
  match k with
  | BigZ.Pos k =>
    match x with
    | BigQ.Qz n => '(n ≪ k)
    | BigQ.Qq n d => BigQ.Qq (n ≪ k) d
    end
  | BigZ.Neg k =>
    match x with
    | BigQ.Qz n => BigQ.Qq n (1 ≪ k)
    | BigQ.Qq n d => BigQ.Qq n (d ≪ k)
    end
  end.

Instance: ShiftLSpec bigQ bigZ _.
Proof.
  apply shiftl_spec_from_int_pow.
  unfold shiftl, bigQ_shiftl.
  intros [n|n d] [k|k].
     rewrite shiftl.preserves_shiftl.
     now rewrite <-shiftl.shiftl_int_pow, shiftl.preserves_shiftl_exp.
    change (BigZ.Neg k) with (-'k : bigZ).
    rewrite int_pow.int_pow_negate.
    rewrite bigQ_div_bigQq, shiftl.preserves_shiftl.
    rewrite <-(shiftl.preserves_shiftl_exp (f:=cast bigN bigZ)).
    now rewrite rings.preserves_1, shiftl.shiftl_base_1_int_pow.
   rewrite 2!bigQ_div_bigQq.
   rewrite shiftl.preserves_shiftl.
   rewrite <-(shiftl.preserves_shiftl_exp (f:=cast bigN bigZ)).
   rewrite shiftl.shiftl_int_pow.
   now rewrite <-2!associativity, (commutativity (/cast bigN bigQ d)).
  change (BigZ.Neg k) with (-'k : bigZ).
  rewrite int_pow.int_pow_negate.
  rewrite 2!bigQ_div_bigQq.
  rewrite shiftl.preserves_shiftl.
  rewrite <-(shiftl.preserves_shiftl_exp (f:=cast bigN bigZ)).
  rewrite shiftl.shiftl_int_pow.
  now rewrite dec_fields.dec_recip_distr, associativity.
Qed.

Instance bigQ_Zshiftl: ShiftL bigQ Z := λ x k, x ≪ 'k.

Instance: ShiftLSpec bigQ Z _.
Proof.
  split; unfold shiftl, bigQ_Zshiftl.
    solve_proper.
   intro. now apply shiftl_0.
  intros x n.
  rewrite rings.preserves_plus. now apply shiftl_S.
Qed.
