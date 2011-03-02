Require Import
  Relation_Definitions Morphisms Ring Program Setoid
  abstract_algebra theory.rings
  implementations.semiring_pairs.
Require Export
  orders.rings.

Section contents.
Context `{SemiRing R} `{!SemiRingOrder o}.
Add Ring R : (stdlib_semiring_theory R).

Global Instance: ∀ (z : R), OrderPreserving (z+).
Proof.
  intros z. repeat (split; try apply _). intros x y E.
  apply srorder_plus in E. destruct E as [a [Ea1 Ea2]].
  apply srorder_plus.
  exists a. split. easy.
  now rewrite <-associativity, <-Ea2.
Qed.

Global Instance: ∀ (z : R), OrderPreserving (+z).
Proof. intro. apply order_preserving_flip. Qed.

Lemma plus_compat x1 y1 x2 y2 : x1 ≤ y1 → x2 ≤ y2 → x1 + x2 ≤ y1 + y2.
Proof.
  intros E1 E2.
  transitivity (y1 + x2).
   now apply (order_preserving (+ x2)).
  now apply (order_preserving (y1 +)).
Qed.

Lemma nonneg_plus_compat_r x y z : z ≤ x → 0 ≤ y → z ≤ x + y.
Proof. intros. rewrite <-(plus_0_r z). now apply plus_compat. Qed.

Lemma nonneg_plus_compat_l x y z : 0 ≤ x → z ≤ y → z ≤ x + y.
Proof. intros. rewrite <-(plus_0_l z). now apply plus_compat. Qed.

Global Instance nonneg_plus_compat x y : PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x + y).
Proof. apply nonneg_plus_compat_r. Qed.

Lemma nonpos_plus_compat x y : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof. intros. rewrite <-(plus_0_r 0). now apply plus_compat. Qed.

Global Instance: ∀ (z : R), PropHolds (0 ≤ z) → OrderPreserving (z *.).
Proof.
  intros z E. 
  repeat (split; try apply _).
  intros x y F.
  apply srorder_plus in F. destruct F as [a [Ea1 Ea2]]. 
  rewrite Ea2. 
  setoid_replace (z * (x + a)) with (z * x + z * a) by ring.
  apply nonneg_plus_compat_r.
   reflexivity.
  now apply srorder_mult.
Qed.

Global Instance: ∀ (z : R), PropHolds (0 ≤ z) → OrderPreserving (.* z).
Proof. intros. apply order_preserving_flip. Qed.

Lemma mult_compat x1 y1 x2 y2 : 
  0 ≤ x1 → 0 ≤ x2 → x1 ≤ y1 → x2 ≤ y2 → x1 * x2 ≤ y1 * y2.
Proof.
  intros E1x E1y E2x E2y.
  transitivity (y1 * x2).
   now apply (order_preserving_flip_ge_0 (.*.) x2).
  apply (order_preserving_ge_0 (.*.) y1); trivial.
  now transitivity x1.
Qed.

Global Instance nonneg_mult_compat (x y : R) : PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y).
Proof. intros. now apply srorder_mult. Qed.

Lemma ge1_mult_compat_r x y z : 0 ≤ x → z ≤ x → 1 ≤ y → z ≤ x * y.
Proof. 
  intros.
  transitivity x.
   easy.
  rewrite <-(mult_1_r x) at 1.
  now apply (order_preserving_ge_0 (.*.) x).
Qed.

Lemma ge1_mult_compat_l x y z : 0 ≤ x → 1 ≤ y → z ≤ x → z ≤ y * x.
Proof. intros. rewrite commutativity. now apply ge1_mult_compat_r. Qed.

Context `{∀ z, LeftCancellation (+) z}.

Global Instance: ∀ (z : R), StrictlyOrderPreserving (z+).
Proof.
  intros z.
  split; try apply _.
  intros x y [E1 E2]. split.
   now apply (order_preserving (z +)).
  intros F. apply E2.
  now apply (left_cancellation (+) z).
Qed.

Global Instance: ∀ (z : R), StrictlyOrderPreserving (+z).
Proof. 
  intros z.
  split; try apply _.
  intros x y E.
  rewrite 2!(commutativity _ z).
  now apply (strictly_order_preserving (z +)).
Qed.

Lemma plus_scompat_l x1 y1 x2 y2 : x1 < y1 → x2 ≤ y2 → x1 + x2 < y1 + y2.
Proof.
  intros E1 E2.
  apply sprecedes_trans_l with (y1 + x2).
   now apply (strictly_order_preserving (+ x2)).
  now apply (order_preserving (y1 +)).
Qed.

Lemma plus_scompat_r x1 y1 x2 y2 : x1 ≤ y1 → x2 < y2 → x1 + x2 < y1 + y2.
Proof.
  intros E1 E2.
  apply sprecedes_trans_r with (y1 + x2).
   now apply (order_preserving (+ x2)).
  now apply (strictly_order_preserving (y1 +)).
Qed.

Lemma nonneg_plus_scompat_r x y z : z < x → 0 ≤ y → z < x + y.
Proof. intros. rewrite <-(plus_0_r z). now apply plus_scompat_l. Qed.

Lemma nonneg_plus_scompat_l x y z : 0 ≤ x → z < y → z < x + y.
Proof. intros. rewrite <-(plus_0_l z). now apply plus_scompat_r. Qed.

Lemma pos_plus_scompat_r x y z : z ≤ x → 0 < y → z < x + y.
Proof. intros. rewrite <-(plus_0_r z). now apply plus_scompat_r. Qed.

Lemma pos_plus_scompat_l x y z : 0 < x → z ≤ y → z < x + y.
Proof. intros. rewrite <-(plus_0_l z). now apply plus_scompat_l. Qed.

Global Instance pos_plus_scompat x y : PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x + y).
Proof. intros. apply pos_plus_scompat_r. now apply sprecedes_weaken. easy. Qed.

Global Instance: ∀ (z : R), OrderPreservingBack (z +).
Proof. 
  intros z.
  split; try apply _. 
  intros x y E.
  apply srorder_plus in E. destruct E as [a [Ea1 Ea2]].
  apply srorder_plus. exists a. split. easy.
  apply (left_cancellation (+) z). 
  now rewrite associativity.
Qed.

Global Instance: ∀ (z : R), OrderPreservingBack (+ z).
Proof. intros. apply order_preserving_back_flip. Qed.

Context `{!TotalOrder (≤)} `{∀ z, PropHolds (z ≠ 0) → LeftCancellation (.*.) z}.

Global Instance: ∀ (z : R), PropHolds (0 < z) → OrderPreservingBack (z *.).
Proof.
  intros z E.
  repeat (split; try apply _). 
  intros x y F.
  destruct (total_order x y) as [G|G]. easy.
  apply (order_preserving_ge_0 (.*.) z) in G.
   apply equiv_precedes.
   apply (left_cancellation_ne_0 (.*.) z).
    now apply not_symmetry, neq_precedes_sprecedes.
   now eapply (antisymmetry (≤)).
  now apply sprecedes_weaken.
Qed.

Global Instance: ∀ (z : R), PropHolds (0 < z) → OrderPreservingBack (.* z).
Proof. intros. apply order_preserving_back_flip. Qed.

Global Instance: ∀ (z : R), PropHolds (0 < z) → StrictlyOrderPreserving (z *.).
Proof.
  intros z Ez.
  split; try apply _.
  intros x y [E1 E2]. split.
   apply (order_preserving_ge_0 (.*.) z). now apply sprecedes_weaken. easy.
  intros F. apply E2.
  apply (left_cancellation_ne_0 (.*.) z). now apply not_symmetry, neq_precedes_sprecedes. easy.
Qed.

Global Instance: ∀ (z : R), PropHolds (0 < z) → StrictlyOrderPreserving (.* z).
Proof. 
  intros z.
  split; try apply _.
  intros x y E.
  rewrite 2!(commutativity _ z).
  now apply (strictly_order_preserving (z *.)).
Qed.

Global Instance pos_mult_scompat x y : PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y).
Proof. 
  intros E F.
  rewrite <-(mult_0_r x).
  now apply (strictly_order_preserving (x *.)).
Qed.

Lemma square_nonneg x : 0 ≤ x * x.
Proof with auto.
  apply (order_preserving_back SRpair_inject).
  rewrite preserves_mult.
  apply square_nonneg.
Qed.

Global Instance precedes_0_1 : PropHolds (0 ≤ 1).
Proof. red. setoid_replace 1 with (1 * 1) by ring. apply square_nonneg. Qed.

Global Instance precedes_0_2 : PropHolds (0 ≤ 2).
Proof. apply _. Qed.

Global Instance precedes_0_3 : PropHolds (0 ≤ 3).
Proof. apply _. Qed.

Global Instance precedes_0_4 : PropHolds (0 ≤ 4).
Proof. apply _. Qed.

Lemma precedes_1_2 : 1 ≤ 2.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. easy. Qed.

Lemma precedes_1_3 : 1 ≤ 3.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. apply precedes_1_2. Qed.

Lemma precedes_1_4 : 1 ≤ 4.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. apply precedes_1_3. Qed.

Lemma precedes_2_3 : 2 ≤ 3.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. easy. Qed.

Lemma precedes_2_4 : 2 ≤ 4.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. apply precedes_2_3. Qed.

Lemma precedes_3_4 : 3 ≤ 4.
Proof. apply nonneg_plus_compat_l. now apply precedes_0_1. easy. Qed.

Context `{!PropHolds (1 ≠ 0)}.

Global Instance sprecedes_0_1 : PropHolds (0 < 1).
Proof. split. apply precedes_0_1. now apply not_symmetry. Qed.

Global Instance sprecedes_0_2 : PropHolds (0 < 2).
Proof. apply _. Qed.

Global Instance sprecedes_0_3 : PropHolds (0 < 3).
Proof. apply _. Qed.

Global Instance sprecedes_0_4 : PropHolds (0 < 4).
Proof. apply _. Qed.

Lemma sprecedes_1_2 : 1 < 2.
Proof. apply pos_plus_scompat_l. apply sprecedes_0_1. easy. Qed.

Lemma sprecedes_1_3 : 1 < 3.
Proof. apply pos_plus_scompat_l. apply sprecedes_0_1. apply precedes_1_2. Qed.

Lemma sprecedes_1_4 : 1 < 4.
Proof. apply pos_plus_scompat_l. apply sprecedes_0_1. apply precedes_1_3. Qed.

Lemma sprecedes_2_3 : 2 < 3.
Proof. apply pos_plus_scompat_l. apply sprecedes_0_1. easy. Qed.

Lemma sprecedes_2_4 : 2 < 4.
Proof. apply pos_plus_scompat_l. apply sprecedes_0_1. apply precedes_2_3. Qed.

Lemma sprecedes_3_4 : 3 < 4.
Proof. apply pos_plus_scompat_l. apply sprecedes_0_1. easy. Qed.

Global Instance ne_0_2 : PropHolds (2 ≠ 0).
Proof. red. apply not_symmetry, neq_precedes_sprecedes, sprecedes_0_2. Qed.

Lemma not_precedes_1_0 : ¬1 ≤ 0.
Proof. apply not_precedes_sprecedes, sprecedes_0_1. Qed.

Lemma not_precedes_2_0 : ¬2 ≤ 0.
Proof. apply not_precedes_sprecedes, sprecedes_0_2. Qed.

Lemma ge1_mult_compat x y : 1 ≤ x → 1 ≤ y → 1 ≤ x * y.
Proof. 
  intros.
  apply ge1_mult_compat_r; trivial. 
  transitivity 1; trivial. apply precedes_0_1.
Qed.

Lemma gt1_mult_scompat_l x y : 1 < x → 1 ≤ y → 1 < x * y.
Proof. 
  intros. 
  apply sprecedes_trans_l with x; trivial.
  apply ge1_mult_compat_r; try easy.
  transitivity 1. apply precedes_0_1. firstorder.
Qed.

Lemma gt1_mult_scompat_r x y : 1 ≤ x → 1 < y → 1 < x * y.
Proof. intros. rewrite commutativity. now apply gt1_mult_scompat_l. Qed.

Section another_semiring.
  Context `{SemiRing R2} `{o2 : Order R2} `{!SemiRingOrder o2} {f : R → R2} `{!SemiRing_Morphism f}.

  (* If a morphism agrees on the positive cone then it is order preserving *)    
  Lemma preserving_preserves_nonneg : (∀ x, 0 ≤ x → 0 ≤ f x) → OrderPreserving f.
  Proof.
    intros E.
    repeat (split; try apply _).
    intros x y F.
    apply srorder_plus in F. destruct F as [z [Ez1 Ez2]].
    apply srorder_plus. exists (f z). split.
     now apply E.
    now rewrite Ez2, preserves_plus.
  Qed.

  Global Instance preserves_nonneg `{!OrderPreserving f} x : PropHolds (0 ≤ x) → PropHolds (0 ≤ f x).
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_nonpos `{!OrderPreserving f} x : x ≤ 0 → f x ≤ 0.
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_pos `{!StrictlyOrderPreserving f} x : PropHolds (0 < x) → PropHolds (0 < f x).
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (strictly_order_preserving f). Qed.

  Lemma preserves_neg `{!StrictlyOrderPreserving f} x : x < 0 → f x < 0.
  Proof. intros. rewrite <-(preserves_0 (f:=f)). now apply (strictly_order_preserving f). Qed.

  Lemma preserves_ge1 `{!OrderPreserving f} x : 1 ≤ x → 1 ≤ f x.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_le1 `{!OrderPreserving f} x : x ≤ 1 → f x ≤ 1.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (order_preserving f). Qed.

  Lemma preserves_gt1 `{!StrictlyOrderPreserving f} x : 1 < x → 1 < f x.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (strictly_order_preserving f). Qed.

  Lemma preserves_lt1 `{!StrictlyOrderPreserving f} x : x < 1 → f x < 1.
  Proof. intros. rewrite <-(preserves_1 (f:=f)). now apply (strictly_order_preserving f). Qed.
End another_semiring.
End contents.
