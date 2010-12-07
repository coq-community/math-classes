Require 
  peano_naturals orders.semiring
  theory.integers theory.rings theory.naturals.
Require Import
  Morphisms Ring Program RelationClasses Setoid
  abstract_algebra
  interfaces.integers interfaces.naturals interfaces.additional_operations.

Definition Pos R `{RingZero R} `{Order R} := { z : R | 0 ≤ z }.

Section positive_integers_naturals.
Context Z `{Integers Z}.

Add Ring Z: (rings.stdlib_ring_theory Z).

Let ZPos := Pos Z.

(* Operations *)
Global Program Instance ZPos_plus: RingPlus ZPos := λ x y, exist _ (`x + `y) _. 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  simpl. apply semiring.sr_precedes_nonneg_plus_compat...
Qed.

Global Program Instance ZPos_mult: RingMult ZPos := λ x y, exist _ (`x * `y) _. 
Next Obligation with auto.
  destruct x as [x Hx], y as [y Hy].
  simpl. apply semiring.sr_precedes_nonneg_mult_compat...
Qed.

Global Program Instance ZPos_0: RingZero ZPos := exist _ 0 _.
Next Obligation. reflexivity. Qed. 

Global Program Instance ZPos_1: RingOne ZPos := exist _ 1 _.
Next Obligation. apply semiring.sr_precedes_0_1. Qed.

Global Instance ZPos_equiv: Equiv ZPos := λ x y, `x = `y.

Local Ltac unfold_equivs := unfold equiv, ZPos_equiv in *; simpl in *.

Instance: Proper ((=) ==> (=) ==> (=)) ZPos_plus.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs. 
  rewrite E1, E2. reflexivity.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) ZPos_mult.
Proof.
  intros [x1 Ex1] [y1 Ey1] E1 [x2 Ex2] [y2 Ey2] E2. unfold_equivs. 
  rewrite E1, E2. reflexivity.
Qed.

(* Properties: *)
Instance: Associative ZPos_plus.
Proof. intros [x Ex] [y Ey] [z Ez]. unfold_equivs. apply associativity. Qed.
Instance: Associative ZPos_mult. 
Proof. intros [x Ex] [y Ey] [z Ez]. unfold_equivs. apply associativity. Qed.
Instance: Commutative ZPos_plus.
Proof. intros [x Ex] [y Ey]. unfold_equivs. apply commutativity. Qed.
Instance: Commutative ZPos_mult.
Proof. intros [x Ex] [y Ey]. unfold_equivs. apply commutativity. Qed.
Instance: Distribute ZPos_mult ZPos_plus.
Proof. split; intros [x Ex] [y Ey] [z Ez]; unfold_equivs. apply distribute_l. apply distribute_r. Qed.
Instance: LeftIdentity ZPos_plus ZPos_0.
Proof. intros [x Ex]. unfold_equivs. apply left_identity. Qed.
Instance: RightIdentity ZPos_plus ZPos_0.
Proof. intros [x Ex]. unfold_equivs. apply right_identity. Qed.
Instance: LeftIdentity ZPos_mult ZPos_1.
Proof. intros [x Ex]. unfold_equivs. apply left_identity. Qed.
Instance: RightIdentity ZPos_mult ZPos_1.
Proof. intros [x Ex]. unfold_equivs. apply right_identity. Qed.
Instance: LeftAbsorb ZPos_mult ZPos_0.
Proof. intros [x Ex]. unfold_equivs. apply left_absorb. Qed.

(* Structures: *)
Instance: SemiRing ZPos. 
Proof. repeat (split; try apply _). Qed.

(* Misc *)
Global Instance ZPos_equiv_dec `{∀ x y : Z, Decision (x = y)} : ∀ x y: ZPos, Decision (x = y) 
  := λ x y, decide (`x = `y).

Program Definition of_nat (x : nat) : Pos Z := exist (λ x, 0 ≤ x) (naturals_to_semiring nat Z x) _.
Next Obligation. 
  apply semiring.zero_sr_precedes_nat.
Qed.

Instance: Proper ((=) ==> (=)) of_nat.
Proof.
  intros x y E. unfold_equivs. 
  rewrite E. reflexivity.
Qed.

Instance: SemiRing_Morphism of_nat.
Proof with reflexivity.
  repeat (split; try apply _); repeat intro; unfold_equivs.
  apply rings.preserves_plus...
  apply rings.preserves_0...
  apply rings.preserves_mult...
  apply rings.preserves_1...
Qed.

Program Instance to_nat: Inverse of_nat := λ x, int_abs Z nat (`x).

Instance: Proper ((=) ==> (=)) to_nat.
Proof.
  intros [x Ex] [y Ey] E. unfold to_nat. unfold_equivs. 
  rewrite E. reflexivity.
Qed.

Instance ZPos_to_nat_sr_morphism: SemiRing_Morphism to_nat.
Proof with auto.
  repeat (split; try apply _). 

  intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
  apply integers.abs_nonneg_plus...

  apply integers.abs_0.
  
  intros [x Ex] [y Ey]. unfold to_nat; unfold_equivs. simpl.
  apply integers.abs_nonneg_mult...

  apply integers.abs_1.
Qed.

Instance: Surjective of_nat.
Proof.
  split. 2: apply _.
  intros [x Ex] y E. rewrite <- E.
  unfold to_nat, of_nat. unfold_equivs.
  apply integers.abs_nonneg. assumption.
Qed.

Global Instance: NaturalsToSemiRing ZPos := naturals.retract_is_nat_to_sr of_nat.
Global Instance: Naturals ZPos := naturals.retract_is_nat of_nat.

(* * Embedding of ZPos into Z *)
Global Instance: SemiRing_Morphism (@proj1_sig Z _).
Proof with auto; try reflexivity.
  repeat (split; try apply _); repeat intro; unfold_equivs...
Qed.

(* Are these lemmas really needed *)
Lemma ZPos_to_semiring_self x p : naturals_to_semiring ZPos Z (exist _ x p) = x.
Proof.
  apply integers.abs_nonneg. assumption.
Qed.

Lemma ZPos_to_semiring_proj_1 x : naturals_to_semiring ZPos Z x = `x.
Proof.
  destruct x. simpl. apply ZPos_to_semiring_self.
Qed.

Lemma ZPos_to_semiring_proj_2 x : 
  naturals_to_semiring nat Z x = ` (naturals_to_semiring nat ZPos x).
Proof.
  rewrite <-ZPos_to_semiring_proj_1.
  symmetry. apply (naturals.to_semiring_twice nat ZPos Z).
Qed.

Lemma ZPos_to_nat_int_abs x p : naturals_to_semiring ZPos nat (exist _ x p) = int_abs Z nat x.
Proof.
  replace (int_abs Z nat x) with (to_nat (exist _ x p)) by reflexivity.
  apply naturals.to_semiring_unique'. apply _. apply ZPos_to_nat_sr_morphism.
  reflexivity.
Qed.

Lemma ZPos_int_nat_precedes (x y : ZPos) : `x ≤ `y → x ≤ y.
Proof.
  intros [z Ez].
  exists z.
  unfold_equivs. rewrite <-ZPos_to_semiring_proj_2.
  assumption.
Qed.

Lemma ZPos_nat_int_precedes (x y : ZPos) : x ≤ y → `x ≤ `y.
Proof with auto.
  intros [z Ez].
  exists z.
  unfold_equivs. rewrite <-ZPos_to_semiring_proj_2 in Ez.
  assumption.
Qed.

(* Efficient comparison *)
Global Instance ZPos_precedes_dec `{∀ x y : Z, Decision (x ≤ y)} : ∀ x y: ZPos, Decision (x ≤ y).
Proof with auto.
  intros x y.
  destruct (decide (`x ≤ `y)) as [El | Er]. 
  left. apply ZPos_int_nat_precedes...
  right. intro E. apply Er. apply ZPos_nat_int_precedes...
Defined.

End positive_integers_naturals.

(* 
  For an unknown reason instance resolution fails to find this instance when it's contained in 
  the above section. However, then its type is equivalent to the function below and it is listed
  in typeclass_instances.. Todo: further investigation.

  Also, it might be more elegant to use an existing instance of CutMinus Z (whose
  default implementation is similar to the definition below).
*)
Program Instance ZPos_cut_minus `{Integers Z} 
  `{Zdec : ∀ x y : Z, Decision (x ≤ y)} `{!RingMinus Z} : CutMinus (Pos Z)
  := λ (x y : Pos Z), (exist _ (
     if decide (`x ≤ `y) 
     then 0:(Pos Z)
     else exist (λ z, 0 ≤ z) (`x - `y) _
  ) _).

Next Obligation with auto.
  apply semiring.sr_precedes_0_minus. apply orders.precedes_flip...
Qed.

Next Obligation with auto.
  case (decide (`x ≤ `y)); intros E; split; intros F.
  rewrite left_identity. apply (antisymmetry (≤))...
  apply orders.strictly_precedes_weaken...  apply ZPos_int_nat_precedes...
  reflexivity.
  unfold equiv, ZPos_equiv. simpl. 
    rewrite rings.ring_minus_correct, <-associativity, rings.plus_opp_l, right_identity. reflexivity.
  unfold equiv, ZPos_equiv. simpl. 
    apply ZPos_nat_int_precedes in F. contradiction.
Qed.
