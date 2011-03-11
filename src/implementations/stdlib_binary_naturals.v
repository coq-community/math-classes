Require Import 
  NArith
  peano_naturals theory.naturals
  abstract_algebra interfaces.naturals.  

(* canonical names for relations/operations/constants: *)
Instance N_equiv : Equiv N := eq.
Instance N_0 : RingZero N := 0%N.
Instance N_1 : RingOne N := 1%N.
Instance N_plus : RingPlus N := Nplus.
Instance N_mult : RingMult N := Nmult.

(* properties: *)
Instance: SemiRing N.
Proof.
  repeat (split; try apply _); repeat intro.
          now apply Nmult_assoc.
         now apply Nmult_1_l.
        now apply Nmult_1_r.
       now apply Nmult_comm.
      now apply Nplus_assoc.
     now apply Nplus_0_r.
    now apply Nplus_comm.
   now apply Nmult_plus_distr_l.
  now apply Nmult_plus_distr_r.
Qed.

Instance: ∀ x y: N, Decision (x = y) := N_eq_dec.

(* order *)
Instance: Order N := Nle.

Instance: SemiRingOrder Nle.
Proof with auto.
  split.
    repeat (split; try apply _)...
    exact N.le_antisymm.
   intros x y. split.
    intros E. exists (Nminus y x).
    split.
     now apply N.le_add_le_sub_r.
    symmetry. rewrite commutativity. now apply N.sub_add.
   intros [z [_ Ez]]. rewrite Ez.
   now apply N.le_add_r.
  intros. now apply Nle_0. 
Qed.

Instance: TotalOrder Nle.
Proof with auto.
  intros x y.
  now apply N.le_ge_cases.
Qed.

Program Instance: ∀ x y: N, Decision (x ≤ y) := λ y x, 
  match Ncompare y x with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. now apply not_symmetry. Qed.

Lemma Qlt_coincides x y : (x < y)%N ↔ x < y.
Proof with trivial.
  split.
   intro. now apply N.le_neq.
  intros [E1 E2]. now apply N.T.le_neq_lt.
Qed.

Instance inject_nat_N: Coerce nat N := N_of_nat.
Instance inject_N_nat: Coerce N nat := nat_of_N.

Instance: SemiRing_Morphism nat_of_N.
Proof. 
  repeat (split; try apply _); repeat intro.
   now apply nat_of_Nplus.
  now apply nat_of_Nmult.
Qed.

Instance: Inverse nat_of_N := N_of_nat.

Instance: Surjective nat_of_N.
Proof. constructor. intros x y E. rewrite <- E. now apply nat_of_N_of_nat. now apply _. Qed.

Instance: Injective nat_of_N.
Proof. constructor. exact nat_of_N_inj. apply _. Qed.

Instance: Bijective nat_of_N.

Instance: Inverse N_of_nat := nat_of_N.

Instance: Bijective N_of_nat.
Proof. apply jections.flip_bijection, _. Qed.

Instance: SemiRing_Morphism N_of_nat.
Proof. change (SemiRing_Morphism (nat_of_N⁻¹)). split; apply _. Qed.

Instance: NaturalsToSemiRing N := retract_is_nat_to_sr N_of_nat.
Instance: Naturals N := retract_is_nat N_of_nat.
