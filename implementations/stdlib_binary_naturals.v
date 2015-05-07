Require Import
  Coq.NArith.NArith MathClasses.implementations.peano_naturals MathClasses.theory.naturals
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.naturals MathClasses.interfaces.orders
  MathClasses.interfaces.additional_operations.  

(* canonical names for relations/operations/constants: *)
Instance N_equiv : Equiv N := eq.
Instance N_0 : Zero N := 0%N.
Instance N_1 : One N := 1%N.
Instance N_plus : Plus N := Nplus.
Instance N_mult : Mult N := Nmult.

(* properties: *)
Instance: SemiRing N.
Proof.
  repeat (split; try apply _); repeat intro.
         now apply Nplus_assoc.
        now apply Nplus_0_r.
       now apply Nplus_comm.
      now apply Nmult_assoc.
     now apply Nmult_1_l.
    now apply Nmult_1_r.
   now apply Nmult_comm.
  now apply Nmult_plus_distr_l.
Qed.

Instance: ∀ x y : N, Decision (x = y) := N_eq_dec.

Instance inject_nat_N: Cast nat N := N_of_nat.
Instance inject_N_nat: Cast N nat := nat_of_N.

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

Instance: Bijective nat_of_N := {}.

Instance: Inverse N_of_nat := nat_of_N.

Instance: Bijective N_of_nat.
Proof. apply jections.flip_bijection. Qed.

Instance: SemiRing_Morphism N_of_nat.
Proof. change (SemiRing_Morphism (nat_of_N⁻¹)). split; apply _. Qed.

Instance: NaturalsToSemiRing N := retract_is_nat_to_sr N_of_nat.
Instance: Naturals N := retract_is_nat N_of_nat.

(* order *)
Instance N_le: Le N := Nle.
Instance N_lt: Lt N := Nlt.

Instance: FullPseudoSemiRingOrder N_le N_lt.
Proof.
  assert (PartialOrder N_le).
   repeat (split; try apply _). exact N.le_antisymm.
  assert (SemiRingOrder N_le).
   split; try apply _.
     intros x y E. exists (Nminus y x).
     symmetry. rewrite commutativity. now apply N.sub_add.
    repeat (split; try apply _); intros.
     now apply N.add_le_mono_l.
    eapply N.add_le_mono_l. eassumption.
   intros. now apply Nle_0.
  assert (TotalRelation N_le).
   intros x y. now apply N.le_ge_cases.
  rapply semirings.dec_full_pseudo_srorder.
  split.
   intro. now apply N.le_neq.
  intros [E1 E2]. now apply N.Private_Tac.le_neq_lt.
Qed.

Program Instance: ∀ x y: N, Decision (x ≤ y) := λ y x,
  match Ncompare y x with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. now apply not_symmetry. Qed.

Instance N_cut_minus: CutMinus N := Nminus.
Instance: CutMinusSpec N _.
Proof.
  split; try apply _.
   intros. now apply N.sub_add.
  intros. now apply Nminus_N0_Nle.
Qed.
