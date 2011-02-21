Require Import
  QArith BigQ Morphisms Program Field workaround_tactics
  abstract_algebra interfaces.integers 
  fast_integers field_of_fractions stdlib_rationals.
Require Export 
  QType_rationals.

Module Import BigQ_Rationals := QType_Rationals BigQ.

Definition fastQ: Type := BigQ.t.

(* Embedding of [fastZ] into [fastQ] *)
Definition fastZ_to_fastQ := BigQ.Qz.

Instance: Proper ((=) ==> (=)) fastZ_to_fastQ.
Proof.
  intros x y E. unfold_equiv. unfold Qeq. simpl.
  now rewrite E.
Qed.

Instance: SemiRing_Morphism fastZ_to_fastQ.
Proof. repeat (split; try apply _). Qed.

(* Embedding of [fastQ] into [Frac fastZ] *)
Definition fastQ_to_frac_fastZ (x : fastQ) : Frac fastZ :=
  match x with
  | BigQ.Qz n => 'n
  | BigQ.Qq n d =>
     match decide_rel (=) (BigN_BigZ.Z_of_N d) 0 with
     | left _ => 0
     | right E => frac n (BigN_BigZ.Z_of_N d) E
     end
  end.

Lemma fastQ_to_frac_fastZ_correct :
  fastQ_to_frac_fastZ = Frac_lift BigZ.of_Z ∘ Q_to_fracZ ∘ BigQ.to_Q.
Proof.
  intros x y E. rewrite <-E. clear y E.
  destruct x as [n | n d]. 
   unfold equiv, Frac_equiv. simpl.
   now posed_rewrite (jections.surjective_applied' BigZ.of_Z n).
  unfold equiv, Frac_equiv. simpl.
  case (decide_rel equiv (BigN_BigZ.Z_of_N d) 0); 
       case_eq (BigN.eq_bool d BigN.zero); simpl; intros E1 E2.
     reflexivity.
    contradict E1. now apply not_false_iff_true, BigN.eqb_eq.
   destruct E2. now apply BigN.eqb_eq in E1. 
  posed_rewrite (jections.surjective_applied' BigZ.of_Z n).
  unfold equiv, BigZ_Integers.ZType_equiv, BigZ.eq.
  rewrite 2!rings.preserves_mult.
  f_equal; try reflexivity. simpl.
  rewrite BigN.spec_of_pos.
  apply Z2P_correct.
  apply stdlib_binary_integers.Zlt_coincides. split.
   apply BigN.spec_pos.
  now apply not_symmetry.
Qed.

Instance: Injective fastQ_to_frac_fastZ.
Proof. rewrite fastQ_to_frac_fastZ_correct. apply _. Qed.

Instance: SemiRing_Morphism fastQ_to_frac_fastZ.
Proof. 
  eapply rings.semiring_morphism_proper.
   apply fastQ_to_frac_fastZ_correct. 
  apply _. 
Qed.
