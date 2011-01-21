Require Import
  QArith BigQ Morphisms Program Field
  abstract_algebra 
  interfaces.rationals QType_rationals
  interfaces.integers fast_integers.

Module Import BigQ_Rationals := QType_Rationals BigQ.

Definition fastQ: Type := BigQ.t.

Definition fastZ_to_fastQ := BigQ.Qz.

Instance: Proper ((=) ==> (=)) fastZ_to_fastQ.
Proof.
  intros x y E. unfold_equiv. unfold Qeq. simpl.
  rewrite E. reflexivity.
Qed.

Instance: SemiRing_Morphism fastZ_to_fastQ.
Proof. repeat (split; try apply _). Qed.

Instance fastQ_to_frac: Inverse (λ p, fastZ_to_fastQ (fst p) * / fastZ_to_fastQ (snd p)) 
  := λ x, match x with
  | BigQ.Qz x => (x, 1)
  | BigQ.Qq x y => (x, BigN_BigZ.Z_of_N y)
  end.

Add Field F: (fields.stdlib_field_theory BigQ.t_).

Lemma fastQ_fastZ_surjective_aux y : (0 < y)%Z →  
  (Qnum (Qinv (y # 1)) * ' Z2P y)%Z ≡ (' Qden (Qinv (y # 1)))%Z.
Proof with try reflexivity; auto.
  intros E.
  destruct y as [| | y]...
  destruct (Zlt_irrefl 0)...
  destruct (Zlt_asym _ _ (Zlt_neg_0 y))...
Qed.

Instance: Surjective (λ p, fastZ_to_fastQ (fst p) * / fastZ_to_fastQ (snd p)).
Proof with auto; try reflexivity.
  split.
    intros x y E. rewrite <- E. clear E y. 
    unfold id, compose, inverse, fastZ_to_fastQ.
    destruct x as [x | x y]; simpl. 
    rewrite rings.preserves_1. field. 
    apply (ne_zero 1).
   unfold_equiv.
   rewrite rings.preserves_mult, fields.preserves_dec_mult_inv.
   unfold QArith_base.Qeq. simpl. 
   BigQ.destr_eqb; intros F; simpl.
    rewrite F, BigN.spec_0. simpl. 
    rewrite right_absorb, left_absorb...
   rewrite <-associativity. apply sg_mor...
   apply fastQ_fastZ_surjective_aux...
  repeat (split; try apply _).
  intros x y E. rewrite E. reflexivity...
Qed.
