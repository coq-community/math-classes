Require Import 
  BigZ Program
  abstract_algebra positive_integers_naturals
  ZType_integers interfaces.integers interfaces.additional_operations.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ: Type := BigZ.t.

(* The following definition and lemma should be added to stdlib *)
Definition fastZ_shiftl (p x : fastZ) :=
  match p with
  | BigZ.Pos p => match x with 
     | BigZ.Pos x => BigZ.Pos (BigN.shiftl p x)
     | BigZ.Neg x => BigZ.Neg (BigN.shiftl p x)
     end
  | BigZ.Neg p => x
  end.

Lemma BigN_neg_is_zero p :  (BigZ.le 0 (BigZ.Neg p) -> BigN.to_Z p = 0)%Z.
Proof.
  intros E.
  apply Zle_antisym.
   apply Z.opp_nonneg_nonpos. trivial.
  apply BigN.spec_pos.
Qed.
 
Lemma spec_shiftl (p x : fastZ) : (BigZ.le 0 p -> BigZ.to_Z (fastZ_shiftl p x) = BigZ.to_Z x * 2 ^(BigZ.to_Z p))%Z.
Proof with auto.
  intros E. case_eq p; intros p' Ep'.
   case_eq x; intros x' Ex'; simpl.
    apply BigN.spec_shiftl.
   rewrite BigN.spec_shiftl. rewrite Z.mul_opp_l. reflexivity.
  subst. simpl. rewrite (BigN_neg_is_zero p')...
  simpl. rewrite Z.mul_1_r. reflexivity.
Qed.

Program Instance: ShiftLeft fastZ (Pos fastZ) := λ x y, fastZ_shiftl y x.
Next Obligation.
  intros x y. 
  BigZ_Integers.unfold_equiv. 
  rewrite spec_shiftl.
   rewrite rings.preserves_mult. 
   unfold pow, nat_pow, nat_pow_sig, BigZ_Integers.ZType_pow. simpl.
   rewrite BigZ.spec_pow. 
   reflexivity.
  apply BigZ_Integers.to_Z_sr_precedes_Zle. destruct y. trivial.
Qed.

Definition fastZ_shiftr (p x : fastZ) := 
  match p with
  | BigZ.Pos p => match x with 
     | BigZ.Pos x => BigZ.Pos (BigN.shiftr p x)
     | BigZ.Neg x => BigZ.Neg (BigN.shiftr p x)
     end
  | BigZ.Neg p => 0
  end.

(* Add Ring R : (rings.stdlib_ring_theory Z). *)

Program Instance: ShiftRight fastZ (Pos fastZ) := λ x y, fastZ_shiftr y x.
Next Obligation. Admitted.
