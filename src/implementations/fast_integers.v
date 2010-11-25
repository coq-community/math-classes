Require Import 
  BigZ Program
  abstract_algebra positive_integers_naturals
  ZType_integers interfaces.integers interfaces.additional_operations.

Module BigZ_Integers := ZType_Integers BigZ.

Definition fastZ: Type := BigZ.t.

Print BigN.log2.
(* Some ad hoc hacks to integrate BigN's shiftl and shiftr *)
Definition fastZ_shiftl (p : fastZ) (x : fastZ) :=
  match p with
  | BigZ.Pos p => match x with 
     | BigZ.Pos x => BigZ.Pos (BigN.shiftl p x)
     | BigZ.Neg x => BigZ.Neg (BigN.shiftl p x)
     end
  | BigZ.Neg p => 0
  end.

Definition fastZ_shiftr (p : fastZ) (x : fastZ) := 
  match p with
  | BigZ.Pos p => match x with 
     | BigZ.Pos x => BigZ.Pos (BigN.shiftr p x)
     | BigZ.Neg x => BigZ.Neg (BigN.shiftr p x)
     end
  | BigZ.Neg p => 0
  end.

Add Ring R : (rings.stdlib_ring_theory Z).
Program Instance: ShiftLeft fastZ (Pos fastZ) := fastZ_shiftl.
Next Obligation.
  unfold fastZ_shiftl.
  intros [x [[y|y] Ey] |x]; simpl.
  unfold fastZ_shiftl. 
  program_simpl. destruct y as [[? | ?] ?]. simpl in *. inject Heq_y.
  unfold equiv, BigZ_Integers.anyZ_eq, BigZ.eq. simpl.
  rewrite BigN.spec_shiftl.
  unfold pow, nat_pow, nat_pow_sig, BigZ_Integers.anyZ_pow. simpl.
  rewrite rings.preserves_mult.
  replace (2:bigZ) with (BigZ.Pos 2) by reflexivity.
  rewrite BigZ.spec_pow. simpl. reflexivity.
  simpl in *. discriminate.
Qed.

Next Obligation.
  program_simpl. destruct y as [[? | ?] ?]. simpl in *. inject Heq_y.
  unfold equiv, BigZ_Integers.anyZ_eq, BigZ.eq. simpl.
  rewrite BigN.spec_shiftl.
  unfold pow, nat_pow, nat_pow_sig, BigZ_Integers.anyZ_pow. simpl.
  rewrite rings.preserves_mult.
  replace (2:bigZ) with (BigZ.Pos 2) by reflexivity.
  rewrite BigZ.spec_pow. rewrite Zopp_mult_distr_l. simpl. reflexivity.
  simpl in *. discriminate.
Qed.

Next Obligation. 
  program_simpl. destruct y as [[? | ?] ?]. simpl in *. discriminate.
  exfalso. clear Heq_y.
  apply (BigZ_Integers.to_Z_sr_precedes_Zle _ _) in p.
  simpl in p.
Admitted.

Program Instance: ShiftRight fastZ (Pos fastZ) := λ (x : fastZ) (y : Pos fastZ), 
  match y with
  | BigZ.Pos y => match x with 
     | BigZ.Pos x => BigZ.Pos (BigN.shiftr y x)
     | BigZ.Neg x => BigZ.Neg (BigN.shiftr y x)
     end
  | BigZ.Neg y => 0
  end.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
