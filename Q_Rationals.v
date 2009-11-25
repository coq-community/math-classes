Require
  stdZ_Integers.
Require Import
  QArith_base Ring Morphisms
  Structures RingOps FieldOps AbstractProperties BoringInstances
  AbstractIntegers AbstractRationals.

Instance: Proper (equiv ==> equiv) inject_Z. Proof. intros x y H. info rewrite H. reflexivity. Qed.

Instance: SemiGroup_Morphism inject_Z (Aop:=Zmult) (Bop:=Qmult) := { preserves_sg_op := fun _ _  => refl_equal }.

Instance: SemiGroup_Morphism inject_Z (Aop:=Zplus) (Bop:=Qplus) := { preserves_sg_op := _ }.
Proof. intros. unfold inject_Z, sg_op, Qplus. repeat rewrite Zmult_1_r. reflexivity. Qed.

Instance: Monoid_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) (Amult:=Zplus) (Bmult:=Qplus) := { preserves_mon_unit := refl_equal }.

Instance: Monoid_Morphism inject_Z (Aunit:=1%Z) (Bunit:=1%Q) (Amult:=Zmult) (Bmult:=Qmult) := { preserves_mon_unit := refl_equal }.

Instance: Group_Morphism inject_Z (Aunit:=0%Z) (Bunit:=0%Q) := { preserves_inv := fun _ => refl_equal }.

Instance: Ring_Morphism inject_Z. 

Instance: Injective inject_Z.
Proof. intros x y. change (x * 1 == y * 1 -> x == y). do 2 rewrite mult_1_r. intuition. Qed.

Instance ding: Surjective (fun p => inject_Z (fst p) * / inject_Z (snd p)).
Proof. unfold dec_mult_inv. intros [num den]. exists (num, Zpos den). rewrite Qmake_Qdiv. reflexivity. Qed.

Instance Qrat: Rationals Q.
Proof. apply (alt_Build_Rationals _ _ inject_Z); apply _. Qed.
