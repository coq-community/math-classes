Set Automatic Introduction.

Require CatStuff UniversalAlgebra.
Require Import Structures RingOps BoringInstances Morphisms Numbers.
Import UniversalAlgebra.notations.

Close Scope nat_scope.

Module for_another_semiring.
Section contents.

  Variable (R: semiring.Object).

  Let R_sr := semiring.Variety_as_SemiRing R.

  Add Ring R: (SemiRing_semi_ring_theory R).

  Fixpoint f (n: nat): R := match n with 0%nat => 0 | S n' => f n' + 1 end.

  Instance f_proper: Proper (equiv ==> equiv) f.
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

  Let f_preserves_plus a a': f (a + a') == f a + f a'.
  Proof with try ring. induction a; simpl; intros... rewrite IHa... Qed.

  Let f_preserves_mult a a': f (a * a') == f a * f a'.
  Proof with try ring. induction a; simpl; intros... rewrite f_preserves_plus, IHa... Qed.

  Instance: @UA.HomoMorphism semiring.sig nat _ R _ semiring.impl_from_instance _ f.
  Proof with reflexivity.
   constructor. apply _.
   destruct o; repeat intro.
      apply f_preserves_plus...
     apply f_preserves_mult...
    simpl...
   change (f 1 == 1). simpl. ring.
  Qed.

  Definition arrow: semiring.Arrow (semiring.as_object nat) R := exist (UA.HomoMorphism semiring.sig) f _.

  Lemma arrow_unique arrow': arrow == arrow'.
  Proof with reflexivity.
   intro.
   unfold semiring.Arrow in arrow'.
   destruct arrow'. unfold arrow. simpl in *.
   set (@semiring.impl_from_instance nat _ _ _ _).
   pose proof (hmok x _ _).
   induction a.
    change (0 == x 0). symmetry.
    apply preserves_0.
   change (f a + 1 == x (1 + a)).
   rewrite preserves_plus, preserves_1, IHa.
   ring.
  Qed.

End contents.
End for_another_semiring.

Definition nat_initial: @CatStuff.initial _ semiring.Arrow _ (semiring.as_object nat) :=
  fun y => exist _ _ (for_another_semiring.arrow_unique y).

Global Instance nat_Naturals: Naturals nat.
  exact (@Build_Naturals nat _ _ _ _ _ _ nat_initial _).
Defined. (* can't make this opaque because of nonsense below. todo: look into this *)

Lemma Naturals_ordinary_ind `{Naturals N}
  (P: N -> Prop) `{!Proper (equiv ==> iff)%signature P}:
  P 0 -> (forall n, P n -> P (1 + n)) -> forall n, P n.
Proof with auto.
 intros.
 rewrite <- (iso_nats nat n).
 change (P (naturals_to_semiring N (naturals_to_semiring nat n))).
 pose proof (naturals_to_semiring_mor nat N).
 induction (naturals_to_semiring nat n).
  change (P (naturals_to_semiring N (0:nat))).
  rewrite preserves_0...
 change (P (naturals_to_semiring N (1 + n0))).
 rewrite preserves_plus, preserves_1...
Qed.

Lemma Mult_mult_reg_l: forall n m p: nat, ~ p = 0 -> mult p n = mult p m -> n = m.
Proof. (* simple omission in the stdlib *)
 destruct p. intuition.
 intros. apply Le.le_antisym; apply Mult.mult_S_le_reg_l with p; rewrite H0; constructor.
Qed.

Section borrowed_from_nat.

  Context `{Naturals A} (x y z: A).

  Let w v := match v with 0%nat => x | 1%nat => y | _ => z end.
  Let d := semiring.impl_from_instance.

  Lemma from_nat_stmt (s: UA.Statement semiring.sig):
    (forall v : nat -> nat, @UniversalAlgebra.eval_stmt semiring.sig nat _ semiring.impl_from_instance v s) ->
    (@UniversalAlgebra.eval_stmt semiring.sig A _ semiring.impl_from_instance w s).
  Proof.
   pose proof (@naturals_initial A _ _ _ _ _ _).
   pose proof (@naturals_initial nat _ _ _ _ _ _).
   destruct (@CatStuff.initials_unique semiring.Object semiring.Arrow _ _ _ _ _ (semiring.as_object A) (semiring.as_object nat) X X0).
   destruct X. destruct X0. simpl in *.
   clear e0 e1.
   destruct x0. destruct x1.
   simpl in *.
   intros.
   exact (@UA.carry_stmt semiring.sig nat A _ _ _ _ semiring.impl_from_instance semiring.impl_from_instance _ _ x1 x0 _ _ H0 H1 s H2 w).
  Qed.

  Local Notation x' := (UA.Var _ 0).
  Local Notation y' := (UA.Var _ 1).
  Local Notation z' := (UA.Var _ 2).

  (* Some clever autoquoting tactic might make what follows even more automatic. *)
  (* The ugly [pose proof ... . apply that_thing.]'s are because of Coq bug 2185. *)

  Lemma naturals_plus_reg_l: x + y == x + z -> y == z.
  Proof.
   pose proof (from_nat_stmt (x' + y' === x' + z' -=> y' === z')).
   apply H0. intro. simpl. apply Plus.plus_reg_l.
  Qed.

  Lemma naturals_mult_reg_l: ~ x == 0 -> x * y == x * z -> y == z.
  Proof.
   pose proof (from_nat_stmt ((x' === 0 -=> UA.Ext _ False) -=> x' * y' === x' * z' -=> y' === z')).
   apply H0. intro. simpl. apply Mult_mult_reg_l.
  Qed.

  Lemma naturals_0_neq_1': ~ 0 == 1.
  Proof.
   pose proof (from_nat_stmt (0 === 1 -=> UA.Ext _ False)).
   apply H0. discriminate.
  Qed.

End borrowed_from_nat.
