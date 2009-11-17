Set Automatic Introduction.

Require CatStuff UniversalAlgebra Plus.
Require Import Structures RingOps BoringInstances Morphisms Numbers SemiRingAlgebra.
Import UniversalAlgebra.notations.

Close Scope nat_scope.

Instance f: NaturalsToSemiRing nat :=
  fun _ _ _ _ _ => fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Module for_another_semiring.
Section contents.

  Context `{SemiRing R}.

  Add Ring R: (SemiRing_semi_ring_theory R).

  Instance f_proper: Proper (equiv ==> equiv) (naturals_to_semiring nat R).
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

  Let f_preserves_0: naturals_to_semiring nat R 0 == 0.
   reflexivity.
  Qed.

  Let f_preserves_1: naturals_to_semiring nat R 1 == 1.
  Proof. unfold naturals_to_semiring. simpl. ring. Qed.

  Let f_preserves_plus a a': naturals_to_semiring nat R (a + a') == naturals_to_semiring nat R a + naturals_to_semiring nat R a'.
  Proof with try ring.
   induction a.
    change (naturals_to_semiring nat R (0 + a') == naturals_to_semiring nat R 0 + naturals_to_semiring nat R a').
    unfold naturals_to_semiring in *.
    rewrite plus_0_l.
    simpl.
    rewrite plus_0_l.
    reflexivity.
    (* this is awful, due to a Coq bug i've already reported on irc *)
   unfold naturals_to_semiring in *.
   simpl.
   rewrite IHa...
  Qed.

  Let f_preserves_mult a a': naturals_to_semiring nat R (a * a') == naturals_to_semiring nat R a * naturals_to_semiring nat R a'.
  Proof with try ring.
   unfold naturals_to_semiring.
   induction a. simpl...
   simpl.
   unfold ring_mult.
   simpl.
   rewrite f_preserves_plus.
   unfold naturals_to_semiring.
   change (f R mult0 plus0 one zero a' + f R mult0 plus0 one zero (a * a') ==
      (f R mult0 plus0 one zero a + 1) * (f R mult0 plus0 one zero a')).
   rewrite IHa...
  Qed.

  Instance f_mor: SemiRing_Morphism (naturals_to_semiring nat R).
   repeat (constructor; try apply _).
      apply f_preserves_plus.
     apply f_preserves_0.
    apply f_preserves_mult.
   apply f_preserves_1.
  Qed.

End contents.
End for_another_semiring.

Global Instance nat_Naturals: Naturals nat.
 apply (@Build_Naturals nat _ _ _ _ _ _ _ (@for_another_semiring.f_mor)).
 unfold CatStuff.proves_initial.
 destruct f'.
 simpl.
 intro.
 simpl.
 intro.
 destruct b.
 simpl in *.
 pose proof (semiring.from_object y).
 pose proof (@semiring.morphism_from_ua nat _ y _ semiring.impl_from_instance _ x _ _).
 pose proof (H0 H tt).
 induction a.
  unfold naturals_to_semiring.
  simpl.
  rewrite (@preserves_0 nat (y tt) _ _ _ _ _ _ _ _ _ _ (x tt) H1).
  reflexivity.
 unfold naturals_to_semiring.
 simpl.
 rewrite IHa.
 change (x tt a + 1 == x tt (1 + a)).
 rewrite (@preserves_plus nat (y tt) _ _ _ _ _ _ _ _ _ _ (x tt) H1).
 rewrite (@preserves_1 nat (y tt) _ _ _ _ _ _ _ _ _ _ (x tt) H1).
 rewrite commutativity.
 reflexivity.
Qed.

Lemma Naturals_ordinary_ind `{Naturals N}
  (P: N -> Prop) `{!Proper (equiv ==> iff)%signature P}:
  P 0 -> (forall n, P n -> P (1 + n)) -> forall n, P n.
Proof with auto.
 intros.
 rewrite <- (iso_nats N nat n).
 pose proof (naturals_to_semiring_mor nat N).
 induction (naturals_to_semiring N nat n).
  change (P (naturals_to_semiring nat N (0:nat))).
  rewrite preserves_0...
 change (P (naturals_to_semiring nat N (1 + n0))).
 rewrite preserves_plus, preserves_1...
Qed.

Lemma Mult_mult_reg_l: forall n m p: nat, ~ p = 0 -> mult p n = mult p m -> n = m.
Proof. (* simple omission in the stdlib *)
 destruct p. intuition.
 intros. apply Le.le_antisym; apply Mult.mult_S_le_reg_l with p; rewrite H0; constructor.
Qed.

Lemma Mult_nz_mult_nz (x y: nat): ~ y == 0 -> ~ x == 0 -> ~ y * x == 0.
Proof.
 intros A B C.
 destruct (Mult.mult_is_O y x C); intuition.
Qed.

Section borrowed_from_nat.

  Context `{Naturals A} (x y z: A).

  Let w (_: unit) v := match v with 0%nat => x | 1%nat => y | _ => z end.
  Let d := semiring.impl_from_instance.

  Lemma from_nat_stmt (s: UA.Statement semiring.sig):
    (forall v : unit -> nat -> nat, @UniversalAlgebra.eval_stmt semiring.sig (fun _ => nat) (fun _ => equiv) semiring.impl_from_instance v s) ->
    (@UniversalAlgebra.eval_stmt semiring.sig (fun _ => A) (fun _ => equiv) semiring.impl_from_instance w s).
  Proof.
   pose proof (@naturals_initial A _ _ _ _ _ _ _).
   pose proof (@naturals_initial nat _ _ _ _ _ _ _).
   destruct (@CatStuff.initials_unique' semiring.Object semiring.Arrow _ _ _ _ _ (semiring.as_object A) (semiring.as_object nat) _ _ H1 H2).
   pose proof (H3 tt). simpl in H5.
   pose proof (H4 tt). simpl in H6.
   clear H1 H2.
   intros.
   apply (@UA.carry_stmt semiring.sig (fun _ => nat) (fun _ => A) (fun _ => equiv) (fun _ => equiv) _ _ semiring.impl_from_instance semiring.impl_from_instance) with (fun u => match u with tt => naturals_to_semiring nat A end) (fun u => match u with tt => naturals_to_semiring A nat end); auto.
      apply _.
     apply _.
    set (naturals_to_semiring_arrow nat (semiring.as_object A)).
    apply (proj2_sig a).
   set (naturals_to_semiring_arrow A (semiring.as_object nat)).
   apply (proj2_sig a).
  Qed.

  Local Notation x' := (UA.Var semiring.sig 0 tt).
  Local Notation y' := (UA.Var semiring.sig 1 tt).
  Local Notation z' := (UA.Var semiring.sig 2%nat tt).

  (* Some clever autoquoting tactic might make what follows even more automatic. *)
  (* The ugly [pose proof ... . apply that_thing.]'s are because of Coq bug 2185. *)

  Lemma naturals_plus_reg_l: x + y == x + z -> y == z.
  Proof.
   pose proof (from_nat_stmt (x' + y' === x' + z' -=> y' === z')).
   apply H1. intro. simpl. apply Plus.plus_reg_l.
  Qed.

  Lemma naturals_mult_reg_l: ~ x == 0 -> x * y == x * z -> y == z.
  Proof.
   pose proof (from_nat_stmt ((x' === 0 -=> UA.Ext _ False) -=> x' * y' === x' * z' -=> y' === z')).
   apply H1. intro. simpl. apply Mult_mult_reg_l.
  Qed.

  Lemma naturals_0_neq_1': ~ 0 == 1.
  Proof.
   pose proof (from_nat_stmt (0 === 1 -=> UA.Ext _ False)).
   apply H1. discriminate.
  Qed.

  Lemma naturals_zero_sum: x + y == 0 -> x == 0 /\ y == 0.
  Proof.
   pose proof (from_nat_stmt (x' + y' === 0 -=> UA.Conj _ (x' === 0) (y' === 0))).
   apply H1. intro. simpl. apply Plus.plus_is_O.
  Qed.

  Lemma naturals_nz_mult_nz: ~ y == 0 -> ~ x == 0 -> ~ y * x == 0.
  Proof.
   pose proof (from_nat_stmt ((y' === 0 -=> UA.Ext _ False) -=>
     (x' === 0 -=> UA.Ext _ False) -=> (y' * x' === 0 -=> UA.Ext _ False))).
   unfold not. apply H1. intro. simpl. apply Mult_nz_mult_nz.
  Qed.

End borrowed_from_nat.

(* The instance below is given low priority because specific models will typically be able to
 provide a more efficient implementation. *)

Program Instance naturals_eq_dec `{Naturals N}: forall x y: N, Decision (x == y) | 10 :=
  match Peano_dec.eq_nat_dec (naturals_to_semiring _ nat x) (naturals_to_semiring _ nat y) with
  | left E => left _
  | right E => right _
  end.
 
Next Obligation.
 change (x == y).
 rewrite <- (iso_nats _ nat x), <- (iso_nats _ nat y).
 rewrite E. reflexivity.
Qed.

Next Obligation.
 apply E.
 change (naturals_to_semiring _ nat x == naturals_to_semiring _ nat y).
 apply (naturals_to_semiring_mor _ nat).
 assumption.
Qed.

Require Import Max.

Definition naturals_max `{Naturals N} (x y: N): N :=
  naturals_to_semiring _ _ (max (naturals_to_semiring _ _ x) (naturals_to_semiring _ _ y)).

Definition naturals_minus `{Naturals N} (x y: N): N :=
  naturals_to_semiring _ _ (minus (naturals_to_semiring _ _ x) (naturals_to_semiring _ _ y)).
