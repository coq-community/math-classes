Require Import
  Program Relation_Definitions nat_Naturals
  RingOps BoringInstances AbstractProperties Numbers
  Morphisms Ring Structures IntegerOrder stdZ_Integers simpleZ.

Section contents.

Context Z `{Zth: Integers Z} `{Nth: Naturals N}.

Add Ring Z: (Ring_ring_theory Z).
Add Ring N: (SemiRing_semi_ring_theory N).

Inductive Q: Type := C { num: Z; den: N; den_nonzero: ~ den == 0 }.
  (* We used to have den and den_nonzero bundled, which did work relatively nicely with Program, but the
   extra messyness in proofs etc turned out not to be worth it. *)

Let NtoZ := naturals_to_semiring N Z.
Coercion NtoZ: N >-> Z.

(* equality *)

Program Instance q_equiv: Equiv Q := fun x y => num x * den y == num y * den x.

Instance: Reflexive q_equiv. Proof. repeat intro. unfold q_equiv. reflexivity. Qed.
Instance: Symmetric q_equiv. Proof. repeat intro. unfold q_equiv. symmetry. assumption. Qed.
Instance: Transitive q_equiv.
Proof with auto.
 unfold q_equiv. repeat intro.
 destruct x. destruct y. destruct z.
 simpl in *.
 apply (stdZ_Integers.integers_mult_reg_l (naturals_to_semiring N Z den1))...
  intro.
  apply den_nonzero1.
  apply (naturals_to_integers_injective den1 0).
  rewrite preserves_0...
 do 2 rewrite associativity.
 do 2 rewrite (commutativity (naturals_to_semiring N Z den1)).
 subst NtoZ.
 rewrite H1, <- H2. ring.
Qed.

Instance: Equivalence q_equiv.

Instance: forall x y: Q, Decision (x == y) := fun x y => decide (num x * den y == num y * den x).

(* injection from Z *)

Program Definition inject_Z (z: Z): Q := C z 1 _.
Next Obligation. apply (naturals_0_neq_1' 0 0 0). symmetry. assumption. Qed.

Instance: Proper (equiv ==> equiv) inject_Z.
Proof.
 unfold inject_Z, equiv, q_equiv. intros x x' E. simpl.
 rewrite E. reflexivity.
Qed.

(* relations/operations/constants: *)

Program Instance q_plus: RingPlus Q := fun (x y: Q) => C (num x * den y + num y * den x) (den x * den y) _.
Next Obligation. Proof with auto.
 destruct x. destruct y. simpl in H1.
 apply (naturals_nz_mult_nz den1 den0)...
Qed.

Instance q_zero: RingZero Q := inject_Z 0.
Instance q_ring_one: RingOne Q := inject_Z 1.

Instance q_opp: GroupInv Q := fun (x: Q) => C (- num x) (den x) (den_nonzero x).

Program Instance q_mult: RingMult Q := fun x y => C (num x * num y) (den x * den y) _.
Next Obligation. Proof with auto.
 destruct x. destruct y. simpl in H1.
 apply (naturals_nz_mult_nz den1 den0)...
Qed.

Program Instance q_inv: MultInv Q := fun x => C (den x) (abs (num x)) _.
Next Obligation.
 unfold equiv, q_equiv in H1.
 apply H1. simpl. ring_simplify. assumption.
Qed.

Definition q_le: Order Q := fun x y: Q => int_le (num x * den y) (num y * den x).

(* plus is nice: *)

Instance: Associative q_plus.
Proof.
 repeat intro. unfold q_plus, equiv, q_equiv. simpl.
 rewrite (associativity (den x) (den y) (den z)). ring.
Qed.

Instance: Commutative q_plus.
Proof.
 repeat intro. unfold q_plus, equiv, q_equiv. simpl.
 rewrite (commutativity (den y)). ring.
Qed.

Instance: Proper (q_equiv ==> q_equiv ==> q_equiv) q_plus.
Proof.
 unfold q_equiv, q_plus. intros x x' E y y' E'. simpl.
 transitivity (num x * den x' * den y * den y' + num y * den y' * den x * den x'); [ring|].
 rewrite E, E'. ring.
Qed.

Instance: SemiGroup q_equiv q_plus.

Instance: Monoid q_equiv q_plus q_zero.
Proof. constructor; try apply _; unfold sg_op, q_plus, equiv, q_equiv; intro; simpl; ring. Qed.

(* opp is nice: *)

Instance: Proper (q_equiv ==> q_equiv) q_opp.
Proof.
 unfold q_equiv, q_opp. intros x y E. simpl.
 rewrite <- ring_distr_opp_mult, E. ring.
Qed.

Instance: Group q_equiv q_plus q_zero q_opp.
Proof. constructor; try apply _; unfold equiv, q_equiv, sg_op, q_plus, q_opp; intro x; simpl; ring. Qed.

Instance: AbGroup q_equiv q_plus q_zero q_opp.

(* mult is nice: *)

Instance: Proper (q_equiv ==> q_equiv ==> q_equiv) q_mult.
Proof with try ring.
 unfold q_equiv. intros x y E x0 y0 E'. simpl.
 transitivity (num x * den y * (num x0 * den y0))...
 rewrite E, E'...
Qed.

Instance: Associative q_mult.
Proof. repeat intro. unfold equiv, q_equiv. simpl. ring. Qed.

Instance: Commutative q_mult.
Proof. repeat intro. unfold equiv, q_equiv. simpl. ring. Qed.

Instance: Distribute q_mult q_plus.
Proof. constructor; repeat intro; unfold equiv, q_equiv; simpl; ring. Qed.

Instance: SemiGroup q_equiv q_mult.

Instance: Monoid q_equiv q_mult q_ring_one.
Proof. constructor; try apply _; unfold equiv, q_equiv; simpl; intro; ring. Qed.

Instance: Ring q_equiv q_plus q_mult q_opp q_zero q_ring_one.

Instance: Ring_Morphism inject_Z.
Proof.
 repeat (constructor; try apply _); unfold equiv, q_equiv; try reflexivity; simpl; intros.
  change ((a + a') * (1 * 1) == (a * 1 + a' * 1) * 1). ring.
 change ((a * a') * (1 * 1) == a * a' * 1). ring.
Qed.

(* inv is nice: *)

Instance: Proper (sig_relation q_equiv _ ==> q_equiv) q_inv.
Proof.
 unfold q_equiv, sig_relation.
 intros [x N] [x' N'] E.
 simpl in *.
 symmetry.
 rewrite (commutativity (den x')), (commutativity (den x)).
 assumption.
Qed.

Instance: Field q_equiv q_plus q_mult q_opp q_zero q_ring_one q_inv.
Proof.
 constructor; try apply _.
  unfold equiv, q_equiv.
  simpl.
  do 2 rewrite mult_1_r.
  apply integers_0_neq_1.
 unfold mult_inv, q_inv, equiv, q_equiv.
 intros [x N]. simpl. ring.
Qed.

(* le is nice: *)

Instance: Proper (q_equiv ==> q_equiv ==> iff) q_le.
Proof.
 unfold q_le. intros x x' E y y' E'.
 unfold q_equiv in *.
 split; intro.
  

Admitted.

Instance: Reflexive q_le.
Proof. intro x. unfold q_le. apply reflexivity. Qed.

Instance: Transitive q_le.
Proof.
 unfold q_le.
 assert (PartialOrder int_le). apply _. revert H0.
 assert (Proper (equiv ==> equiv ==> iff) int_le).
  apply _.
  revert H0.
 pose proof int_le_mult_compat_inv_l. revert H0.
 generalize int_le.
 intros r M N O.
 intros x y z xy yz.
 cut (r (num x * den z * (den y * den y)) (num z * den x * (den y * den y))).
  intro.
  apply (M (num x * den z) (num z * den x) (den y * den y)).
   admit.
  assumption.
 transitivity (num x * den y * (den z * den y)).
  ring_simplify.
  reflexivity.
 
 
 assert (num x * den y * (den z * den y) == num y * den x * (den z * den y)).
  rewrite xy.
  ring.
 rewrite H0.

 transitivity (num x * den y * (den z * den y)).
  ring_simplify.
  

 transitivity (num y * den x * den z * den y).
  
  

  admit. (* uses xy *)
 transitivity (num z * den y * den x * den y).
  admit. (* uses yz *)  
 ring_simplify.


Admitted.

Instance: PartialOrder q_le.
Proof.
 constructor. apply _.
  constructor; apply _.
 intros x x'.
 unfold relation_conjunction.
 unfold predicate_intersection.
 unfold pointwise_extension.
 split; intro E.
  rewrite E.
  intuition.
 unfold q_le in E.
 unfold q_equiv.
 destruct E.
 unfold flip in H1.
 apply (@partial_order_equivalence Z _ int_le _ (num x * den x') (num x' * den x)).
 split; assumption.
Qed.

Lemma q_le_0_mult (x: Q): q_le q_zero x -> forall y: Q, q_le 0 y -> q_le 0 (x * y).
Proof.
 unfold q_le.
 assert (Proper (equiv ==> equiv ==> iff) int_le).
  apply _.
 revert H0.
 pose proof int_le_0_mult.
 revert H0.
 generalize int_le.
 intros.
 simpl in *. 
 ring_simplify in H2. ring_simplify in H3. ring_simplify.
 apply H0; assumption.
Qed. (* proof ugly because normal rewriting horribly inefficient. asked mattam about it on irc. *)

Lemma q_le_compat_r (x y: Q): q_le x y -> forall z, q_le (x + z) (y + z).
Proof.
 unfold q_le.
 assert (Proper (equiv ==> equiv ==> iff) int_le).
  apply _.
 revert H0.
 assert (PartialOrder int_le).
  apply _.
 revert H0.
 pose proof int_le_0_sqr.
 revert H0.
 pose proof int_le_plus_compat_l.
 revert H0.
 pose proof int_le_mult_compat_l.
 revert H0.
 generalize int_le.
 simpl.
 intros.
 ring_simplify.
 apply H1.
 transitivity (num x * den y * (den z * den z)).
  ring_simplify.
  reflexivity.
 transitivity (den x * num y * (den z * den z)).
  apply H0. 
   rewrite (commutativity (den x)). 
   assumption.
  apply H2.
 ring_simplify. 
 reflexivity.
Qed.
  (* again, horrible because of rewrite problems *)

Instance: OrdField q_equiv q_plus q_mult q_opp q_zero q_ring_one q_inv q_le :=
  { leq_plus := q_le_compat_r; leq_zero_mult := q_le_0_mult }.

(* Q is a model of the rationals: *)

Instance Q_rationals: @Rationals Q _ _ _ _ _ _ _ q_le.
Proof.
 apply (@Build_Rationals Q _ _ _ _ _ _ _ q_le _ _).
 intros.
 exists (integers_to_ring Z B (num a)).
 exists (integers_to_ring Z B (den a)).
 subst t.
 rewrite (@ints_through_third Z _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ Q _ _ _ _ _ _ _).
 rewrite (@ints_through_third Z _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ Q _ _ _ _ _ _ _).
  (* hm, shouldn't be necessary to do this so uglily *)
 rewrite <- (integers_to_ring_unique Q inject_Z _ (num a)).
 rewrite <- (integers_to_ring_unique Q inject_Z _ (den a)).
 unfold inject_Z, equiv, q_equiv. simpl.
 unfold FieldOps.dec_mult_inv.
 destruct_call decide.
  unfold equiv, q_equiv in e1.
  simpl in e1. 
  exfalso.
  destruct a.
  simpl in e1.
  ring_simplify in e1.
  intuition.
 simpl. ring.
Qed.

Print Assumptions Q_rationals.
