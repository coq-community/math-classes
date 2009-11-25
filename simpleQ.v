Require Import
  Morphisms Ring
  simpleZ RingOps Naturals AbstractProperties Structures
  AbstractRationals Structures IntegerTheory FieldOps.

Section contents.

Context Z `{Zth: Integers Z} `{forall x y: Z, Decision (x == y)} `{forall x y: Z, Decision (x <= y)}.

Add Ring Ding: (Ring_ring_theory Z).

Inductive Q: Type := C { num: Z; den: Z; den_nonzero: ~ den == 0 }.
  (* We used to have den and den_nonzero bundled, which did work relatively nicely with Program, but the
   extra messyness in proofs etc turned out not to be worth it. *)

(* equality *)

Program Instance q_equiv: Equiv Q := fun x y => num x * den y == num y * den x.

Instance: Reflexive q_equiv. Proof. repeat intro. unfold q_equiv. reflexivity. Qed.
Instance: Symmetric q_equiv. Proof. repeat intro. unfold q_equiv. symmetry. assumption. Qed.
Instance: Transitive q_equiv.
Proof with auto.
 unfold q_equiv. intros x y z V W.
 destruct x. destruct y. destruct z.
 simpl in *.
 apply (int_mult_injective den1)...
 do 2 rewrite associativity.
 do 2 rewrite (commutativity den1).
 rewrite V, <- W. ring.
Qed.

Instance: Equivalence q_equiv.

Instance: forall x y: Q, Decision (x == y)
  := fun x y => decide (num x * den y == num y * den x).

(* injection from Z *)

Program Definition inject_Z (z: Z): Q := C z 1 _.
Next Obligation. symmetry in H2. apply (zero_ne_one H2). Qed.

Instance: Proper (equiv ==> equiv) inject_Z.
Proof. unfold inject_Z, equiv, q_equiv. intros x x' E. simpl. rewrite E. reflexivity. Qed.

(* relations/operations/constants: *)

Program Instance q_plus: RingPlus Q := fun (x y: Q) => C (num x * den y + num y * den x) (den x * den y) _.
Next Obligation.
 destruct x. destruct y. simpl in H2.
 revert den_nonzero0 den_nonzero1 H2. simpl.
 intros. destruct (zero_product _ _ H2); intuition.
Qed.

Instance q_zero: RingZero Q := inject_Z 0.
Instance q_ring_one: RingOne Q := inject_Z 1.

Instance q_opp: GroupInv Q := fun (x: Q) => C (- num x) (den x) (den_nonzero x).

Program Instance q_mult: RingMult Q := fun x y => C (num x * num y) (den x * den y) _.
Next Obligation.
 destruct x. destruct y. simpl in H2.
 revert den_nonzero0 den_nonzero1 H2. simpl. 
 intros. destruct (zero_product _ _ H2); intuition.
Qed.

Program Instance q_inv: MultInv Q := fun x => C (den x) (num x) _.
Next Obligation. unfold equiv, q_equiv in H3. apply H3. rewrite H2. simpl. ring. Qed.

(* plus is nice: *)

Ltac ring_on_int := repeat intro; unfold q_opp, q_plus, equiv, q_equiv; simpl; ring.

Instance: Associative q_plus. Proof. ring_on_int. Qed.
Instance: Commutative q_plus. Proof. ring_on_int. Qed.

Instance: Proper (q_equiv ==> q_equiv ==> q_equiv) q_plus.
Proof.
 unfold q_equiv, q_plus. intros x x' E y y' E'. simpl.
 transitivity (num x * den x' * den y * den y' + num y * den y' * den x * den x'); [ring|].
 rewrite E, E'. ring.
Qed.

Instance: SemiGroup Q (op:=q_plus).

Instance: Monoid Q (op:=q_plus) (unit:=q_zero).
Proof. constructor; try apply _; ring_on_int. Qed.

(* opp is nice: *)

Instance: Proper (q_equiv ==> q_equiv) q_opp.
Proof. unfold q_equiv, q_opp. intros x y E. simpl. rewrite <- ring_distr_opp_mult, E. ring. Qed.

Instance: @Group _ q_equiv q_plus q_zero q_opp.
Proof. constructor; try apply _; ring_on_int. Qed.

Instance: AbGroup Q (op:=q_plus) (unit:=q_zero).

(* mult is nice: *)

Instance: Proper (q_equiv ==> q_equiv ==> q_equiv) q_mult.
Proof with try ring.
 unfold q_equiv. intros x y E x0 y0 E'. simpl.
 transitivity (num x * den y * (num x0 * den y0))...
 rewrite E, E'...
Qed.

Instance: Associative q_mult. Proof. ring_on_int. Qed.
Instance: Commutative q_mult. Proof. ring_on_int. Qed.
Instance: Distribute q_mult q_plus. Proof. constructor; ring_on_int. Qed.

Instance: SemiGroup Q (op:=q_mult).

Instance: Monoid Q (op:=q_mult) (unit:=q_ring_one).
Proof. constructor; try apply _; ring_on_int. Qed.

Instance: Ring Q.

Instance: Ring_Morphism inject_Z.
Proof.
 repeat (constructor; try apply _); unfold equiv, q_equiv; try reflexivity; simpl; intros.
  change ((a + a') * (1 * 1) == (a * 1 + a' * 1) * 1). ring.
 change ((a * a') * (1 * 1) == a * a' * 1). ring.
Qed.

Instance: Injective inject_Z.
Proof. intros x y. unfold equiv, q_equiv. simpl. do 2 rewrite mult_1_r. intuition. Qed.

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

Instance: Field Q.
Proof.
 constructor; try apply _.
  unfold ZeroNeOne, equiv, q_equiv.
  simpl. do 2 rewrite mult_1_r.
  apply zero_ne_one.
 unfold mult_inv, q_inv, equiv, q_equiv. intro. simpl. ring.
Qed.

(* a final touch on inject_Z... *)

Instance: Surjective (fun p => inject_Z (fst p) * / inject_Z (snd p)).
Proof.
 intros [n d P]. exists (n, d).
 unfold equiv, q_equiv. simpl.
 ring_simplify.
 unfold FieldOps.dec_mult_inv. destruct decide.
  exfalso.
  apply P.
  unfold equiv in e0.
  simpl in e0.
  ring_simplify in e0.
  assumption.
 simpl. ring.
Qed.

(* and presto, we have rationals: *)

Global Instance simpleQ_rationals: Rationals Q.
Proof. apply (alt_Build_Rationals Q Z inject_Z); apply _. Qed.

End contents.

Let T := Q (Z nat).
Print Assumptions T.
