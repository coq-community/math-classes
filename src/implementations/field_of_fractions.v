Require theory.fields.
Require Import Morphisms Ring abstract_algebra theory.rings.

Section contents.

Context R
  `{IntegralDomain R}
  `{∀ x y, Stable (x = y)} (* needed to get cancellation law in transitivity proof *)
  `{∀ x y, Decision (x = y)}. (* only used in decider for Frac *)

Add Ring R: (stdlib_ring_theory R).

Inductive Frac: Type := frac { num: R; den: R; den_nonzero: den ≠ 0 }.
  (* We used to have den and den_nonzero bundled, which did work relatively nicely with Program, but the
   extra messyness in proofs etc turned out not to be worth it. *)

(* equality *)

Global Program Instance frac_equiv: Equiv Frac := λ x y, num x * den y = num y * den x.

Instance: Reflexive frac_equiv. Proof. repeat intro. unfold frac_equiv. reflexivity. Qed.
Instance: Symmetric frac_equiv. Proof. repeat intro. unfold frac_equiv. symmetry. assumption. Qed.
Instance: Transitive frac_equiv.
Proof with auto.
 unfold frac_equiv. intros [] [] [] V W.
 simpl in *.
 apply (left_cancellation_ne_zero ring_mult den1)...
 do 2 rewrite associativity.
 do 2 rewrite (commutativity den1).
 rewrite V, <- W. ring.
Qed.

Instance: Equivalence frac_equiv.
Instance: Setoid Frac.

Global Instance: ∀ x y: Frac, Decision (x = y) := λ x y, decide (num x * den y = num y * den x).

(* injection from R *)

Program Definition inject (r: R): Frac := frac r 1 _.
Next Obligation. intro E. apply (ne_zero 1). assumption. Qed.

Instance: Proper (equiv ==> equiv) inject.
Proof. unfold inject, equiv, frac_equiv. intros x x' E. simpl. rewrite E. reflexivity. Qed.

(* relations/operations/constants: *)

Global Program Instance frac_plus: RingPlus Frac :=
  λ x y, frac (num x * den y + num y * den x) (den x * den y) _.
Next Obligation. destruct x, y. simpl. apply mult_ne_zero; assumption. Qed.
  (* hm, this is no good, because now frac_plus refers to the proof :-( *)

Global Instance frac_zero: RingZero Frac := inject 0.
Global Instance frac_one: RingOne Frac := inject 1.

Global Instance frac_opp: GroupInv Frac := λ x, frac (- num x) (den x) (den_nonzero x).

Global Program Instance frac_mult: RingMult Frac := λ x y, frac (num x * num y) (den x * den y) _.
Next Obligation. destruct x, y. simpl. apply mult_ne_zero; assumption. Qed.

Global Program Instance frac_inv: MultInv Frac := λ x, frac (den x) (num x) _.
Next Obligation. intro U. unfold equiv, frac_equiv in H2. apply H2. rewrite U. simpl. ring. Qed.

(* plus is nice, giving us a monoid: *)

Ltac ring_on_int := repeat intro; unfold frac_opp, frac_plus, equiv, frac_equiv; simpl; ring.

Instance: Associative frac_plus. Proof. ring_on_int. Qed.
Instance: Commutative frac_plus. Proof. ring_on_int. Qed.

Instance: Proper (frac_equiv ==> frac_equiv ==> frac_equiv) frac_plus.
Proof.
 unfold frac_equiv, frac_plus. intros x x' E y y' E'. simpl.
 transitivity (num x * den x' * den y * den y' + num y * den y' * den x * den x'); [ring|].
 rewrite E, E'. ring.
Qed.

Instance: SemiGroup Frac (op:=frac_plus).

Instance: Monoid Frac (op:=frac_plus) (unit:=frac_zero).
Proof. constructor; try apply _; ring_on_int. Qed.

(* opp is nice, giving us an abelian group: *)

Instance: Proper (frac_equiv ==> frac_equiv) frac_opp.
Proof. unfold frac_equiv, frac_opp. intros x y E. simpl. rewrite <- ring_distr_opp_mult, E. ring. Qed.

Instance: @Group _ frac_equiv frac_plus frac_zero frac_opp.
Proof. constructor; try apply _; ring_on_int. Qed.

Instance: AbGroup Frac (op:=frac_plus) (unit:=frac_zero).

(* mult is nice, giving us a ring: *)

Instance: Proper (frac_equiv ==> frac_equiv ==> frac_equiv) frac_mult.
Proof with try ring.
 unfold frac_equiv. intros x y E x0 y0 E'. simpl.
 transitivity (num x * den y * (num x0 * den y0))...
 rewrite E, E'...
Qed.

Instance: Associative frac_mult. Proof. ring_on_int. Qed.
Instance: Commutative frac_mult. Proof. ring_on_int. Qed.
Instance: Distribute frac_mult frac_plus. Proof. constructor; ring_on_int. Qed.

Instance: SemiGroup Frac (op:=frac_mult).

Instance: Monoid Frac (op:=frac_mult) (unit:=frac_one).
Proof. constructor; try apply _; ring_on_int. Qed.

Instance: CommutativeMonoid Frac (op:=frac_mult) (unit:=frac_one).

Instance: Ring Frac.

(* inv is nice, giving us the field of fractions: *)

Instance: Proper (sig_relation frac_equiv _ ==> frac_equiv) frac_inv.
Proof.
 unfold frac_equiv, sig_relation.
 intros [x N] [x' N'] E.
 simpl in *.
 symmetry.
 rewrite (commutativity (den x')), (commutativity (den x)).
 assumption.
Qed.

Global Instance: Field Frac.
Proof.
 constructor; try apply _.
  unfold NeZero, equiv, frac_equiv.
  simpl. do 2 rewrite mult_1_r.
  apply (ne_zero 1).
 unfold mult_inv, frac_inv, equiv, frac_equiv. intro. simpl. ring.
Qed.

(* a final word about inject: *)

Global Instance: Ring_Morphism inject.
Proof.
 repeat (constructor; try apply _); unfold equiv, frac_equiv; try reflexivity; simpl; intros.
  change ((a + a') * (1 * 1) = (a * 1 + a' * 1) * 1). ring.
 change ((a * a') * (1 * 1) = a * a' * 1). ring.
Qed.

Global Instance: Injective inject.
Proof. constructor. intros x y. unfold equiv, frac_equiv. simpl. do 2 rewrite mult_1_r. intuition. constructor; apply _. Qed.

Let inject_frac := (λ p, inject (fst p) * / inject (snd p)).

Global Instance: Inverse inject_frac := λ x, (num x, den x).

Global Instance: Surjective inject_frac.
Proof.
 constructor.
  intros [n d P] y E.
  rewrite <- E.
  unfold Basics.compose, inject_frac, equiv, frac_equiv.
  simpl.
  ring_simplify.
  unfold dec_mult_inv. case (decide _).
   intros. exfalso. apply P.
   unfold equiv in e0. unfold frac_equiv in e0. simpl in e0.
   ring_simplify in e0.
   assumption.
  simpl. intros. ring.
 constructor; try apply _.
 intros ?? E.
 unfold inject_frac.
 rewrite E.
 reflexivity.
Qed.

End contents.
