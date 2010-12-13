Require theory.fields.
Require Import Morphisms Ring abstract_algebra theory.rings.

Section contents.

Context R
  `{IntegralDomain R}
  `{∀ x y, Decision (x = y)}. (* needed to get cancellation law in transitivity proof and for the decider for Frac *)

Add Ring R: (stdlib_ring_theory R).

Inductive Frac: Type := frac { num: R; den: R; den_nonzero: den ≠ 0 }.
  (* We used to have den and den_nonzero bundled, which did work relatively nicely with Program, but the
   extra messyness in proofs etc turned out not to be worth it. *)

Global Program Instance frac_equiv: Equiv Frac := λ x y, num x * den y = num y * den x.

Instance: Setoid Frac.
Proof with auto.
  split; red; unfold equiv, frac_equiv.
    reflexivity.
   intros x y E. symmetry...
  intros [nx dx] [ny dy] [nz dz] V W. simpl in *.
  apply (left_cancellation_ne_zero ring_mult dy)...
  do 2 rewrite associativity. 
  do 2 rewrite (commutativity dy).
  rewrite V, <- W. ring.
Qed.

Global Instance: ∀ x y: Frac, Decision (x = y) := λ x y, decide (num x * den y = num y * den x).

(* injection from R *)
Program Definition inject (r: R): Frac := frac r 1 _.
Next Obligation. intro E. apply (ne_zero 1). assumption. Qed.

Instance: Proper ((=) ==> (=)) inject.
Proof. unfold inject, equiv, frac_equiv. intros x x' E. simpl. rewrite E. reflexivity. Qed.

(* Relations, operations and constants *)
Global Program Instance frac_plus: RingPlus Frac :=
  λ x y, frac (num x * den y + num y * den x) (den x * den y) _.
Next Obligation. destruct x, y. simpl. apply mult_ne_zero; assumption. Qed.

Global Instance frac_zero: RingZero Frac := inject 0.
Global Instance frac_one: RingOne Frac := inject 1.

Global Instance frac_opp: GroupInv Frac := λ x, frac (- num x) (den x) (den_nonzero x).

Global Program Instance frac_mult: RingMult Frac := λ x y, frac (num x * num y) (den x * den y) _.
Next Obligation. destruct x, y. simpl. apply mult_ne_zero; assumption. Qed.

Ltac unfolds := unfold frac_opp, frac_plus, equiv, frac_equiv in *; simpl in *.
Ltac ring_on_int := repeat intro; unfolds; try ring.

Lemma nonzero_num x : x ≠ 0 ↔ num x ≠ 0.
Proof.
  split; intros E F; apply E; unfolds.
   rewrite F. ring.
  rewrite right_identity in F.
  rewrite F. apply left_absorb.
Qed.

Global Program Instance frac_inv: MultInv Frac := λ x, frac (den x) (num x) _.
Next Obligation.  apply nonzero_num. assumption. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) frac_plus.
Proof with try ring.
  intros x x' E y y' E'. unfolds.
  transitivity (num x * den x' * den y * den y' + num y * den y' * den x * den x')...
  rewrite E, E'...
Qed.

Instance: Proper ((=) ==> (=)) frac_opp.
Proof. 
  intros x y E. unfolds. 
  rewrite <-ring_distr_opp_mult, E. ring. 
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) frac_mult.
Proof with try ring.
  intros x y E x0 y0 E'. unfolds.
  transitivity (num x * den y * (num x0 * den y0))...
  rewrite E, E'...
Qed.

Instance: Ring Frac.
Proof. repeat (split; try apply _); ring_on_int. Qed.

Instance: Proper ((=) ==> (=)) frac_inv.
Proof.
  intros [x N] [x' N'] E. unfolds.
  symmetry.
  rewrite (commutativity (den x')), (commutativity (den x)).
  assumption.
Qed.

Global Instance: Field Frac.
Proof.
  constructor; try apply _.
   unfold NeZero. unfolds.
   do 2 rewrite mult_1_r.
   apply (ne_zero 1).
  intros [x Ex]. ring_on_int.
Qed.

(* A final word about inject *)
Global Instance: Ring_Morphism inject.
Proof.
  repeat (constructor; try apply _); try reflexivity.
    intros x y. change ((x + y) * (1 * 1) = (x * 1 + y * 1) * 1). ring.
   intros x. unfolds. reflexivity.
  intros x y. change ((x * y) * (1 * 1) = x * y * 1). ring.
Qed.

Global Instance: Injective inject.
Proof. 
  repeat (constructor; try apply _).
  intros x y. unfolds. do 2 rewrite mult_1_r. intuition.
Qed.

Let inject_frac := (λ p, inject (fst p) * / inject (snd p)).

Global Instance: Inverse inject_frac := λ x, (num x, den x).

Global Instance: Surjective inject_frac.
Proof with auto. 
  repeat (constructor; try apply _).
   intros [n d P] y E.
   rewrite <- E.
   unfold equiv, frac_equiv, inject_frac, inject, dec_mult_inv in E |- *. simpl in *.
   case (decide _); intros E2; simpl in *.
    destruct P. unfolds.
    ring_simplify in E2...
   ring.
  intros ?? E.
  unfold inject_frac.
  rewrite E. reflexivity.
Qed.

End contents.
