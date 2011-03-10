Require theory.fields.
Require Import Morphisms Ring abstract_algebra theory.rings.

Inductive Frac R `{e : Equiv R} `{zero : RingZero R} : Type := frac { num: R; den: R; den_nonzero: den ≠ 0 }.
  (* We used to have [den] and [den_nonzero] bundled, which did work relatively nicely with Program, but the
   extra messyness in proofs etc turned out not to be worth it. *)
Implicit Arguments frac [[R] [e] [zero]].
Implicit Arguments num [[R] [e] [zero]].
Implicit Arguments den [[R] [e] [zero]].
Implicit Arguments den_nonzero [[R] [e] [zero]].

Section contents.
Context `{IntegralDomain R}.
Context `{∀ z : R, PropHolds (z ≠ 0) → LeftCancellation (.*.) z}.

Add Ring R: (stdlib_ring_theory R).

Global Instance Frac_equiv: Equiv (Frac R) := λ x y, num x * den y = num y * den x.

Instance: Setoid (Frac R).
Proof with auto.
  split; red; unfold equiv, Frac_equiv.
    reflexivity.
   intros x y E. now symmetry.
  intros [nx dx] [ny dy] [nz dz] V W. simpl in *.
  apply (left_cancellation_ne_0 (.*.) dy)...
  rewrite 2!associativity. 
  rewrite 2!(commutativity dy).
  rewrite V, <- W. ring.
Qed.

Global Instance Frac_dec `{∀ x y, Decision (x = y)} : ∀ x y: Frac R, Decision (x = y) 
  := λ x y, decide_rel (=) (num x * den y) (num y * den x).

(* injection from R *)
Global Program Instance Frac_inject: Coerce R (Frac R) := λ r, frac r 1 _.
Next Obligation. exact (ne_0 1). Qed.

Instance: Proper ((=) ==> (=)) Frac_inject.
Proof. intros x1 x2 E. unfold equiv, Frac_equiv. simpl. now rewrite E. Qed.

(* Relations, operations and constants *)
Global Program Instance Frac_plus: RingPlus (Frac R) :=
  λ x y, frac (num x * den y + num y * den x) (den x * den y) _.
Next Obligation. destruct x, y. simpl. now apply mult_ne_zero. Qed.

Global Instance Frac_0: RingZero (Frac R) := ('0 : Frac R).
Global Instance Frac_1: RingOne (Frac R) := ('1 : Frac R).

Global Instance Frac_opp: GroupInv (Frac R) := λ x, frac (- num x) (den x) (den_nonzero x).

Global Program Instance Frac_mult: RingMult (Frac R) := λ x y, frac (num x * num y) (den x * den y) _.
Next Obligation. destruct x, y. simpl. apply mult_ne_zero; assumption. Qed.

Ltac unfolds := unfold Frac_opp, Frac_plus, equiv, Frac_equiv in *; simpl in *.
Ltac ring_on_ring := repeat intro; unfolds; try ring.

Lemma Frac_nonzero_num x : x ≠ 0 ↔ num x ≠ 0.
Proof.
  split; intros E F; apply E; unfolds.
   rewrite F. ring.
  rewrite right_identity in F.
  rewrite F. apply left_absorb.
Qed.

Global Program Instance Frac_mult_inv: MultInv (Frac R) := λ x, frac (den x) (num x) _.
Next Obligation. apply Frac_nonzero_num. now destruct x. Qed.

Instance: Proper ((=) ==> (=) ==> (=)) Frac_plus.
Proof with try ring.
  intros x x' E y y' E'. unfolds.
  transitivity (num x * den x' * den y * den y' + num y * den y' * den x * den x')...
  rewrite E, E'...
Qed.

Instance: Proper ((=) ==> (=)) Frac_opp.
Proof. 
  intros x y E. unfolds. 
  rewrite <-opp_mult_distr_l, E. ring. 
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) Frac_mult.
Proof with try ring.
  intros x y E x0 y0 E'. unfolds.
  transitivity (num x * den y * (num x0 * den y0))...
  rewrite E, E'...
Qed.

Instance: Ring (Frac R).
Proof. repeat (split; try apply _); ring_on_ring. Qed.

Instance: Proper ((=) ==> (=)) Frac_mult_inv.
Proof.
  intros [x N] [x' N'] E. unfolds.
  symmetry.
  now rewrite (commutativity (den x')), (commutativity (den x)).
Qed.

Definition Frac_field: Field (Frac R).
Proof.
  constructor; try apply _.
   red. unfolds.
   rewrite 2!mult_1_r.
   apply (ne_0 1).
  intros [x Ex]. ring_on_ring.
Qed.

(* A final word about inject *)
Global Instance: SemiRing_Morphism Frac_inject.
Proof.
  repeat (constructor; try apply _); try reflexivity.
   intros x y. change ((x + y) * (1 * 1) = (x * 1 + y * 1) * 1). ring.
  intros x y. change ((x * y) * (1 * 1) = x * y * 1). ring.
Qed.

Global Instance: Injective Frac_inject.
Proof. 
  repeat (constructor; try apply _).
  intros x y. unfolds. rewrite 2!mult_1_r. intuition.
Qed.
End contents.

(* By declaring (Frac R) as a Field, instance resolution will go like: 
    LeftCancellation (.*.) z => Field (Frac R) => LeftCancellation (.*.) z => .. 
  so we have to make it a little less eager *)
Hint Extern 10 (Field (Frac _)) => apply @Frac_field : typeclass_instances. 
Typeclasses Opaque Frac_equiv.

Section morphisms.
Context `{IntegralDomain R1} `{∀ z : R1, PropHolds (z ≠ 0) → LeftCancellation (.*.) z}.
Context `{IntegralDomain R2} `{∀ z : R2, PropHolds (z ≠ 0) → LeftCancellation (.*.) z}.
Context `(f : R1 → R2) `{!SemiRing_Morphism f} `{!Injective f}.

Program Definition Frac_lift (x : Frac R1) : Frac R2 := frac (f (num x)) (f (den x)) _.
Next Obligation.
  apply injective_ne_0.
  apply den_nonzero.
Qed.

Instance: Proper ((=) ==>(=)) Frac_lift.
Proof.
  intros x y E.
  unfold equiv, Frac_equiv, Frac_lift in *. simpl.
  now rewrite <-2!preserves_mult, E.
Qed.

Global Instance: SemiRing_Morphism Frac_lift.
Proof.
  repeat (split; try apply _); unfold equiv, Frac_equiv, Frac_lift in *; simpl.
     intros x y. now rewrite preserves_plus, ?preserves_mult.
    now rewrite preserves_0, preserves_1.
   intros x y. now rewrite ?preserves_mult.
  now rewrite preserves_1.
Qed.

Global Instance: Injective Frac_lift.
Proof.
  split; try apply _.
  intros x  y E.
  unfold equiv, Frac_equiv, Frac_lift in *. simpl in *.
  apply (injective f). now rewrite 2!preserves_mult.
Qed.
End morphisms.
