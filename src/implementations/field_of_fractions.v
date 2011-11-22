Require Import 
  Ring abstract_algebra 
  theory.rings theory.dec_fields.

Inductive Frac R `{Rap : Equiv R} `{Rzero : Zero R} : Type := frac { num: R; den: R; den_ne_0: den ≠ 0 }.
  (* We used to have [den] and [den_nonzero] bundled, which did work relatively nicely with Program, but the
   extra messyness in proofs etc turned out not to be worth it. *)
Implicit Arguments frac [[R] [Rap] [Rzero]].
Implicit Arguments num [[R] [Rap] [Rzero]].
Implicit Arguments den [[R] [Rap] [Rzero]].
Implicit Arguments den_ne_0 [[R] [Rap] [Rzero]].

Section contents.
Context `{IntegralDomain R} `{∀ x y, Decision (x = y)}.

Add Ring R: (stdlib_ring_theory R).

Global Instance Frac_equiv : Equiv (Frac R) | 0 := λ x y, num x * den y = num y * den x.

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

Global Instance Frac_dec : ∀ x y: Frac R, Decision (x = y)
  := λ x y, decide_rel (=) (num x * den y) (num y * den x).

(* injection from R *)
Global Program Instance Frac_inject: Cast R (Frac R) := λ r, frac r 1 _.
Next Obligation. exact (is_ne_0 1). Qed.

Instance: Proper ((=) ==> (=)) Frac_inject.
Proof. intros x1 x2 E. unfold equiv, Frac_equiv. simpl. now rewrite E. Qed.

(* Relations, operations and constants *)
Global Program Instance Frac_plus: Plus (Frac R) :=
  λ x y, frac (num x * den y + num y * den x) (den x * den y) _.
Next Obligation. destruct x, y. simpl. now apply mult_ne_0. Qed.

Global Instance Frac_0: Zero (Frac R) := ('0 : Frac R).
Global Instance Frac_1: One (Frac R) := ('1 : Frac R).

Global Instance Frac_negate: Negate (Frac R) := λ x, frac (- num x) (den x) (den_ne_0 x).

Global Program Instance Frac_mult: Mult (Frac R) := λ x y, frac (num x * num y) (den x * den y) _.
Next Obligation. destruct x, y. simpl. now apply mult_ne_0. Qed.

Ltac unfolds := unfold Frac_negate, Frac_plus, equiv, Frac_equiv in *; simpl in *.
Ltac ring_on_ring := repeat intro; unfolds; try ring.

Lemma Frac_nonzero_num x : x ≠ 0 ↔ num x ≠ 0.
Proof.
  split; intros E F; apply E; unfolds.
   rewrite F. ring.
  rewrite right_identity in F.
  rewrite F. apply left_absorb.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) Frac_plus.
Proof with try ring.
  intros x x' E y y' E'. unfolds.
  transitivity (num x * den x' * den y * den y' + num y * den y' * den x * den x')...
  rewrite E, E'...
Qed.

Instance: Proper ((=) ==> (=)) Frac_negate.
Proof.
  intros x y E. unfolds.
  rewrite <-negate_mult_distr_l, E. ring.
Qed.

Instance: Proper ((=) ==> (=) ==> (=)) Frac_mult.
Proof with try ring.
  intros x y E x0 y0 E'. unfolds.
  transitivity (num x * den y * (num x0 * den y0))...
  rewrite E, E'...
Qed.

Global Instance: Ring (Frac R).
Proof. repeat (split; try apply _); ring_on_ring. Qed.

Global Instance Frac_dec_recip: DecRecip (Frac R) := λ x,
  match decide_rel (=) (num x) 0 with
  | left _ => 0
  | right P => frac (den x) (num x) P
  end.

Instance: Setoid_Morphism Frac_dec_recip.
Proof.
  split; try apply _.
  intros [xn xd Px] [yn yd Py]. unfolds. unfold Frac_dec_recip. simpl.
  case (decide_rel (=) xn 0); case (decide_rel (=) yn 0); intros Ey Ex; simpl.
     reflexivity.
    rewrite Ex. intros E. destruct Ey.
    apply (right_cancellation_ne_0 (.*.) xd); trivial.
    rewrite <-E. ring.
   rewrite Ey. intros E. destruct Ex.
   apply (right_cancellation_ne_0 (.*.) yd); trivial.
   rewrite E. ring.
  symmetry.
  now rewrite (commutativity yd), (commutativity xd).
Qed.

Global Instance: DecField (Frac R).
Proof.
  constructor; try apply _.
    red. unfolds.
    rewrite 2!mult_1_r.
    apply (is_ne_0 1).
   unfold dec_recip, Frac_dec_recip.
   case (decide_rel _); simpl; intuition.
  intros [xn xs] Ex.
  unfold dec_recip, Frac_dec_recip.
  case (decide_rel _); simpl.
   intros E. destruct Ex. unfolds. rewrite E. ring.
  intros. ring_on_ring.
Qed.

Lemma Frac_dec_mult_num_den x :
  x = 'num x / 'den x.
Proof.
  unfold dec_recip, Frac_dec_recip.
  case (decide_rel _); simpl; intros E.
   now destruct (den_ne_0 x).
  unfolds. ring.
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

Typeclasses Opaque Frac_equiv.

Section morphisms.
Context `{IntegralDomain R1} `{∀ x y : R1, Decision (x = y)}.
Context `{IntegralDomain R2} `{∀ x y : R2, Decision (x = y)}.
Context `(f : R1 → R2) `{!SemiRing_Morphism f} `{!Injective f}.

Program Definition Frac_lift (x : Frac R1) : Frac R2 := frac (f (num x)) (f (den x)) _.
Next Obligation.
  apply injective_ne_0.
  now apply (den_ne_0 x).
Qed.

Instance: Proper ((=) ==> (=)) Frac_lift.
Proof.
  intros x y E.
  unfold equiv, Frac_equiv, Frac_lift in *. simpl.
  now rewrite <-2!preserves_mult, E.
Qed.

Global Instance: SemiRing_Morphism Frac_lift.
Proof.
  pose proof (_:Ring (Frac R1)).
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
