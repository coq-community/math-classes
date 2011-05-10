Require
  theory.setoids.
Require Import
  Morphisms abstract_algebra.

Section group_props. 
Context `{Group G}.

Global Instance sg_op_mor_1: ∀ x, Setoid_Morphism (x &) | 0.
Proof. split; try apply _. Qed.

Global Instance sg_op_mor_2: ∀ x, Setoid_Morphism (& x) | 0.
Proof. split; try apply _. solve_proper. Qed.

Lemma inv_involutive x: - - x = x.
Proof.
  rewrite <-(left_identity x) at 2.
  rewrite <-(left_inverse (- x)).
  rewrite <-associativity.
  rewrite left_inverse.
  now rewrite right_identity.
Qed.

Global Instance: Injective (-).
Proof.
  constructor.
   intros x y E.
   now rewrite <-(inv_involutive x), <-(inv_involutive y), E.
  constructor; apply _.
Qed.

Lemma inv_0: - mon_unit = mon_unit.
Proof. rewrite <- (left_inverse mon_unit) at 2. rewrite right_identity. reflexivity. Qed.

Global Instance: ∀ z : G, LeftCancellation (&) z.
Proof.
  intros z x y E.
  rewrite <-(left_identity x), <-(left_inverse z), <-associativity.
  rewrite E.
  now rewrite associativity, left_inverse, left_identity.
Qed.  

Global Instance: ∀ z : G, RightCancellation (&) z.
Proof.
  intros z x y E.
  rewrite <-(right_identity x), <-(right_inverse z), associativity.
  rewrite E.
  now rewrite <-associativity, right_inverse, right_identity.
Qed.  

Lemma sg_inv_distr `{!AbGroup G} x y: - (x & y) = - x & - y.
Proof.
  rewrite <-(left_identity (- x & - y)).
  rewrite <-(left_inverse (x & y)).
  rewrite <-associativity.
  rewrite <-associativity.
  rewrite (commutativity (- x) (- y)).
  rewrite (associativity y).
  rewrite right_inverse.
  rewrite left_identity.
  rewrite right_inverse.
  now rewrite right_identity.
Qed.
End group_props.

Section groupmor_props. 
  Context `{Group A} `{Group B} {f : A → B} `{!Monoid_Morphism f}.

  Lemma preserves_inv x: f (- x) = - f x.
  Proof.
    apply (left_cancellation (&) (f x)).
    rewrite <-preserves_sg_op.
    rewrite 2!right_inverse.
    apply preserves_mon_unit.
  Qed.
End groupmor_props.

Instance semigroup_morphism_proper {A B eA eB opA opB} : 
  Proper ((=) ==> iff) (@SemiGroup_Morphism A B eA eB opA opB) | 1.
Proof.
  assert (∀ (f g : A → B), g = f → SemiGroup_Morphism f → SemiGroup_Morphism g) as P.
   intros f g E [? ? ? ?].
   split; try apply _.
    eapply setoids.morphism_proper; eauto.
   intros x y. now rewrite (E (x & y)), (E x), (E y).
  intros f g ?; split; intros Mor.
   apply P with f. destruct Mor. now symmetry. apply _.
  now apply P with g.
Qed.

Instance monoid_morphism_proper {A B eA eB opA uA opB uB} : 
  Proper ((=) ==> iff) (@Monoid_Morphism A B eA eB opA uA opB uB) | 1.
Proof.
  assert (∀ (f g : A → B), g = f → Monoid_Morphism f → Monoid_Morphism g) as P.
   intros f g E [? ? ? ?].
   split; try apply _.
    eapply semigroup_morphism_proper; eauto.
   now rewrite (E mon_unit mon_unit).
  intros f g ?; split; intros Mor.
   apply P with f. destruct Mor. now symmetry. apply _.
  now apply P with g. 
Qed.
