Require
  theory.setoids.
Require Import
  Morphisms abstract_algebra.

Section group_props. 
Context `{Group G}.

Lemma inv_involutive x: - - x = x.
Proof.
  rewrite <-(left_identity x) at 2.
  rewrite <-(ginv_l (- x)).
  rewrite <-associativity.
  rewrite ginv_l.
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
Proof. rewrite <- (ginv_l mon_unit) at 2. rewrite right_identity. reflexivity. Qed.

Global Instance: ∀ z : G, LeftCancellation sg_op z.
Proof.
  intros z x y E.
  rewrite <-(left_identity x), <-(ginv_l z), <-associativity.
  rewrite E.
  now rewrite associativity, ginv_l, left_identity.
Qed.  

Global Instance: ∀ z : G, RightCancellation sg_op z.
Proof.
  intros z x y E.
  rewrite <-(right_identity x), <-(ginv_r z), associativity.
  rewrite E.
  now rewrite <-associativity, ginv_r, right_identity.
Qed.  

Lemma sg_inv_distr `{!AbGroup G} x y: - (x & y) = - x & - y.
Proof.
  rewrite <-(left_identity (- x & - y)).
  rewrite <-(ginv_l (x & y)).
  rewrite <-associativity.
  rewrite <-associativity.
  rewrite (commutativity (- x) (- y)).
  rewrite (associativity y).
  rewrite ginv_r.
  rewrite left_identity.
  rewrite ginv_r.
  now rewrite right_identity.
Qed.
End group_props.

Section groupmor_props. 
  Context `{Group A} `{Group B} {f : A → B} `{!Monoid_Morphism f}.

  Lemma preserves_inv x: f (- x) = - f x.
  Proof.
    apply (left_cancellation sg_op (f x)).
    rewrite <-preserves_sg_op.
    rewrite 2!ginv_r.
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
