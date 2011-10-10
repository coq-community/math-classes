Require
  theory.setoids.
Require Import
  Morphisms abstract_algebra.

Section semigroup_props.
Context `{SemiGroup G}.

Global Instance sg_op_mor_1: ∀ x, Setoid_Morphism (x &) | 0.
Proof. split; try apply _. Qed.

Global Instance sg_op_mor_2: ∀ x, Setoid_Morphism (& x) | 0.
Proof. split; try apply _. solve_proper. Qed.
End semigroup_props.

Section group_props.
Context `{Group G}.
Global Instance negate_involutive: Involutive (-).
Proof.
  intros x.
  rewrite <-(left_identity x) at 2.
  rewrite <-(left_inverse (- x)).
  rewrite <-associativity.
  rewrite left_inverse.
  now rewrite right_identity.
Qed.

Global Instance: Injective (-).
Proof.
  repeat (split; try apply _).
  intros x y E.
  now rewrite <-(involutive x), <-(involutive y), E.
Qed.

Lemma negate_mon_unit : -mon_unit = mon_unit.
Proof. rewrite <-(left_inverse mon_unit) at 2. now rewrite right_identity. Qed.

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

Lemma negate_sg_op_distr `{!AbGroup G} x y: -(x & y) = -x & -y.
Proof.
  rewrite <-(left_identity (-x & -y)).
  rewrite <-(left_inverse (x & y)).
  rewrite <-associativity.
  rewrite <-associativity.
  rewrite (commutativity (-x) (-y)).
  rewrite (associativity y).
  rewrite right_inverse.
  rewrite left_identity.
  rewrite right_inverse.
  now rewrite right_identity.
Qed.
End group_props.

Section groupmor_props.
  Context `{Group A} `{Group B} {f : A → B} `{!Monoid_Morphism f}.

  Lemma preserves_negate x : f (-x) = -f x.
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

Section from_another_sg.
  Context `{SemiGroup A} `{Setoid B}
   `{Bop : SgOp B} (f : B → A) `{!Injective f} (op_correct : ∀ x y, f (x & y) = f x & f y).

  Instance: Setoid_Morphism f := injective_mor f.
  Instance: Proper ((=) ==> (=) ==> (=)) Bop.
  Proof. intros ? ? E1 ? ? E2. apply (injective f). rewrite 2!op_correct. apply sg_op_proper; now apply sm_proper. Qed.

  Lemma projected_sg: SemiGroup B.
  Proof.
    split; try apply _.
    repeat intro; apply (injective f). now rewrite !op_correct, associativity.
  Qed.
End from_another_sg.

Section from_another_com_sg.
  Context `{CommutativeSemiGroup A} `{Setoid B}
   `{Bop : SgOp B} (f : B → A) `{!Injective f} (op_correct : ∀ x y, f (x & y) = f x & f y).

  Lemma projected_com_sg: CommutativeSemiGroup B.
  Proof.
    split. now apply (projected_sg f).
    repeat intro; apply (injective f). now rewrite !op_correct, commutativity.
  Qed.
End from_another_com_sg.

Section from_another_monoid.
  Context `{Monoid A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_monoid: Monoid B.
  Proof.
    split. now apply (projected_sg f).
     repeat intro; apply (injective f). now rewrite op_correct, unit_correct, left_identity.
    repeat intro; apply (injective f). now rewrite op_correct, unit_correct, right_identity.
  Qed.
End from_another_monoid.

Section from_another_com_monoid.
  Context `{CommutativeMonoid A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_com_monoid: CommutativeMonoid B.
  Proof.
    split. now apply (projected_monoid f).
    repeat intro; apply (injective f). now rewrite op_correct, commutativity.
  Qed.
End from_another_com_monoid.

Section from_another_group.
  Context `{Group A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit)
   (negate_correct : ∀ x, f (-x) = -f x).

  Instance: Setoid_Morphism f := injective_mor f.
  Instance: Setoid_Morphism Bnegate.
  Proof. split; try apply _. intros ? ? E1. apply (injective f). rewrite 2!negate_correct. now do 2 apply sm_proper. Qed.

  Lemma projected_group: Group B.
  Proof.
    split; try apply _. now apply (projected_monoid f).
     repeat intro; apply (injective f). now rewrite op_correct, negate_correct, unit_correct, left_inverse.
    repeat intro; apply (injective f). now rewrite op_correct, negate_correct, unit_correct, right_inverse.
  Qed.
End from_another_group.

Section from_another_ab_group.
  Context `{AbGroup A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit)
   (negate_correct : ∀ x, f (-x) = -f x).

  Lemma projected_ab_group: AbGroup B.
  Proof.
    split; try apply _. now apply (projected_group f).
    repeat intro; apply (injective f). now rewrite op_correct, commutativity.
  Qed.
End from_another_ab_group.
