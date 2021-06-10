Require
  MathClasses.theory.setoids.
Require Import
  Coq.Classes.Morphisms MathClasses.interfaces.abstract_algebra.

Section semigroup_props.
Context `{SemiGroup G}.

Global Instance sg_op_mor_1: ∀ x, Setoid_Morphism (x &) | 0.
Proof. split; try apply _. Qed.

Global Instance sg_op_mor_2: ∀ x, Setoid_Morphism (& x) | 0.
Proof. split; try apply _. solve_proper. Qed.
End semigroup_props.

(**
 * This tactic simplifies group expressions by first pushing group morphisms and
 * negations down to the leaves, then cancelling inverses and removing units.
 *)
Ltac group_simplify :=
  rewrite_strat
    (try bottomup (hints group_simplify));
    (try bottomup (choice (hints group_cancellation) <- associativity)).

Ltac group := group_simplify; easy.

Hint Rewrite @associativity using apply _: group_simplify.
Hint Rewrite @left_identity @right_identity @left_inverse @right_inverse using apply _: group_cancellation.

Section group_props.
Context `{Group G}.
Lemma negate_sg_op_distr_flip `{Group A}: ∀ a b, -(a & b) = -b & -a.
Proof.
intros.
  setoid_replace (-b & -a) with (-(a & b) & (a & b) & (-b & -a)) by group;
  rewrite <- associativity;
  setoid_replace (a & b & (-b & -a)) with mon_unit;
  group.
Qed.

Hint Rewrite @negate_sg_op_distr_flip using apply _ : group_simplify.

Global Instance negate_involutive: Involutive (-).
Proof.
  intros x;
  setoid_replace x with (- - x & (- x & x)) at 2 by group;
  setoid_replace (-x & x) with mon_unit by group;
  group.
Qed.

Hint Rewrite @negate_involutive using apply _ : group_cancellation.

Global Instance: Injective (-).
Proof.
  repeat (split; try apply _).
  intros x y E.
  now rewrite <-(involutive x), <-(involutive y), E.
Qed.

Lemma negate_mon_unit : -mon_unit = mon_unit.
Proof.
  setoid_replace mon_unit with (-mon_unit & mon_unit); group.
Qed.

Hint Rewrite @negate_mon_unit using apply _ : group_cancellation.

Global Instance: ∀ z : G, LeftCancellation (&) z.
Proof.
  intros z x y E;
  setoid_replace x with (-z & (z & x)) by group;
  rewrite E;
  group.
Qed.

Global Instance: ∀ z : G, RightCancellation (&) z.
Proof.
  intros z x y E;
  setoid_replace x with (x & z & -z) by group;
  rewrite E;
  group.
Qed.

Lemma negate_sg_op_distr `{!AbGroup G} x y: -(x & y) = -x & -y.
Proof. group_simplify. apply commutativity. Qed.

End group_props.

Section groupmor_props.
  Context `{Group A} `{Group B} {f : A → B} `{!Monoid_Morphism f}.

  Lemma preserves_negate x : f (-x) = -f x.
  Proof.
    apply (left_cancellation (&) (f x));
    rewrite <- preserves_sg_op;
    group_simplify;
    apply preserves_mon_unit.
  Qed.

  Hint Rewrite @preserves_sg_op @preserves_negate @preserves_mon_unit using apply _ : group_simplify.
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

