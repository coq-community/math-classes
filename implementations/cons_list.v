Require Import
 Morphisms List
 abstract_algebra.

Implicit Arguments app [[A]].

Section contents.

  Variable A: Type.

  Global Instance list_setoid: Equiv (list A) := eq.

  Global Instance: SemiGroupOp (list A) := app.

  Global Instance: Proper (equiv ==> equiv ==> equiv)%signature app.
  Proof. unfold equiv, list_setoid. repeat intro. subst. reflexivity. Qed.

  Global Instance app_assoc_inst: Associative app.
  Proof. repeat intro. symmetry. apply (app_ass x y z). Qed.

  Global Instance: SemiGroup (list A).

  Global Instance: MonoidUnit (list A) := nil.

  Global Instance: Monoid (list A) := { monoid_lunit := fun x => @refl_equal _ x }.
  Proof. symmetry. apply (app_nil_end x). Qed.

End contents.

