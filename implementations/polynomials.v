Require Import
  Coq.Lists.List
  MathClasses.interfaces.abstract_algebra.

Section contents.
  Context R `{Ring R}.

  Definition poly := list R.

  Coercion poly_constant (c : R) : poly := [c].

  Global Instance poly_zero: Zero poly := [].
  Global Instance poly_one: One poly := poly_constant 1.

  Definition all (l: list Prop): Prop := fold_left and l True.

  Definition poly_eq_zero: poly → Prop := all ∘ map ((=) 0).

  Global Instance poly_eq: Equiv poly :=
    fix F p q :=
    match p, q with
    | [], _ => poly_eq_zero q
    | _, [] => poly_eq_zero p
    | h :: t, h' :: t' => h = h' ∧ F t t'
    end.

(*
  Lemma poly_eq_p_zero p: (p = 0) = poly_eq_zero p.
  Proof. induction p; auto. Qed.
*)

  Instance: Reflexive poly_eq.
  Proof with intuition. repeat intro. induction x... split... Qed.

  Lemma poly_eq_cons :
    ∀ (a b : R) (p q : poly), (a = b /\ poly_eq p q) <-> poly_eq (a :: p) (b :: q).
    intros a b.
    split; induction p, q; try trivial.
  Qed.

  Instance: Symmetric poly_eq.
  Proof.
    unfold Symmetric.
    induction x, y; try trivial.
    intros a_x_eq_r_y.
    apply poly_eq_cons.
    split.
    {
      assert (Hyp : a = r /\ poly_eq x y) by (now apply poly_eq_cons).
      destruct Hyp as [? _].
      now symmetry.
    }
    {
      assert (Hyp : a = r /\ poly_eq x y) by (now apply poly_eq_cons).
      destruct Hyp as [_ ?].
      now apply IHx.
    }
  Qed.

  Instance: Transitive poly_eq.
  Admitted.

  Global Instance: Setoid poly.
  Proof. split; try apply _. Qed.

  Global Instance: Plus poly := fix F p q :=
    match p, q with
    | [], _ => q
    | _, [] => p
    | h :: t, h' :: t' => h + h' :: F t t'
    end.

  Global Instance: Negate poly := map (-).

  Fixpoint poly_mult_cr (q: poly) (c: R): poly :=
    match q with
    | [] => 0
    | d :: q1 => c*d :: poly_mult_cr q1 c
    end.

  Global Instance: Mult poly := fix F p q :=
    match p with
    | [] => 0
    | c :: p1 => poly_mult_cr q c + (0 :: F p1 q)
    end.

  Global Instance: Ring poly.
   constructor.
  Admitted.

End contents.

(*

Section test.

  Context `{Ring R} (x y: poly (poly (poly (poly R)))).

  Goal x + y == x * y.
    set (d := Plus_instance_0 ).
    set (u := Mult_instance_0).
    set (t := poly (poly R)).
    unfold poly_zero.

*)
