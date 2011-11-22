Require Import
  List
  abstract_algebra.

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
    | h :: t, h' :: t' => h = h ∧ F t t'
    end.

(*
  Lemma poly_eq_p_zero p: (p = 0) = poly_eq_zero p.
  Proof. induction p; auto. Qed.
*)

  Instance: Reflexive poly_eq.
  Proof with intuition. repeat intro. induction x... split... Qed.

  Instance: Symmetric poly_eq.
  Admitted.

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
