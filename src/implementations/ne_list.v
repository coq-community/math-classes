Set Implicit Arguments.

Require Import
  Unicode.Utf8 canonical_names Setoid.

Section contents.

  Variable T: Type.

  Inductive L: Type := one: T → L | cons: T → L → L.

  Fixpoint app (a b: L) {struct a}: L :=
    match a with
    | one x => cons x b
    | cons x y => cons x (app y b)
    end.

  Fixpoint foldr {R} (o: T → R) (f: T → R → R) (a: L): R :=
    match a with
    | one x => o x
    | cons x y => f x (foldr o f y)
    end.

  Fixpoint foldr1 (f: T → T → T) (a: L): T :=
    match a with
    | one x => x
    | cons x y => f x (foldr1 f y)
    end.

  Definition head (l: L): T := match l with one x => x | cons x _ => x end.

  Definition last: L → T := foldr1 (λ x y, y).

  Fixpoint replicate_Sn (x: T) (n: nat): L :=
    match n with
    | 0 => one x
    | S n' => cons x (replicate_Sn x n')
    end.

End contents.

Fixpoint map `(f: A → B) (l: L A): L B :=
  match l with
  | one x => one (f x)
  | cons h t => cons (f h) (map f t)
  end.
