
Require categories.setoid.
Require Import Setoid Morphisms.
Require Import abstract_algebra canonical_names theory.categories.

Section contents.

Context (M: Type -> Type).

Class MonadReturn := ret: forall {A}, A -> M A.
Class MonadBind := bind: forall {A B}, M A -> (A -> M B) -> M B.

Infix ">>=" := bind (at level 50, no associativity).

Class Monad {Me: forall A, Equiv A -> Equiv (M A)} `{MonadReturn} `{MonadBind}: Prop :=
    (* Propers: *)
  { ret_proper:> forall `{Equiv A}, Proper (equiv ==> equiv) (@ret _ A)
  ; bind_proper:> forall `{Equiv A} `{Equiv B},
     Proper (equiv ==> (fun f g => forall x y, x == y -> f x == g y) ==> equiv) (@bind _ A B)

  ; equivalence: forall `{Setoid A}, Setoid (M A)

  (* Laws: *)
  ; mon_lunit: forall `{Setoid A} `{Setoid B} (x: A) (f: A -> M B), ret x >>= f == f x
  ; mon_runit: forall `{Setoid A} (m: M A), m >>= ret == m
  ; mon_assoc: forall `{Setoid A} `{Setoid B} `{Setoid C} (n: M A) (f: A -> M B) (g: B -> M C),
      (n >>= f) >>= g == n >>= (fun x => f x >>= g)
        (* todo: write using Setoid type class (rather than categories.setoid.Object) *)
  }.

End contents.
