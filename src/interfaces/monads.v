
Require categories.setoid.
Require Import Setoid Morphisms.
Require Import abstract_algebra canonical_names theory.categories.

Section contents.

Context (M: Type → Type).

Class MonadReturn := ret: Π {A}, A → M A.
Class MonadBind := bind: Π {A B}, M A → (A → M B) → M B.

Infix ">>=" := bind (at level 50, no associativity).

Class Monad {Me: Π A, Equiv A → Equiv (M A)} `{MonadReturn} `{MonadBind}: Prop :=
    (* Propers: *)
  { ret_proper:> Π `{Equiv A}, Proper (equiv ==> equiv) (@ret _ A)
  ; bind_proper:> Π `{Equiv A} `{Equiv B},
     Proper (equiv ==> (equiv ==> equiv) ==> equiv) (@bind _ A B)

  ; equivalence: Π `{Setoid A}, Setoid (M A)

  (* Laws: *)
  ; mon_lunit: Π `{Setoid A} `{Setoid B} (x: A) (f: A → M B), ret x >>= f = f x
  ; mon_runit: Π `{Setoid A} (m: M A), m >>= ret = m
  ; mon_assoc: Π `{Setoid A} `{Setoid B} `{Setoid C} (n: M A) (f: A → M B) (g: B → M C),
      (n >>= f) >>= g = n >>= (λ x => f x >>= g)
        (* todo: write using Setoid type class (rather than categories.setoid.Object) *)
  }.

End contents.
