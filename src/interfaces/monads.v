
Require Import
  Setoid Morphisms
  abstract_algebra canonical_names.

Section ops.

  Context (M: Type → Type).

  Class MonadReturn := ret: ∀ {A}, A → M A.
  Class MonadBind := bind: ∀ {A B}, M A → (A → M B) → M B.

End ops.

Implicit Arguments ret [[M] [MonadReturn] [A]].
Implicit Arguments bind [[M] [MonadBind] [A] [B]].

Infix ">>=" := bind (at level 50, no associativity).
Notation "x ← y ; z" := (y >>= (λ x : _, z)) (at level 30, right associativity).
Notation "x >> y" := (_ ← x ; y) (at level 30, right associativity).

Section structure.

  Context (M: Type → Type).

  Class Monad {Me: ∀ A, Equiv A → Equiv (M A)} `{MonadReturn M} `{MonadBind M}: Prop :=
    (* Propers: *)
    { ret_proper:> ∀ `{Setoid A}, Proper (equiv ==> equiv) (@ret _ _ A)
    ; bind_proper:> ∀ `{Setoid A} `{Setoid B},
       Proper ((=) ==> ((=) ==> (=)) ==> (=)) (@bind _ _ A B)

    ; mon_setoid: ∀ `{Setoid A}, Setoid (M A)

    (* Laws: *)
    ; mon_lunit: ∀ `{Setoid A} `{Setoid B} (x: A) (f: A → M B), ret x >>= f = f x
    ; mon_runit: ∀ `{Setoid A} (m: M A), m >>= ret = m
    ; mon_assoc: ∀ `{Setoid A} `{Setoid B} `{Setoid C} (n: M A) (f: A → M B) (g: B → M C),
        (n >>= f) >>= g = n >>= (λ x, f x >>= g)
    }.

End structure.
