Require Import
  abstract_algebra canonical_names.
Require Export
  interfaces.functors.

Section ops.
  Context (M : Type → Type).

  Class MonadReturn := ret: ∀ {A}, A → M A.
  Class MonadBind := bind: ∀ {A B}, (A → M B) → M A → M B.
  Class MonadJoin := join: ∀ {A}, M (M A) → M A.
End ops.

Arguments ret {M MonadReturn A} _.
Arguments bind {M MonadBind A B} _ _.
Arguments join {M MonadJoin A} _.

Notation "m ≫= f" := (bind f m) (at level 60, right associativity) : mc_scope.
Notation "x ← y ; z" := (y ≫= (λ x : _, z)) (at level 65, next at level 35, right associativity, only parsing) : mc_scope.
(* Notation "x ≫ y" := (_ ← x ; y) (at level 33, right associativity, only parsing) : mc_scope. *)

Class Monad (M : Type → Type) `{∀ A, Equiv A → Equiv (M A)} 
     `{MonadReturn M} `{MonadBind M} : Prop :=
  { mon_ret_proper `{Setoid A} :> Proper ((=) ==> (=)) (@ret _ _ A)
  ; mon_bind_proper `{Setoid A} `{Setoid B} :>
      Proper (((=) ==> (=)) ==> (=) ==> (=)) (@bind _ _ A B)
  ; mon_setoid `{Setoid A} :> Setoid (M A)
  ; bind_lunit `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} : bind f ∘ ret = f
  ; bind_runit `{Setoid A} : bind ret = id
  ; bind_assoc `{Equiv A} `{Equiv B} `{Setoid C} 
         `{!Setoid_Morphism (f : B → M C)} `{!Setoid_Morphism (g : A → M B)} :
      bind f ∘ bind g = bind (bind f ∘ g) }.

Class StrongMonad (M : Type → Type) `{∀ A, Equiv A → Equiv (M A)}
     `{MonadReturn M} `{SFmap M} `{MonadJoin M} : Prop :=
  { smon_ret_proper `{Setoid A} :> Proper ((=) ==> (=)) (@ret _ _ A)
  ; smon_join_proper `{Setoid A} :> Proper ((=) ==> (=)) (@join _ _ A)
  ; smon_sfunctor :> SFunctor M  
  ; sfmap_ret `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} :
      sfmap f ∘ ret = ret ∘ f
  ; sfmap_join `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)} : 
      sfmap f ∘ join = join ∘ sfmap (sfmap f)
  ; join_ret `{Setoid A} :
      join ∘ ret = id
  ; join_sfmap_ret `{Setoid A} :
      join ∘ sfmap ret = id
  ; join_sfmap_join `{Setoid A} :
      join ∘ sfmap join = join ∘ join }.

Class FullMonad (M : Type → Type) `{∀ A, Equiv A → Equiv (M A)} 
     `{MonadReturn M} `{MonadBind M} `{SFmap M} `{MonadJoin M} : Prop := 
  { full_mon_mon :> Monad M
  ; full_smon :> StrongMonad M
  ; bind_as_join_sfmap `{Equiv A} `{Setoid B} `{!Setoid_Morphism (f : A → M B)} :
      bind f = join ∘ sfmap f }.
