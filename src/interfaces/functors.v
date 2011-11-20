Require Import
  abstract_algebra.
Require theory.setoids.

Section functor_class.
  Context `{Category C} `{Category D} (map_obj: C → D).

  Class Fmap: Type := fmap: ∀ {v w: C}, (v ⟶ w) → (map_obj v ⟶ map_obj w).

  Class Functor `(Fmap): Prop :=
    { functor_from: Category C
    ; functor_to: Category D
    ; functor_morphism:> ∀ a b: C, Setoid_Morphism (@fmap _ a b)
    ; preserves_id: `(fmap (cat_id: a ⟶ a) = cat_id)
    ; preserves_comp `(f: y ⟶ z) `(g: x ⟶ y): fmap (f ◎ g) = fmap f ◎ fmap g }.

End functor_class.

Typeclasses Transparent Fmap.

(* The usual notational convention for functor application is to use the
name of the functor to refer to both its object map and its arrow map, relying
on additional conventions regarding object/arrow names for disambiguation
(i.e. "F x" and "F f" map an object and an arrow, respectively, because
"x" and "f" are conventional names for objects and arrows, respectively.

In Coq, for a term F to function as though it had two different types
simultaneously (namely the object map and the arrow map), there must
either (1) be coercions from the type of F to either function, or (2) F must
be (coercible to) a single function that is able to consume both object and
arrow arguments. The following snippet shows that (1) doesn't appear to be
supported in Coq:

  Section test.
    Context (A B: Type).
    Record R := { Ra:> A → unit; Rb:> B → unit }.
    Variables (r: R) (a: A) (b: B).
    Check (r a). (* ok so far *)
    Check (r b). (* Error: The term "b" has type "B" while it is expected to have type "A". *)
  End test.

And even if this /did/ work, we could not use it, because leaving
computational components unbundled is a key aspect of our approach.

For (2), if it could be made to work at all (which is not clear at all), F would need
a pretty egregious type considering that arrow types are indexed by objects,
and that the type of the arrow map (namely "∀ x y, (x ⟶ y) → (F x ⟶ F y)")
must refer to the object map.

We feel that these issues are not limitations of the Coq system, but merely
reflect the fact that notationally identifying these two different and interdependent
maps is a typical example of an "abus de notation" that by its very nature
is ill-suited to a formal development where software engineering concerns apply.

Hence, we do not adopt this practice, and use "fmap F" (name taken from the Haskell
standard library) to refer to the arrow map of a functor F.

TODO: Sharpen. *)

Section id_functor.
  Context `{Category C}.

  Global Instance: Fmap id := λ _ _, id.

  Global Instance id_functor: Functor (id: C → C) _.
  Proof.
   constructor; try reflexivity; try apply _. intros.
   change (Setoid_Morphism (id: (a ⟶ b) → (a ⟶ b))).
   apply _.
  Qed.

End id_functor.

Section compose_functors.
  Context
    A B C
    `{!Arrows A} `{!Arrows B} `{!Arrows C}
    `{!CatId A} `{!CatId B} `{!CatId C}
    `{!CatComp A} `{!CatComp B} `{!CatComp C}
    `{∀ x y: A, Equiv (x ⟶ y)}
    `{∀ x y: B, Equiv (x ⟶ y)}
    `{∀ x y: C, Equiv (x ⟶ y)}
    `{!Functor (f: B → C) f'} `{!Functor (g: A → B) g'}.

  Global Instance comp_Fmap: Fmap (f ∘ g) := λ _ _, fmap f ∘ fmap g.

  Global Instance compose_functors: Functor (f ∘ g) _.
  Proof with intuition; try apply _.
   pose proof (functor_from g).
   pose proof (functor_to g).
   pose proof (functor_to f).
   constructor; intros; try apply _.
     apply (@setoids.compose_setoid_morphism _ _ _ _ _ _)...
     apply (@functor_morphism _ _ _ _ _ _ _ _ _ _ f _)...
     (* todo: this part really should be automatic *)
    change (fmap f (fmap g (cat_id: a ⟶ a)) = cat_id).
    repeat try rewrite preserves_id...
   change (fmap f (fmap g (f0 ◎ g0)) = fmap f (fmap g f0) ◎ fmap f (fmap g g0)).
   repeat try rewrite preserves_comp...
  Qed.

End compose_functors.

(** The Functor class is nice and abstract and theory-friendly, but not as convenient
 to use for regular programming as Haskell's Functor class. The reason for this is that
 our Functor is parameterized on two Categories, which by necessity bundle setoid-
 ness and setoid-morphism-ness into objects and arrows, respectively.
 The Haskell Functor class, by contrast, is essentially specialized for endofunctors on
 the category of Haskell types and functions between them. The latter corresponds to our
 setoid.Object category.

 To recover convenience, we introduce a second functor type class tailored specifically to
 functors of this kind. The specialization allows us to forgo bundling, and lets us recover
 the down-to-earth Type→Type type for the type constructor, and the (a→b)→(F a→F b)
 type for the function map, with all setoid/morphism proofs hidden in the structure class
 in Prop.

 To justify this definition, in theory/functors we show that instances of this new functor
 class do indeed give rise to instances of the original nice abstract Functor class. *)

Section setoid_functor.
  Context (map_obj: Type → Type) {map_eq: ∀ `{Equiv A}, Equiv (map_obj A)}.

  Class SFmap: Type := sfmap: ∀ `(v → w), (map_obj v → map_obj w).

  Class SFunctor `{SFmap}: Prop :=
    { sfunctor_makes_setoids `{Setoid A}: Setoid (map_obj A)
    ; sfunctor_makes_morphisms `{Equiv v} `{Equiv w} (f: v → w):>
        Setoid_Morphism f → Setoid_Morphism (sfmap f)
    ; sfunctor_morphism `{Setoid v} `{Setoid w}:>
        Proper (((=) ==> (=)) ==> ((=) ==> (=))) (@sfmap _ v w)
    ; sfunctor_id `{Setoid v}: sfmap id = id
    ; sfunctor_comp `{Equiv a} `{Equiv b} `{Equiv c} (f: b → c) (g: a → b):
        Setoid_Morphism f → Setoid_Morphism g →
        sfmap (f ∘ g) = sfmap f ∘ sfmap g }.

End setoid_functor.
