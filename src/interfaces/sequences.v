Require Import
  List abstract_algebra theory.categories forget_algebra forget_variety
  theory.rings interfaces.universal_algebra interfaces.functors
  categories.setoids categories.varieties.
Require
  categories.product varieties.monoids categories.algebras
  categories.categories theory.setoids.

Module ua := universal_algebra.

Instance: Arrows Type := λ X Y, X → Y.
  (* todo: move elsewhere *)

(* First, the nice clean high level encapsulated version: *)

Class PoshSequence
   (free: setoids.Object → monoids.Object) `{!Fmap free}
   (inject: id ⇛ monoids.forget ∘ free)
   (extend: `((x ⟶ monoids.forget y) → (free x ⟶ y))): Prop :=
   { sequence_adjunction: ηAdjunction _ _ inject extend
   ; extend_morphism: `(Setoid_Morphism (extend x y)) }.
     (* todo: how come extend_morphism isn't part of ηAdjunction? *)

(* This looks very nice, but the encapsulation of the parameters makes it
a bit awkward to work with. Hence, let us define a more down to earth
version. *)

Section practical.
  (* Here, again, are the ingredients, this time in somewhat more raw form: *)

  Class ExtendToSeq (free: Type → Type) :=
    extend: ∀ {x y} `{!SgOp y} `{!MonUnit y}, (x → y) → (free x → y).
      (* todo: rename to extend_to_seq or something *)

  Class InjectToSeq (free: Type → Type) := inject: ∀ x, x → free x.
      (* todo: rename to singleton or something *)

  Context
   (free: Type → Type) {raw_fmap: Fmap free}
   `{∀ a, MonUnit (free a)}
   `{∀ a, SgOp (free a)}
   `{∀ a, Equiv a → Equiv (free a)}
   `{!InjectToSeq free} `{!ExtendToSeq free}.

  Class Sequence :=
    { sequence_makes_monoids:> ∀ `{Setoid a}, Monoid (free a)
    ; sequence_inject_morphism:> ∀ `{Setoid a}, Setoid_Morphism (inject a)
    ; sequence_map_morphism:> ∀ `{Equiv x} `{Equiv y} (f: x → y),
        Setoid_Morphism f → Monoid_Morphism (raw_fmap _ _ f)
    ; sequence_fmap_proper: ∀ `{Equiv x} `{Equiv y} (f g: x → y), f = g → fmap free f = raw_fmap _ _ g
    ; sequence_fmap_id: ∀ `{Equiv x}, raw_fmap _ _ (@id x) = id
    ; sequence_fmap_comp: ∀ `{Equiv x} `{Equiv y} `{Equiv z} (f: y → z) (g: x → y),
        raw_fmap _ _ (f ∘ g) = raw_fmap _ _ f ∘ raw_fmap _ _ g
    ; sequence_extend_makes_morphisms:> ∀ `{Equiv x} `{Monoid y} (f: x → y),
        Setoid_Morphism f → Monoid_Morphism (extend f)
    ; sequence_inject_natural: ∀ `{Setoid A} `{Setoid B} (f: A → B), Setoid_Morphism f →
        inject B ∘ f = raw_fmap _ _ f ∘ inject A
    ; sequence_extend_commutes: ∀ `{Setoid x} `{Monoid y} (f: x → y), Setoid_Morphism f →
        extend f ∘ inject x = f
    ; sequence_only_extend_commutes: ∀ `{Setoid x} `{Monoid y} (f: x → y), Setoid_Morphism f →
        (∀ (g: free x → y), Monoid_Morphism g →  g ∘ inject x = f → g = extend f)
    ; sequence_extend_morphism: ∀ `{Setoid x} `{Monoid y} (f g: x → y),
        Setoid_Morphism f → Setoid_Morphism g →
        f = g → extend f (free:=free) = extend g (free:=free)
    }.

  (* From this motley collection we can construct the encapsulated free/inject/extend: *)

  Context `{PS: Sequence}.

  Program Definition posh_free (X: setoids.Object): monoids.Object := monoids.object (free X).

  Program Instance posh_fmap: functors.Fmap posh_free :=
    λ _ _ X _, raw_fmap _ _ X.

  Next Obligation. apply monoids.encode_morphism_only. destruct X. apply _. Qed.

  Instance: Functor posh_free posh_fmap.
  Proof with try apply _.
   constructor...
     repeat intro.
     constructor...
     repeat intro.
     simpl.
     apply sequence_fmap_proper.
     intro.
     apply H2.
     reflexivity.
    repeat intro.
    simpl.
    apply sequence_fmap_id.
    reflexivity.
   repeat intro.
   simpl.
   apply sequence_fmap_comp.
   reflexivity.
  Qed.

  Program Definition posh_inject: id ⇛ monoids.forget ∘ posh_free := λ a, inject a.

  Next Obligation. apply PS, _. Qed.

  (* Needed for some type conversions. *)
  Typeclasses Transparent compose.

  Program Definition posh_extend (x: setoids.Object) (y: monoids.Object)
    (X: x ⟶ monoids.forget y): posh_free x ⟶ y
    := λ u, match u return posh_free x u → y u with
      tt => @extend free ExtendToSeq0 x (monoids.forget y) _ _ X end.

  Next Obligation. apply _. Defined.
  Next Obligation. apply _. Defined.

  Next Obligation.
   apply monoids.encode_morphism_only.
   destruct X. simpl in *.
   apply (sequence_extend_makes_morphisms _). apply _.
  Qed.

  (* ... and show that they form a posh sequence: *)

  Instance: NaturalTransformation posh_inject.
  Proof.
   unfold NaturalTransformation.
   intros [???] [???] [??] ?? E.
   simpl in *.
   rewrite E.
   apply sequence_inject_natural.
   apply _.
   reflexivity.
  Qed.

  Goal @PoshSequence posh_free posh_fmap posh_inject posh_extend.
  Proof.
   constructor.
    constructor; try apply _.
    intros [x xE xH] y [f fM].
    pose proof (@monoids.decode_variety_and_ops y _ _ _).
    split.
     repeat intro.
     simpl in *.
     assert (f x0 = f y0).
      destruct fM.
      apply sm_proper.
      assumption.
     unfold compose.
     simpl in *.
     rewrite H4.
     symmetry.
     apply (@sequence_extend_commutes PS x _ _ _ _ _ _ H2 f fM).
     reflexivity.
    unfold compose.
    intros [x0 h] H4 [] a.
    unfold equiv, setoids.Equiv_instance_0 in H4.
    simpl in *.
    apply (@sequence_only_extend_commutes PS x _ _ _ _ _ _ H2 f _ (x0 tt)).
     apply (@monoids.decode_morphism_and_ops _ _ _ _ _ _ _ _ _ h).
    intros. symmetry. apply H4. reflexivity.
   unfold posh_extend.
   intros [x ??] [y ?? yV].
   constructor; try apply _.
   intros [] [] E [] a.
   simpl in *.
   apply (@sequence_extend_morphism PS x _ _ _ _ _ _
     (@monoids.decode_variety_and_ops _ _ _ yV) _ _ _ _).
   intro. apply E. reflexivity.
  Qed. (* todo: clean up *)

  Definition fold `{MonUnit M} `{SgOp M}: free M → M := extend id.

  Global Instance fold_mor `{Monoid M}: Monoid_Morphism (fold (M:=M)).
  Proof. apply _. Qed.

End practical.
