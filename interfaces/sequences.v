Set Automatic Introduction.

Require Import
 Morphisms List Program
 abstract_algebra theory.categories forget_algebra forget_variety theory.rings interfaces.functors.
Require
 categories.setoid categories.product varieties.monoid categories.algebra.
Require categories.cat theory.setoids.

Module ua := universal_algebra.

Instance oh: Π {A} `{Equiv B} `{Equiv C} (f: B → C) `{!Setoid_Morphism f},
 Proper ((=) ==> (=)) (@compose A B C f).
Proof. firstorder. Qed.

Instance: Π {A} `{Equiv B} `{Equiv C}, Proper ((=) ==> eq ==> (=)) (@compose A B C).
Proof. repeat intro. subst. firstorder. Qed.

Lemma eta {A} `{Setoid B} (f: A → B): (λ x => f x) = f.
Proof. intro. reflexivity. Qed.

Instance: Arrows Type := λ X Y => X → Y.

(* todo: move last four  elsewhere *)

(* First, the nice clean high level encapsulated version: *)

Class PoshSequence
   (free: setoid.Object → monoid.Object) `{!Fmap free}
   (inject: id ⇛ monoid.forget ∘ free)
   (extend: `((x ⟶ monoid.forget y) → (free x ⟶ y))): Prop :=
   { sequence_adjunction: AltAdjunction _ _ inject extend
   ; extend_morphism: `(Setoid_Morphism (extend x y)) }.
     (* todo: how come extend_proper isn't part of AltAdjunction? *)

(* This looks very nice, but the encapsulation of the parameters makes it
a bit awkward to work with. Hence, let us define a more down to earth
version. *)

Section practical.

  (* Here, again, are the ingredients, this time in somewhat more raw form: *)

  Class ExtendToSeq (free: Type → Type) :=
    extend: Π {x y} `{!SemiGroupOp y} `{!MonoidUnit y}, (x → y) → (free x → y).
      (* todo: rename to extend_to_seq or something *)

  Class InjectToSeq (free: Type → Type) := inject: Π x, x → free x.
      (* todo: rename to singleton or something *)

  Context
   (free: Type → Type) {raw_fmap: Fmap free}
   `{Π a, MonoidUnit (free a)}
   `{Π a, SemiGroupOp (free a)}
   `{Π a, Equiv a → Equiv (free a)}
   `{!InjectToSeq free} `{!ExtendToSeq free}.

  Class Sequence :=
    { sequence_makes_monoids:> Π `{Setoid a}, Monoid (free a)
    ; sequence_inject_morphism:> Π `{Setoid a}, Setoid_Morphism (inject a)
    ; sequence_map_morphism:> Π `{Equiv x} `{Equiv y} (f: x → y),
        Setoid_Morphism f → Monoid_Morphism (raw_fmap _ _ f)
    ; sequence_extend_makes_morphisms:> Π `{Equiv x} `{Monoid y} (f: x → y),
        Setoid_Morphism f → Monoid_Morphism (extend f)
    ; sequence_inject_natural: Π `{Setoid A} `{Setoid B} (f: A → B), Setoid_Morphism f →
        inject B ∘ f = raw_fmap _ _ f ∘ inject A
    ; sequence_extend_commutes: Π `{Setoid x} `{Monoid y} (f: x → y), Setoid_Morphism f →
        extend f ∘ inject x = f
    ; sequence_only_extend_commutes: Π `{Setoid x} `{Monoid y} (f: x → y), Setoid_Morphism f →
        (Π (g: free x → y), Monoid_Morphism g →  g ∘ inject x = f → g = extend f)
    ; sequence_extend_morphism: Π `{Setoid x} `{Monoid y} (f g: x → y),
        Setoid_Morphism f → Setoid_Morphism g →
        f = g → extend f = extend g
    }.

  (* From this motley collection we can construct the encapsulated free/inject/extend: *)

  Context `{PS: Sequence}.

  Program Definition posh_free (X: setoid.Object): monoid.Object := monoid.object (free X).

  Program Instance posh_fmap: functors.Fmap posh_free :=
    λ _ _ X _ => raw_fmap _ _ X.

  Next Obligation. apply monoid.encode_morphism_only. destruct X. apply _. Qed.

  Program Definition posh_inject: id ⇛ monoid.forget ∘ posh_free := λ a => inject a.

  Next Obligation. apply PS, _. Qed.

  Program Definition posh_extend (x: setoid.Object) (y: monoid.Object)
    (X: x ⟶ monoid.forget y): posh_free x ⟶ y
    := λ u => match u return posh_free x u → y u with
      tt => @extend free _ x (monoid.forget y) _ _ X end.

  Next Obligation. apply _. Defined.
  Next Obligation. apply _. Defined.

  Next Obligation.
   apply monoid.encode_morphism_only.
   destruct X. simpl in *. apply _.
  Qed.

  (* ... and show that they form a posh sequence: *)

  Goal @PoshSequence posh_free posh_fmap posh_inject posh_extend.
  Proof.
   constructor.
    constructor.
     unfold NaturalTransformation.
     intros [???] [???] [??] ?? E.
     simpl in *.
     rewrite E.
     apply sequence_inject_natural.
     apply _.
    intros [x xE xH] y [f fM].
    pose proof (@monoid.decode_variety_and_ops y _ _ _).
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
    unfold compose.
    intros [x0 h] H4 [] a.
    unfold equiv, setoid.Equiv_instance_0 in H4.
    simpl in *.
    apply (@sequence_only_extend_commutes PS x _ _ _ _ _ _ H2 f _ (x0 tt)).
     apply (@monoid.decode_morphism_and_ops _ _ _ _ _ _ _ _ _ h).
    intro. symmetry. apply H4. reflexivity.
   unfold posh_extend.
   intros [x ??] [y ?? yV].
   constructor; try apply _.
   intros [] [] E [] a.
   simpl in *.
   apply (@sequence_extend_morphism PS x _ _ _ _ _ _
     (@monoid.decode_variety_and_ops _ _ _ yV) _ _ _ _).
   intro. apply E. reflexivity.
  Qed. (* todo: clean up *)

  Definition fold `{MonoidUnit M} `{SemiGroupOp M}: free M → M := extend id.

  Global Instance fold_mor `{Monoid M}: Monoid_Morphism (fold (M:=M)).
  Proof. apply _. Qed.

End practical.
