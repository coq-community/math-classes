Require Import
  abstract_algebra interfaces.naturals theory.categories
  categories.varieties.
Require
  varieties.rings.

Section initial_maps.
  Variable A : Type.

  Class IntegersToRing :=
    integers_to_ring: ∀ R `{Mult R} `{Plus R} `{One R} `{Zero R} `{Negate R}, A → R.

  Context `{IntegersToRing} `{Ring A} `{∀ `{Ring B}, SemiRing_Morphism (integers_to_ring B)}.

  Global Instance integer_initial_arrow: InitialArrow (rings.object A).
   intro y.
   exists (λ u, match u return A → y u with tt => integers_to_ring (y tt) end).
   abstract (apply rings.encode_morphism_only; apply _).
  Defined. (* for some reason [Program] isn't cooperating here. look into it *)

  Lemma integer_initial (same_morphism : ∀ `{Ring B} {h :  A → B} `{!SemiRing_Morphism h}, integers_to_ring B = h) :
    Initial (rings.object A).
  Proof.
    intros y [x h] [] ?. simpl in *.
    apply same_morphism.
      apply rings.decode_variety_and_ops.
     apply (@rings.decode_morphism_and_ops _ _ _ _ _ _ _ _ _ h).
    reflexivity.
  Qed.
End initial_maps.

Instance: Params (@integers_to_ring) 8.

Class Integers A {e plus mult zero one negate} `{U : IntegersToRing A} :=
  { integers_ring:> @Ring A e plus mult zero one negate
  ; integers_to_ring_mor:> ∀ `{Ring B}, SemiRing_Morphism (integers_to_ring A B)
  ; integers_initial:> Initial (rings.object A) }.

Section specializable.
  Context (Z N : Type) `{Integers Z} `{Naturals N}.

  Class IntAbs := int_abs_sig : ∀ x,
    { n : N | naturals_to_semiring N Z n = x } + { n : N | naturals_to_semiring N Z n = -x }.

  Definition int_abs `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n↾_) => n
    | inr (n↾_) => n
    end.

  Definition int_to_nat `{Zero N} `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n↾_) => n
    | inr (n↾_) => 0
    end.
End specializable.

Instance: Params (@int_abs) 10.
Instance: Params (@int_abs_sig) 10.
Instance: Params (@int_to_nat) 11.
