Require Import
 MathClasses.interfaces.abstract_algebra MathClasses.theory.categories
 MathClasses.varieties.semirings MathClasses.categories.varieties.

Module bad.
  Class Naturals (A: semirings.Object) `{!InitialArrow A}: Prop :=
    { naturals_initial:> Initial A }.
End bad.

Section initial_maps.
  Variable A: Type.

  Class NaturalsToSemiRing :=
    naturals_to_semiring: ∀ B `{Mult B} `{Plus B} `{One B} `{Zero B}, A → B.

  Context `{NaturalsToSemiRing} `{SemiRing A} `{∀ `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring B)}.

  Program Definition natural_initial_arrow: InitialArrow (semirings.object A) :=
    λ y u, match u return A → y u with tt => naturals_to_semiring (y tt) end.
  Next Obligation.
   apply (@semirings.mor_from_sr_to_alg (λ _, A) _ _ (semirings.variety A)); apply _.
  Qed.

  Global Existing Instance natural_initial_arrow.
   (* For some reason if we try to make it an instance immediately upon
    definition, Program suddenly generates 5 subgoals.. *)

  Lemma natural_initial (same_morphism : ∀ `{SemiRing B} {h :  A → B} `{!SemiRing_Morphism h}, naturals_to_semiring B = h) :
    Initial (semirings.object A).
  Proof.
    intros y [x h] [] ?. simpl in *.
    apply same_morphism.
      apply semirings.decode_variety_and_ops.
     apply (@semirings.decode_morphism_and_ops _ _ _ _ _ _ _ _ _ h).
    reflexivity.
  Qed.
End initial_maps.

Instance: Params (@naturals_to_semiring) 7.

Class Naturals A {e plus mult zero one} `{U: NaturalsToSemiRing A} :=
  { naturals_ring:> @SemiRing A e plus mult zero one
  ; naturals_to_semiring_mor:> ∀ `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B)
  ; naturals_initial:> Initial (semirings.object A) }.

(* Specializable operations: *)
Class NatDistance N `{Equiv N} `{Plus N}
  := nat_distance_sig : ∀ x y : N, { z : N | x + z = y } + { z : N | y + z = x }.
Definition nat_distance `{nd : NatDistance N} (x y : N) :=
  match nat_distance_sig x y with
  | inl (n↾_) => n
  | inr (n↾_) => n
  end.
Instance: Params (@nat_distance_sig) 4.
Instance: Params (@nat_distance) 4.
