Require RingCat.
Require Import Structures CatStuff RingOps FieldOps.

Class Naturals A {e plus mult zero one} :=
  { naturals_ring:> SemiRing e plus mult zero one
  ; naturals_initial: @initial _ semiring.Arrow _ (semiring.as_object A)
  ; naturals_eqdec:> Decidable e }.

(* Above, initiality is stated in categorical/universal algebra terms, which isn't the most
 pleasant form to subsequently reason about. We therefore state its key properties in
 more pleasant terms of canonical SemiRing_Morphisms, below. *)

Section nicer_naturals_initial.

  Context `{Naturals N} SR `{SemiRing SR}.

  Definition naturals_to_semiring_arrow: semiring.Arrow (semiring.as_object N) (semiring.as_object SR)
     := proj1_sig (naturals_initial (semiring.as_object SR)).

  Definition naturals_to_semiring: N -> SR := proj1_sig naturals_to_semiring_arrow.

  Lemma naturals_to_semring_unique (f: N -> SR) (h: SemiRing_Morphism f): forall x, f x == naturals_to_semiring x.
  Proof.
   unfold naturals_to_semiring, naturals_to_semiring_arrow.
   destruct (naturals_initial), x.
   unfold semiring.Arrow, UniversalAlgebra.Arrow in e1.
   simpl in *. intros. symmetry.
   apply (((fun p => e1 (exist _ f p) x0: x x0 == f x0))).
   constructor. apply _.
   destruct o; simpl.
      apply preserves_plus.
     apply preserves_mult.
    apply preserves_0.
   apply preserves_1.
  Qed.

  Definition naturals_to_semiring_mor: SemiRing_Morphism naturals_to_semiring.
  Proof.
   unfold naturals_to_semiring.
   intros.
   destruct naturals_to_semiring_arrow.
   apply (@hmok _ _ _ _ semiring.impl_from_instance semiring.impl_from_instance _ _ _ _).
  Qed. (* making this an instance causes weird ring problems. see ringbug.v *)

End nicer_naturals_initial.

Lemma iso_nats `{Naturals A} B `{Naturals B}: forall a: A, naturals_to_semiring A (naturals_to_semiring B a) == a.
Proof.
 intros.
 unfold naturals_to_semiring, naturals_to_semiring_arrow.
 generalize (@naturals_initial B _ _ _ _ _ _), (@naturals_initial A _ _ _ _ _ _).
 intros.
 destruct (@initials_unique semiring.Object semiring.Arrow _ _ _ _ _ (semiring.as_object A) (semiring.as_object B) i0 i).
 apply (H2 a).
Qed.

Class Integers A {e plus mult opp zero one} :=
  { integers_ring:> Ring e plus mult opp zero one
  ; integers_initial: @initial RingCat.O RingCat.A RingCat.a_equiv (RingCat.MkO A)
  ; integers_eqdec:> Decidable e }.

Definition integers_to_ring `{Integers In} `{Ring R}: In -> R := proj1_sig (proj1_sig (integers_initial (RingCat.MkO R))).

Class Rationals A {e plus mult opp zero one mult_inv leq} :=
  { rationals_ordfield:> OrdField e plus mult opp zero one mult_inv leq
  ; rationals_eqdec:> Decidable e
  ; rationals_frac: forall `{i: Integers B} (t := integers_to_ring) (a: A), exists num: B, exists den: B, a == t num * / t den }.
