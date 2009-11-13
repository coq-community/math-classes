Require Import Structures CatStuff RingOps FieldOps SemiRingAlgebra RingAlgebra.

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

  Definition naturals_to_semiring: N -> SR := proj1_sig naturals_to_semiring_arrow tt.

  Lemma naturals_to_semiring_unique (f: N -> SR) (h: SemiRing_Morphism f): forall x, f x == naturals_to_semiring x.
  Proof.
   unfold naturals_to_semiring, naturals_to_semiring_arrow.
   destruct (naturals_initial), x.
   unfold semiring.Arrow, UniversalAlgebra.Arrow in e1.
   simpl in *. intros. symmetry.
   apply (((fun p => e1 (exist (UA.HomoMorphism semiring.sig (fun _ : unit => N) (fun _ : unit => SR)) (fun _ => f) p) tt x0: x tt x0 == f x0))).
   constructor. intro. apply _.
   destruct o; simpl.
      apply preserves_plus.
     apply preserves_mult.
    apply preserves_0.
   apply preserves_1.
  Qed.

  Definition naturals_to_semiring_mor: SemiRing_Morphism naturals_to_semiring.
  Proof.
   unfold naturals_to_semiring.
   destruct naturals_to_semiring_arrow.
   simpl.
   simpl in h.
   apply (@semiring.morphism_from_ua N _ (fun _ => SR) (fun _ => equiv) semiring.impl_from_instance semiring.impl_from_instance x h _ H0 tt).
(*
   Check (@semiring.morphism_from_ua N _ (fun _ => SR) (fun _ => equiv) semiring.impl_from_instance semiring.impl_from_instance _ _ _ H0).
*)
  Qed. (* making this an instance causes weird ring problems. see ringbug.v *)

End nicer_naturals_initial.

Lemma iso_nats `{Naturals A} B `{Naturals B}: forall a: A, naturals_to_semiring A (naturals_to_semiring B a) == a.
Proof.
 intros.
 unfold naturals_to_semiring, naturals_to_semiring_arrow.
 generalize (@naturals_initial B _ _ _ _ _ _), (@naturals_initial A _ _ _ _ _ _).
 intros.
 destruct (@initials_unique semiring.Object semiring.Arrow _ _ _ _ _ (semiring.as_object A) (semiring.as_object B) i0 i).
 apply (H2 tt a).
Qed.

Class Integers A {e plus mult opp zero one} :=
  { integers_ring:> Ring e plus mult opp zero one
  ; integers_initial: @initial _ ring.Arrow _ (ring.as_object A)
  ; integers_eqdec:> Decidable e }.

Section nicer_integers_initial.

  Context `{Integers Int} R `{Ring R}.

  Definition integers_to_ring_arrow: ring.Arrow (ring.as_object Int) (ring.as_object R)
     := proj1_sig (integers_initial (ring.as_object R)).

  Definition integers_to_ring: Int -> R := proj1_sig integers_to_ring_arrow tt.

  Lemma integers_to_ring_unique (f: Int -> R) (h: Ring_Morphism f): forall x, f x == integers_to_ring x.
  Proof.
   unfold integers_to_ring, integers_to_ring_arrow.
   destruct (integers_initial), x.
   unfold semiring.Arrow, UniversalAlgebra.Arrow in e1.
   simpl in *. intros. symmetry.
   apply (((fun p => e1 (exist (UA.HomoMorphism ring.sig (fun _ : unit => Int) (fun _ : unit => R)) (fun _ => f) p) tt x0: x tt x0 == f x0))).
   constructor. intro. apply _.
   destruct o; simpl.
       apply preserves_plus.
      apply preserves_mult.
     apply preserves_0.
    apply preserves_1.
   apply preserves_inv.
  Qed.

  Definition integers_to_ring_mor: Ring_Morphism integers_to_ring.
  Proof.
   unfold integers_to_ring.
   destruct integers_to_ring_arrow.
   simpl in h.
   apply (@ring.morphism_from_ua Int _ (fun _ => R) (fun _ => equiv) ring.impl_from_instance ring.impl_from_instance x h _ H0 tt).
  Qed.

End nicer_integers_initial.

Class Rationals A {e plus mult opp zero one mult_inv leq} :=
  { rationals_ordfield:> OrdField e plus mult opp zero one mult_inv leq
  ; rationals_eqdec:> Decidable e
  ; rationals_frac: forall `{i: Integers B} (t := integers_to_ring A) (a: A), exists num: B, exists den: B, a == t num * / t den }.
