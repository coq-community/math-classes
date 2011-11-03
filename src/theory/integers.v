(* General results about arbitrary integer implementations. *)
Require
 theory.nat_distance.
Require Import
 Ring interfaces.naturals abstract_algebra natpair_integers.
Require Export
 interfaces.integers.

(* Any two integer implementations are trivially isomorphic because of their initiality,
 but it's nice to have this stated in terms of integers_to_ring being self-inverse: *)
Lemma to_ring_involutive `{Integers Int} Int2 `{Integers Int2} x :
  integers_to_ring Int2 Int (integers_to_ring Int Int2 x) = x.
Proof.
  rapply (proj2 (@categories.initials_unique' _ _ _ _ _ _ (rings.object Int) (rings.object Int2) _
    integers_initial _ integers_initial) tt x).
Qed.

Lemma to_ring_unique `{Integers Int} `{Ring R} (f: Int → R) {h: SemiRing_Morphism f} x :
  f x = integers_to_ring Int R x.
Proof.
  symmetry.
  pose proof (rings.encode_morphism_and_ops (f:=f)).
  set (@varieties.arrow rings.theory _ _ _ (rings.encode_variety_and_ops _) _ _ _ (rings.encode_variety_and_ops _) (λ _, f) _).
  exact (integers_initial _ a tt x).
Qed.

Lemma to_ring_unique_alt `{Integers Int} `{Ring R} (f g: Int → R) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x :
  f x = g x.
Proof. now rewrite (to_ring_unique f), (to_ring_unique g). Qed.

Lemma morphisms_involutive `{Integers N} `{Integers N2} (f: N → N2) (g: N2 → N)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x : f (g x) = x.
Proof. now apply (to_ring_unique_alt (f ∘ g) id). Qed.

Lemma to_ring_twice `{Integers N} `{Ring R1} `{Ring R2} (f : R1 → R2) (g : N → R1) (h : N → R2)
     `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} `{!SemiRing_Morphism h} x :
  f (g x) = h x.
Proof. now apply (to_ring_unique_alt (f ∘ g) h). Qed.

Lemma to_ring_self `{Integers N} (f : N → N) `{!SemiRing_Morphism f} x : f x = x.
Proof. now apply (to_ring_unique_alt f id). Qed.

(* A ring morphism from integers to another ring is injective if there's an injection in the other direction: *)
Lemma to_ring_injective `{Integers Int} `{Ring R} (f: R → Int) (g: Int → R) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}:
  Injective g.
Proof.
  repeat (split; try apply _). intros x y E.
  rewrite <-(to_ring_self (f ∘ g) x), <-(to_ring_self (f ∘ g) y).
  unfold compose. now rewrite E.
Qed.

Instance integers_to_integers_injective `{Integers Int} `{Integers Int2} (f: Int → Int2) `{!SemiRing_Morphism f}:
  Injective f.
Proof. apply (to_ring_injective (integers_to_ring Int2 Int) _). Qed.

Instance naturals_to_integers_injective `{Integers Int} `{Naturals N} (f: N → Int) `{!SemiRing_Morphism f} :
  Injective f.
Proof.
  split; try apply _. intros x y E.
  apply (injective (cast N (SRpair N))).
  now rewrite <-2!(naturals.to_semiring_twice (integers_to_ring Int (SRpair N)) f (cast N (SRpair N))), E.
Qed.

Section retract_is_int.
  Context `{Integers Int} `{Ring Int2}.
  Context (f : Int → Int2) `{!Inverse f} `{!Surjective f} `{!SemiRing_Morphism f} `{!SemiRing_Morphism (f⁻¹)}.

  (* If we make this an instance, then instance resolution will often loop *)
  Definition retract_is_int_to_ring : IntegersToRing Int2 := λ R _ _ _ _ _, integers_to_ring Int R ∘ f⁻¹.

  Section for_another_ring.
    Context `{Ring R}.

    Instance: SemiRing_Morphism (integers_to_ring Int R ∘ f⁻¹) := {}.
    Context (h :  Int2 → R) `{!SemiRing_Morphism h}.

    Lemma same_morphism: integers_to_ring Int R ∘ f⁻¹ = h.
    Proof with auto.
      intros x y F. rewrite <-F.
      transitivity ((h ∘ (f ∘ f⁻¹)) x).
       symmetry. unfold compose. apply (to_ring_unique (h ∘ f)).
      unfold compose. now rewrite jections.surjective_applied.
    Qed.
  End for_another_ring.

  (* If we make this an instance, then instance resolution will often loop *)
  Program Instance retract_is_int: Integers Int2 (U:=retract_is_int_to_ring).
  Next Obligation. unfold integers_to_ring, retract_is_int_to_ring. apply _. Qed.
  Next Obligation. apply integer_initial. intros. now apply same_morphism. Qed.
End retract_is_int.

Section contents.
Context `{Integers Int}.

Global Program Instance: ∀ x y: Int, Decision (x = y) | 10 := λ x y,
  match decide (integers_to_ring Int (SRpair nat) x = integers_to_ring Int (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (injective (integers_to_ring Int (SRpair nat))). Qed.
Next Obligation. intros F. apply E. now rewrite F. Qed.

Instance: PropHolds ((1:Int) ≠ 0).
Proof.
  intros E.
  apply (rings.is_ne_0 (1:nat)).
  apply (injective (naturals_to_semiring nat Int)).
  now rewrite rings.preserves_0, rings.preserves_1.
Qed.

Global Instance: ZeroProduct Int.
Proof.
  intros x y E.
  destruct (zero_product (integers_to_ring Int (SRpair nat) x) (integers_to_ring Int (SRpair nat) y)).
    now rewrite <-rings.preserves_mult, E, rings.preserves_0.
   left. apply (injective (integers_to_ring Int (SRpair nat))). now rewrite rings.preserves_0.
  right. apply (injective (integers_to_ring Int (SRpair nat))). now rewrite rings.preserves_0.
Qed.

Global Instance: IntegralDomain Int := {}.
End contents.
