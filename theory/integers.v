(* General results about arbitrary integer implementations. *)
Require
 MathClasses.theory.nat_distance.
Require Import
 Coq.setoid_ring.Ring MathClasses.interfaces.naturals MathClasses.interfaces.abstract_algebra MathClasses.implementations.natpair_integers.
Require Export
 MathClasses.interfaces.integers.

(* Any two integer implementations are trivially isomorphic because of their initiality,
 but it's nice to have this stated in terms of integers_to_ring being self-inverse: *)
Lemma to_ring_involutive `{Integers Z} Z2 `{Integers Z2} x :
  integers_to_ring Z2 Z (integers_to_ring Z Z2 x) = x.
Proof.
  rapply (proj2 (@categories.initials_unique' _ _ _ _ _ _ (rings.object Z) (rings.object Z2) _
    integers_initial _ integers_initial) tt x).
Qed.

Lemma to_ring_unique `{Integers Z} `{Ring R} (f: Z → R) {h: SemiRing_Morphism f} x :
  f x = integers_to_ring Z R x.
Proof.
  symmetry.
  pose proof (rings.encode_morphism_and_ops (f:=f)).
  set (@varieties.arrow rings.theory _ _ _ (rings.encode_variety_and_ops _) _ _ _ (rings.encode_variety_and_ops _) (λ _, f) _).
  exact (integers_initial _ a tt x).
Qed.

Lemma to_ring_unique_alt `{Integers Z} `{Ring R} (f g: Z → R) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x :
  f x = g x.
Proof. now rewrite (to_ring_unique f), (to_ring_unique g). Qed.

Lemma morphisms_involutive `{Integers Z} `{Integers Z2} (f: Z → Z2) (g: Z2 → Z)
  `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} x : f (g x) = x.
Proof. now apply (to_ring_unique_alt (f ∘ g) id). Qed.

Lemma to_ring_twice `{Integers Z} `{Ring R1} `{Ring R2} (f : R1 → R2) (g : Z → R1) (h : Z → R2)
     `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} `{!SemiRing_Morphism h} x :
  f (g x) = h x.
Proof. now apply (to_ring_unique_alt (f ∘ g) h). Qed.

Lemma to_ring_self `{Integers Z} (f : Z → Z) `{!SemiRing_Morphism f} x : f x = x.
Proof. now apply (to_ring_unique_alt f id). Qed.

(* A ring morphism from integers to another ring is injective if there's an injection in the other direction: *)
Lemma to_ring_injective `{Integers Z} `{Ring R} (f: R → Z) (g: Z → R) `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} :
  Injective g.
Proof.
  repeat (split; try apply _). intros x y E.
  rewrite <-(to_ring_self (f ∘ g) x), <-(to_ring_self (f ∘ g) y).
  unfold compose. now rewrite E.
Qed.

Instance integers_to_integers_injective `{Integers Z} `{Integers Z2} (f: Z → Z2) `{!SemiRing_Morphism f} :
  Injective f.
Proof. apply (to_ring_injective (integers_to_ring Z2 Z) _). Qed.

Instance naturals_to_integers_injective `{Integers Z} `{Naturals N} (f: N → Z) `{!SemiRing_Morphism f} :
  Injective f.
Proof.
  split; try apply _. intros x y E.
  apply (injective (cast N (SRpair N))).
  now rewrite <-2!(naturals.to_semiring_twice (integers_to_ring Z (SRpair N)) f (cast N (SRpair N))), E.
Qed.

Section retract_is_int.
  Context `{Integers Z} `{Ring Z2}.
  Context (f : Z → Z2) `{!Inverse f} `{!Surjective f} `{!SemiRing_Morphism f} `{!SemiRing_Morphism (f⁻¹)}.

  (* If we make this an instance, then instance resolution will often loop *)
  Definition retract_is_int_to_ring : IntegersToRing Z2 := λ Z2 _ _ _ _ _, integers_to_ring Z Z2 ∘ f⁻¹.

  Section for_another_ring.
    Context `{Ring R}.

    Instance: SemiRing_Morphism (integers_to_ring Z R ∘ f⁻¹) := {}.
    Context (h :  Z2 → R) `{!SemiRing_Morphism h}.

    Lemma same_morphism: integers_to_ring Z R ∘ f⁻¹ = h.
    Proof with auto.
      intros x y F. rewrite <-F.
      transitivity ((h ∘ (f ∘ f⁻¹)) x).
       symmetry. unfold compose. apply (to_ring_unique (h ∘ f)).
      unfold compose. now rewrite jections.surjective_applied.
    Qed.
  End for_another_ring.

  (* If we make this an instance, then instance resolution will often loop *)
  Program Instance retract_is_int: Integers Z2 (U:=retract_is_int_to_ring).
  Next Obligation. unfold integers_to_ring, retract_is_int_to_ring. apply _. Qed.
  Next Obligation. apply integer_initial. intros. now apply same_morphism. Qed.
End retract_is_int.

Section contents.
Context `{Integers Z}.

Global Program Instance: ∀ x y: Z, Decision (x = y) | 10 := λ x y,
  match decide (integers_to_ring Z (SRpair nat) x = integers_to_ring Z (SRpair nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (injective (integers_to_ring Z (SRpair nat))). Qed.

Global Program Instance slow_int_abs `{Naturals N} : IntAbs Z N | 10 := λ x, 
  match int_abs_sig (SRpair N) N (integers_to_ring Z (SRpair N) x) with
  | inl (n↾E) => inl n
  | inr (n↾E) => inr n
  end.
Next Obligation.
  apply (injective (integers_to_ring Z (SRpair N))).
  rewrite <-E. apply (naturals.to_semiring_twice _ _ _).
Qed.
Next Obligation.
  apply (injective (integers_to_ring Z (SRpair N))).
  rewrite rings.preserves_negate, <-E.
  now apply (naturals.to_semiring_twice _ _ _).
Qed.

Instance: PropHolds ((1:Z) ≠ 0).
Proof.
  intros E.
  apply (rings.is_ne_0 (1:nat)).
  apply (injective (naturals_to_semiring nat Z)).
  now rewrite rings.preserves_0, rings.preserves_1.
Qed.

Global Instance: ZeroProduct Z.
Proof.
  intros x y E.
  destruct (zero_product (integers_to_ring Z (SRpair nat) x) (integers_to_ring Z (SRpair nat) y)).
    now rewrite <-rings.preserves_mult, E, rings.preserves_0.
   left. apply (injective (integers_to_ring Z (SRpair nat))). now rewrite rings.preserves_0.
  right. apply (injective (integers_to_ring Z (SRpair nat))). now rewrite rings.preserves_0.
Qed.

Global Instance: IntegralDomain Z := {}.
End contents.
