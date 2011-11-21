(* The standard library's implementation of the integers (BinInt) uses nasty binary positive
  crap with various horrible horrible bit fiddling operations on it (especially Pminus).
  The following is a much simpler implementation whose correctness can be shown much
  more easily. In particular, it lets us use initiality of the natural numbers to prove initiality
  of these integers. *)

Require
 theory.naturals.
Require Import
 Ring abstract_algebra theory.categories
 interfaces.naturals interfaces.integers.
Require Export
 implementations.semiring_pairs.

Section contents.
Context `{Naturals N}.
Add Ring N : (rings.stdlib_semiring_theory N).

Notation Z := (SRpair N).

(* We show that Z is initial, and therefore a model of the integers. *)
Global Instance SRpair_to_ring: IntegersToRing Z :=
  λ _ _ _ _ _ _ z, naturals_to_semiring N _ (pos z) + - naturals_to_semiring N _ (neg z).

(* Hint Rewrite preserves_0 preserves_1 preserves_mult preserves_plus: preservation.
  doesn't work for some reason, so we use: *)
Ltac preservation :=
   repeat (rewrite rings.preserves_plus || rewrite rings.preserves_mult || rewrite rings.preserves_0 || rewrite rings.preserves_1).

Section for_another_ring.
  Context `{Ring R}.

  Add Ring R : (rings.stdlib_ring_theory R).

  Notation n_to_sr := (naturals_to_semiring N R).
  Notation z_to_r := (integers_to_ring Z R).

  Instance: Proper ((=) ==> (=)) z_to_r.
  Proof.
    intros [xp xn] [yp yn].
    change (xp + yn = yp + xn → n_to_sr xp - n_to_sr xn = n_to_sr yp - n_to_sr yn). intros E.
    apply rings.equal_by_zero_sum.
    transitivity (n_to_sr xp + n_to_sr yn - (n_to_sr xn + n_to_sr yp)); [ring|].
    rewrite <-2!rings.preserves_plus, E, (commutativity xn yp). ring.
  Qed.

  Ltac derive_preservation := unfold integers_to_ring, SRpair_to_ring; simpl; preservation; ring.

  Let preserves_plus x y: z_to_r (x + y) = z_to_r x + z_to_r y.
  Proof. derive_preservation. Qed.

  Let preserves_mult x y: z_to_r (x * y) = z_to_r x * z_to_r y.
  Proof. derive_preservation. Qed.

  Let preserves_1: z_to_r 1 = 1.
  Proof. derive_preservation. Qed.

  Let preserves_0: z_to_r 0 = 0.
  Proof. derive_preservation. Qed.

  Global Instance: SemiRing_Morphism z_to_r.
  Proof.
    repeat (split; try apply _).
       exact preserves_plus.
      exact preserves_0.
     exact preserves_mult.
    exact preserves_1.
  Qed.

  Section for_another_morphism.
    Context (f : Z → R) `{!SemiRing_Morphism f}.

    Definition g : N → R := f ∘ cast N (SRpair N).

    Instance: SemiRing_Morphism g.
    Proof. unfold g. repeat (split; try apply _). Qed.

    Lemma same_morphism: z_to_r = f.
    Proof.
      intros [p n] z' E. rewrite <- E. clear E z'.
      rewrite SRpair_splits.
      preservation. rewrite 2!rings.preserves_negate.
      now rewrite 2!(naturals.to_semiring_twice _ _ _).
    Qed.
  End for_another_morphism.
End for_another_ring.

Instance: Initial (rings.object Z).
Proof. apply integer_initial. intros. now apply same_morphism. Qed.

Global Instance: Integers Z := {}.

Context `{!NatDistance N}.

Global Program Instance SRpair_abs: IntAbs Z N := λ x,
  match nat_distance_sig (pos x) (neg x) with
  | inl (n↾E) => inr n
  | inr (n↾E) => inl n
  end.
Next Obligation.
  rewrite <-(naturals.to_semiring_unique (cast N (SRpair N))).
  do 2 red. simpl. now rewrite rings.plus_0_r, commutativity.
Qed.
Next Obligation.
  rewrite <-(naturals.to_semiring_unique (cast N (SRpair N))).
  do 2 red. simpl. symmetry. now rewrite rings.plus_0_r, commutativity.
Qed.

Notation n_to_z := (naturals_to_semiring N Z).

Let zero_product_aux a b :
  n_to_z a * n_to_z b = 0 → n_to_z a = 0 ∨ n_to_z b = 0.
Proof.
  rewrite <-rings.preserves_mult.
  rewrite <-(naturals.to_semiring_unique (SRpair_inject)).
  intros E. apply (injective SRpair_inject) in E.
  destruct (zero_product _ _ E) as [C|C].
   left. now rewrite C, rings.preserves_0.
  right. now rewrite C, rings.preserves_0.
Qed.

Global Instance: ZeroProduct Z.
Proof.
  intros x y E.
  destruct (SRpair_abs x) as [[a A]|[a A]], (SRpair_abs y) as [[b B]|[b B]].
     rewrite <-A, <-B in E |- *. now apply zero_product_aux.
    destruct (zero_product_aux a b) as [C|C].
      rewrite A, B. now apply rings.negate_zero_prod_r.
     left. now rewrite <-A.
    right. apply rings.flip_negate_0. now rewrite <-B.
   destruct (zero_product_aux a b) as [C|C].
     rewrite A, B. now apply rings.negate_zero_prod_l.
    left. apply rings.flip_negate_0. now rewrite <-A.
   right. now rewrite <-B.
  destruct (zero_product_aux a b) as [C|C].
    now rewrite A, B, rings.negate_mult_negate.
   left. apply rings.flip_negate_0. now rewrite <-A.
  right. apply rings.flip_negate_0. now rewrite <-B.
Qed.
End contents.
