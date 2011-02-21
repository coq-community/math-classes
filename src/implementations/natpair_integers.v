(* The standard library's implementation of the integers (BinInt) uses nasty binary positive
  crap with various horrible horrible bit fiddling operations on it (especially Pminus).
  The following is a much simpler implementation whose correctness can be shown much
  more easily. In particular, it lets us use initiality of the natural numbers to prove initiality
  of these integers. *)

Require
 theory.naturals orders.naturals.
Require Import
 Morphisms Ring Program
 abstract_algebra theory.categories
 interfaces.naturals interfaces.integers.
Require Export
 implementations.semiring_pairs.

Section contents.
Context `{Naturals N}.
Add Ring N : (rings.stdlib_semiring_theory N).

Notation Z := (SRpair N).

(* We show that Z is initial, and therefore a model of the integers. *)
Global Instance z_to_ring: IntegersToRing Z :=
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
  Proof with try ring.
   unfold equiv, SRpair_equiv, integers_to_ring, z_to_ring. 
   intros [xp xn] [yp yn] E. simpl in *.
   apply rings.equal_by_zero_sum.
   transitivity (n_to_sr xp + n_to_sr yn + - (n_to_sr xn + n_to_sr yp))...
   apply rings.equal_by_zero_sum.
   rewrite <-2!rings.preserves_plus. rewrite E. 
   now rewrite commutativity.
  Qed.

  Ltac derive_preservation := unfold integers_to_ring, z_to_ring; simpl; preservation; ring.

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
    pose proof (_ : Ring (SRpair N)).
    repeat (split; try apply _).
       exact preserves_plus.
      exact preserves_0.
     exact preserves_mult.
    exact preserves_1.
  Qed.

  Section for_another_morphism.
    Context (f : Z → R) `{!SemiRing_Morphism f}.

    Definition g : N → R := f ∘ coerce.

    Instance: Proper ((=) ==> (=)) g.
    Proof. intros x y E. unfold g. now rewrite E. Qed.

    Instance: SemiRing_Morphism g.

    Lemma agree_on_nat : g = n_to_sr.
    Proof.
     intros x y E. rewrite E.
     apply (naturals.to_semiring_unique g).
    Qed.

    Lemma same_morphism: z_to_r = f.
    Proof with intuition.
     intros [p n] z' E. rewrite <- E. clear E z'.
     rewrite SRpair_splits.
     preservation.
     rewrite 2!rings.preserves_opp.
     rewrite (agree_on_nat p p), (agree_on_nat n n)...
     unfold integers_to_ring, z_to_ring. simpl. 
     rewrite rings.preserves_0.
     ring.
    Qed.
  End for_another_morphism.
End for_another_ring.

Instance: Initial (ring.object Z).
Proof. apply integer_initial. intros. apply same_morphism. auto. Qed.

Global Instance: Integers Z.

Lemma NtoZ_uniq x : naturals_to_semiring N Z x = 'x.
Proof. symmetry. apply (naturals.to_semiring_unique coerce x). Qed. 

Context `{!NatDistance N}.
Global Program Instance simpleZ_abs : IntAbs Z N := λ x, nat_distance (pos x) (neg x).
Next Obligation.
  rewrite NtoZ_uniq. destruct x as [xp xn].
  unfold equiv, SRpair_equiv, nat_distance.
  destruct nat_distance_sig as [z [Ez | Ez]]; simpl in *.
   right. rewrite <-Ez. ring.
  left. rewrite <-Ez. ring.
Qed.

Notation n_to_sr := (naturals_to_semiring N Z).

Lemma zero_product_aux (a b : N) : n_to_sr a * n_to_sr b = 0
  → n_to_sr a = 0 ∨ n_to_sr b = 0.
Proof.
  intros E.
  rewrite <-rings.preserves_mult in E. 
  rewrite <-(naturals.to_semiring_unique (SRpair_inject)) in E.
  apply (injective SRpair_inject) in E.
  destruct (zero_product _ _ E) as [C|C].
   left. rewrite C. apply rings.preserves_0.
  right. rewrite C. apply rings.preserves_0.
Qed.

Global Instance: ZeroProduct Z.
Proof with auto.
  intros x y E.
  destruct (simpleZ_abs x) as [a [A|A]], (simpleZ_abs y) as [b [B|B]]; rewrite <-A, <-B in E |- *.
     now apply zero_product_aux.
    destruct (zero_product_aux a b) as [C|C]...
     now apply rings.opp_zero_prod_r.
    right. rewrite C. apply rings.opp_0.
   destruct (zero_product_aux a b) as [C|C]...
    now apply rings.opp_zero_prod_l.
   left. rewrite C. apply rings.opp_0.
  rewrite rings.opp_mult_opp in E. 
  destruct (zero_product_aux a b) as [C|C]...
   left. rewrite C. apply rings.opp_0.
  right. rewrite C. apply rings.opp_0.
Qed.

End contents.
