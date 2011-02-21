Require Import 
  Setoid Program Morphisms Ring
  abstract_algebra 
  theory.fields.

(* The non zero elements of a field form a CommutativeMonoid. *)
Section contents.
Context `{Field F}.
Add Ring F : (rings.stdlib_ring_theory F).

Global Program Instance NonZero_1: RingOne (F ₀) := (1:F).
Next Obligation. now apply (rings.ne_0 1). Qed.

Global Program Instance NonZero_mult: RingMult (F ₀) := λ x y, (`x *  `y : F).
Next Obligation. apply (_ : PropHolds (`x * `y ≠ 0)). Qed.

Ltac unfold_equiv := repeat intro; unfold equiv, sig_equiv in *; simpl in *.

Instance: Proper ((=) ==> (=) ==> (=)) NonZero_mult.
Proof.
  intros [??] [??] E1 [??] [??] E2. unfold_equiv.
  now rewrite E1, E2.
Qed.

Global Instance: CommutativeMonoid (F ₀).
Proof. 
  repeat (split; try apply _); red; unfold_equiv.
     now apply associativity.
    now apply left_identity.
   now apply right_identity.
  now apply commutativity.
Qed.

Definition NonZero_inject (x : F ₀) : F := `x.

Global Instance: SemiGroup_Morphism NonZero_inject (Bop:=(.*.)).
Proof. repeat (split; try apply _); now repeat intro. Qed.

Lemma quotients (a c : F) (b d : F ₀) :
  a // b + c // d = (a * `d + c * `b) // (b * d).
Proof.
  setoid_replace (a // b) with ((a * `d) // (b * d)) by (apply equal_quotients; simpl; ring).
  setoid_replace (c // d) with ((`b * c) // (b * d)) by (apply equal_quotients; simpl; ring).
  ring. 
Qed.

Lemma mult_inv_distr `{∀ z, PropHolds (z ≠ 0) → LeftCancellation (.*.) z} (x y : F ₀) : 
  // (x * y) = // x * // y.
Proof. destruct x, y. apply mult_inv_distr_alt. Qed. 
End contents.