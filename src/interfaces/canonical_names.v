Global Generalizable All Variables.
Global Set Automatic Introduction.

Require Export
  Morphisms Setoid Program Unicode.Utf8 Utf8_core.

(* Equality *)
Class Equiv A := equiv: relation A.

(* Revert to transparency to allow conversions during unification. *)
Typeclasses Transparent Equiv.
Typeclasses Transparent compose flip.

(* We use this virtually everywhere, and so use "=" for it: *)
Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing).
Notation "( x =)" := (equiv x) (only parsing).
Notation "(= x )" := (λ y, equiv y x) (only parsing).
Notation "(≠)" := (λ x y, ¬x = y) (only parsing).
Notation "x ≠ y":= (¬x = y): type_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing).
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing).

(* Coq sometimes uses an incorrect DefaultRelation, so we override it. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (=) | 3.

(*
Because Coq does not support setoid rewriting in Type'd relations
we put apartness in Prop. This has as obvious disadvantage, that when an
implementation actually needs the witness from the apartness relation (e.g. for
division), it has to use something like [constructive_indefinite_description]
to extract it. This is quite inefficient and will also most likely block due
to proofs being Opaque. Nonetheless we do not think this is a problem because
for actual computation, one does not want to rely on some arbitrary witness
obtained by chaining a lot of proofs. Instead one would (and probably should)
specify an optimal witness by hand.

Another advantage of our approach is that classes describing structures (e.g.
Field) can remain in Prop.
*)
Class Apart A := apart: relation A.
Infix "≶" := apart (at level 70, no associativity) : type_scope.
Notation "(≶)" := apart (only parsing).
Notation "( x ≶)" := (apart x) (only parsing).
Notation "(≶ x )" := (λ y, apart y x) (only parsing).

(* Even for setoids with decidable equality x ≠ y does not imply x ≶ y.
Therefore we introduce the following class. *)
Class TrivialApart A `{Equiv A} {Aap : Apart A} := trivial_apart : ∀ x y, x ≶ y ↔ x ≠ y.

(* For Leibniz equality we use "≡", We do not define it as setoid equality with
low priority because sometimes we are interested in both setoid and Leibniz
equality on the same structure. *)
Infix "≡" := eq (at level 70, no associativity).
Notation "(≡)" := eq (only parsing).
Notation "( x ≡)" := (eq x) (only parsing).
Notation "(≡ x )" := (λ y, eq y x) (only parsing).
Notation "(≢)" := (λ x y, ¬x ≡ y) (only parsing).
Notation "x ≢ y":= (¬x ≡ y) (at level 70, no associativity).
Notation "( x ≢)" := (λ y, x ≢ y) (only parsing).
Notation "(≢ x )" := (λ y, y ≢ x) (only parsing).

(* Some common notions of equality *)
Definition ext_equiv `{Equiv A} `{Equiv B} : Equiv (A → B) := ((=) ==> (=))%signature.
Hint Extern 10 (Equiv (_ → _)) => apply @ext_equiv : typeclass_instances.
Hint Extern 10 (Equiv (relation _)) => apply @ext_equiv : typeclass_instances. (* Due to bug #2491 *)
(** Interestingly, most of the development works fine if this is defined as
  ∀ x, f x = g x.
However, in the end that version was just not strong enough for comfortable rewriting
in setoid-pervasive contexts. *)

Definition sig_equiv `{Equiv A} (P: A → Prop) : Equiv (sig P) := λ x y, `x = `y.
Hint Extern 10 (Equiv (sig _)) => apply @sig_equiv : typeclass_instances.

Definition sigT_equiv `{Equiv A} (P: A → Type) : Equiv (sigT P) := λ a b, projT1 a = projT1 b.
Hint Extern 10 (Equiv (sigT _)) => apply @sigT_equiv : typeclass_instances.

Definition sig_apart `{Apart A} (P: A → Prop) : Equiv (sig P) := λ x y, `x ≶ `y.
Hint Extern 10 (Apart (sig _)) => apply @sig_apart : typeclass_instances.

Class Cast A B := cast: A → B.
Implicit Arguments cast [[Cast]].
Notation "' x" := (cast _ _ x) (at level 20).
Instance: Params (@cast) 3.
Typeclasses Transparent Cast.

(* Other canonically named relations/operations/constants: *)
Class SgOp A := sg_op: A → A → A.
Class MonUnit A := mon_unit: A.
Class Plus A := plus: A → A → A.
Class Mult A := mult: A → A → A.
Class One A := one: A.
Class Zero A := zero: A.
Class Negate A := negate: A → A.
Class DecRecip A := dec_recip: A → A.
Definition ApartZero R `{Zero R} `{Apart R} := sig (≶ zero).
Class Recip A `{Apart A} `{Zero A} := recip: ApartZero A → A.
Typeclasses Transparent SgOp MonUnit Plus Mult Zero One Negate.

Class Meet A := meet: A → A → A.
Class Join A := join: A → A → A.
Class Top A := top: A.
Class Bottom A := bottom: A.
Typeclasses Transparent Meet Join Top Bottom.

Class Contains A B := contains: A → B → Prop.
Class Singleton A B := singleton: A → B.
Class Difference A := difference : A → A → A.
Typeclasses Transparent Contains Singleton Difference.

Class Le A := le: relation A.
Class Lt A := lt: relation A.
Typeclasses Transparent Le Lt.

Definition NonNeg R `{Zero R} `{Le R} := sig (le zero).
Definition Pos R `{Zero R} `{Equiv R} `{Lt R} := sig (lt zero).
Definition NonPos R `{Zero R} `{Le R} := sig (λ y, le y zero).
Inductive PosInf (R : Type) : Type := finite (x : R) | infinite.

Class Arrows (O: Type): Type := Arrow: O → O → Type.
Typeclasses Transparent Arrows. (* Ideally this should be removed *)

Infix "⟶" := Arrow (at level 90, right associativity).
Class CatId O `{Arrows O} := cat_id: ∀ x, x ⟶ x.
Class CatComp O `{Arrows O} := comp: ∀ x y z, (y ⟶ z) → (x ⟶ y) → (x ⟶ z).
Class RalgebraAction A B := ralgebra_action: A → B → B.

Implicit Arguments cat_id [[O] [H] [CatId] [x]].
Implicit Arguments comp [[O] [H] [CatComp]].

Instance: Params (@mult) 2.
Instance: Params (@plus) 2.
Instance: Params (@negate) 2.
Instance: Params (@equiv) 2.
Instance: Params (@apart) 2.
Instance: Params (@le) 2.
Instance: Params (@lt) 2.
Instance: Params (@recip) 4.
Instance: Params (@dec_recip) 2.
Instance: Params (@meet) 2.
Instance: Params (@join) 2.
Instance: Params (@contains) 3.
Instance: Params (@singleton) 3.
Instance: Params (@difference) 2.

Instance plus_is_sg_op `{f : Plus A} : SgOp A := f.
Instance mult_is_sg_op `{f : Mult A} : SgOp A := f.
Instance one_is_mon_unit `{c : One A} : MonUnit A := c.
Instance zero_is_mon_unit `{c : Zero A} : MonUnit A := c.
Instance meet_is_sg_op `{f : Meet A} : SgOp A := f.
Instance join_is_sg_op `{f : Join A} : SgOp A := f.
Instance top_is_mon_unit `{s : Top A} : MonUnit A := s.
Instance bottom_is_mon_unit `{s : Bottom A} : MonUnit A := s.
Instance singleton_is_cast `{s : Singleton A B} : Cast A B := s.

Hint Extern 10 (Equiv (_ ⟶ _)) => apply @ext_equiv : typeclass_instances.
Hint Extern 4 (Equiv (ApartZero _)) => apply @sig_equiv : typeclass_instances.
Hint Extern 4 (Equiv (NonNeg _)) => apply @sig_equiv : typeclass_instances.
Hint Extern 4 (Equiv (Pos _)) => apply @sig_equiv : typeclass_instances.
Hint Extern 4 (Equiv (PosInf _)) => apply @sig_equiv : typeclass_instances.
Hint Extern 4 (Apart (ApartZero _)) => apply @sig_apart : typeclass_instances.
Hint Extern 4 (Apart (NonNeg _)) => apply @sig_apart : typeclass_instances.
Hint Extern 4 (Apart (Pos _)) => apply @sig_apart : typeclass_instances.
Hint Extern 4 (Apart (PosInf _)) => apply @sig_apart : typeclass_instances.

(* Notations: *)
Notation "R ₀" := (ApartZero R) (at level 20, no associativity).
Notation "R ⁺" := (NonNeg R) (at level 20, no associativity).
Notation "R ₊" := (Pos R) (at level 20, no associativity).
Notation "R ⁻" := (NonPos R) (at level 20, no associativity).
Notation "R ∞" := (PosInf R) (at level 20, no associativity).
Notation "x ↾ p" := (exist _ x p) (at level 20).

Infix "&" := sg_op (at level 50, left associativity).
Notation "(&)" := sg_op (only parsing).
Notation "( x &)" := (sg_op x) (only parsing).
Notation "(& x )" := (λ y, y & x) (only parsing).

Infix "+" := plus.
Notation "(+)" := plus (only parsing).
Notation "( x +)" := (plus x) (only parsing).
Notation "(+ x )" := (λ y, y + x) (only parsing).

Infix "*" := mult.
(* We don't add "( * )", "( * x )" and "( x * )" notations because they conflict with comments. *)
Notation "( x *.)" := (mult x) (only parsing).
Notation "(.*.)" := mult (only parsing).
Notation "(.* x )" := (λ y, y * x) (only parsing).

Notation "- x" := (negate x).
Notation "(-)" := negate (only parsing).
Notation "x - y" := (x + -y).

Notation "0" := zero.
Notation "1" := one.
Notation "2" := (1 + 1).
Notation "3" := (1 + (1 + 1)).
Notation "4" := (1 + (1 + (1 + 1))).
Notation "- 1" := (-(1)).
Notation "- 2" := (-(2)).
Notation "- 3" := (-(3)).
Notation "- 4" := (-(4)).

Notation "/ x" := (dec_recip x).
Notation "(/)" := dec_recip (only parsing).
Notation "x / y" := (x * /y).

Notation "// x" := (recip x) (at level 35, right associativity).
Notation "(//)" := recip (only parsing).
Notation "x // y" := (x * //y) (at level 35, right associativity).

Notation "⊤" := top.
Notation "⊥" := bottom.

Infix "⊓" := meet (at level 50, no associativity).
Notation "(⊓)" := meet (only parsing).
Notation "( X ⊓)" := (meet X) (only parsing).
Notation "(⊓ X )" := (λ Y, Y ⊓ X) (only parsing).

Infix "⊔" := join (at level 50, no associativity).
Notation "(⊔)" := join (only parsing).
Notation "( X ⊔)" := (join X) (only parsing).
Notation "(⊔ X )" := (λ Y, Y ⊔ X) (only parsing).

Infix "≤" := le.
Notation "(≤)" := le (only parsing).
Notation "( x ≤)" := (le x) (only parsing).
Notation "(≤ x )" := (λ y, y ≤ x) (only parsing).

Infix "<" := lt.
Notation "(<)" := lt (only parsing).
Notation "( x <)" := (lt x) (only parsing).
Notation "(< x )" := (λ y, y < x) (only parsing).

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) (at level 70, y at next level).

Infix "∖" := difference (at level 35).
Notation "(∖)" := difference (only parsing).
Notation "( X ∖)" := (difference X) (only parsing).
Notation "(∖ X )" := (λ Y, Y ∖ X) (only parsing).

Infix "∈" := contains (at level 70, no associativity).
Notation "(∈)" := contains (only parsing).
Notation "( x ∈)" := (contains x) (only parsing).
Notation "(∈ X )" := (λ x, x ∈ X) (only parsing).

Notation "x ∉ y" := (¬x ∈ y) (at level 70, no associativity).
Notation "(∉)" := (λ x X, x ∉ X).
Notation "( x ∉)" := (λ X, x ∉ X) (only parsing).
Notation "(∉ X )" := (λ x, x ∉ X) (only parsing).

Notation "{{ x }}" := (singleton x).
Notation "{{ x ; y ; .. ; z }}" := (join .. (join (singleton x) (singleton y)) .. (singleton z)).

Infix "◎" := (comp _ _ _) (at level 40, left associativity).
  (* Taking over ∘ is just a little too zealous at this point. With our current
   approach, it would require changing all (nondependent) function types A → B
   with A ⟶ B to make them use the canonical name for arrows, which is
   a tad extreme. *)
Notation "(◎)" := (comp _ _ _) (only parsing).
Notation "( f ◎)" := (comp _ _ _ f) (only parsing).
Notation "(◎ f )" := (λ g, comp _ _ _ g f) (only parsing).

(* Haskell style! *)
Notation "(→)" := (λ x y, x → y).
Notation "t $ r" := (t r) (at level 65, right associativity, only parsing).
Notation "(∘)" := compose (only parsing).

(* Agda style! *)
Require Import Streams.
Notation "∞ X" := (Stream X) (at level 23).
Infix ":::" := Cons (at level 60, right associativity).
Notation "(:::)" := Cons (only parsing).
Notation "(::: X )" := (λ x, Cons x X) (only parsing).
Notation "( x :::)" := (Cons x) (only parsing).

Class Abs A `{Equiv A} `{Le A} `{Zero A} `{Negate A} := abs_sig: ∀ (x : A), { y : A | (0 ≤ x → y = x) ∧ (x ≤ 0 → y = -x)}.
Definition abs `{Abs A} := λ x : A, ` (abs_sig x).
Instance: Params (@abs_sig) 6.
Instance: Params (@abs) 6.

(* Common properties: *)
Class Inverse `(A → B) : Type := inverse: B → A.
Implicit Arguments inverse [[A] [B] [Inverse]].
Typeclasses Transparent Inverse.
Notation "f ⁻¹" := (inverse f) (at level 30).

Class Idempotent `{ea : Equiv A} (f: A → A → A) (x : A) : Prop := idempotency: f x x = x.
Implicit Arguments idempotency [[A] [ea] [Idempotent]].

Class UnaryIdempotent `{Equiv A} (f: A → A) : Prop := unary_idempotent :> Idempotent (∘) f.
Lemma unary_idempotency `{Equiv A} `{!Reflexive (=)} `{!UnaryIdempotent f} x : f (f x) = f x.
Proof. firstorder. Qed.

Class BinaryIdempotent `{Equiv A} (op: A → A → A) : Prop := binary_idempotent :> ∀ x, Idempotent op x.

Class LeftIdentity {A} `{Equiv B} (op : A → B → B) (x : A): Prop := left_identity: ∀ y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op : A → B → A) (y : B): Prop := right_identity: ∀ x, op x y = x.

Class Absorption `{Equiv A} {B} {C} (op1: A → C → A) (op2: A → B → C) : Prop := absorption: ∀ x y, op1 x (op2 x y) = x.

Class LeftAbsorb `{Equiv A} {B} (op : A → B → A) (x : A): Prop := left_absorb: ∀ y, op x y = x.
Class RightAbsorb {A} `{Equiv B} (op : A → B → B) (y : B): Prop := right_absorb: ∀ x, op x y = y.

Class LeftInverse {A} {B} `{Equiv C} (op : A → B → C) (inv : B → A) (unit : C) := left_inverse: ∀ x, op (inv x) x = unit.
Class RightInverse {A} {B} `{Equiv C} (op : A → B → C) (inv : A → B) (unit : C) := right_inverse: ∀ x, op x (inv x) = unit.

Class Commutative `{Equiv B} `(f : A → A → B) : Prop := commutativity: ∀ x y, f x y = f y x.

Class HeteroAssociative {A B C AB BC} `{Equiv ABC}
     (fA_BC: A → BC → ABC) (fBC: B → C → BC) (fAB_C: AB → C → ABC) (fAB : A → B → AB): Prop
   := associativity : ∀ x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative `{Equiv A} f := simple_associativity:> HeteroAssociative f f f f.
Notation ArrowsAssociative C := (∀ {w x y z: C}, HeteroAssociative (◎) (comp z _ _ ) (◎) (comp y x w)).

Class Involutive `{Equiv A} (f : A → A) := involutive: ∀ x, f (f x) = x.

Class TotalRelation `(R : relation A) : Prop := total : ∀ x y : A, R x y ∨ R y x.
Implicit Arguments total [[A] [TotalRelation]].

Class Trichotomy `{Ae : Equiv A} `(R : relation A) := trichotomy : ∀ x y : A, R x y ∨ x = y ∨ R y x.
Implicit Arguments trichotomy [[Ae] [A] [Trichotomy]].

Implicit Arguments irreflexivity [[A] [Irreflexive]].
Class CoTransitive `(R : relation A) : Prop := cotransitive : ∀ x y, R x y → ∀ z, R x z ∨ R z y.
Implicit Arguments cotransitive [[A] [R] [CoTransitive] [x] [y]].

Class AntiSymmetric `{Ae : Equiv A} (R : relation A) : Prop := antisymmetry: ∀ x y, R x y → R y x → x = y.
Implicit Arguments antisymmetry [[A] [Ae] [AntiSymmetric]].

Class LeftHeteroDistribute {A B} `{Equiv C} (f : A → B → C) (g_r : B → B → B) (g : C → C → C) : Prop
  := distribute_l : ∀ a b c, f a (g_r b c) = g (f a b) (f a c).
Class RightHeteroDistribute {A B} `{Equiv C} (f : A → B → C) (g_l : A → A → A) (g : C → C → C) : Prop
  := distribute_r: ∀ a b c, f (g_l a b) c = g (f a c) (f b c).
Class LeftDistribute`{Equiv A} (f g: A → A → A) := simple_distribute_l :> LeftHeteroDistribute f g g.
Class RightDistribute `{Equiv A} (f g: A → A → A) := simple_distribute_r :> RightHeteroDistribute f g g.

Class HeteroSymmetric {A} {T : A → A → Type} (R : ∀ {x y}, T x y → T y x → Prop) : Prop :=
  hetero_symmetric `(a : T x y) (b : T y x) : R a b → R b a.

(* Although cancellation is the same as being injective, we want a proper
  name to refer to this commonly used property. *)
Section cancellation.
  Context `{Ae : Equiv A} `{Aap : Apart A} (op : A → A → A) (z : A).

  Class LeftCancellation := left_cancellation : ∀ x y, op z x = op z y → x = y.
  Class RightCancellation := right_cancellation : ∀ x y, op x z = op y z → x = y.

  Class StrongLeftCancellation := strong_left_cancellation : ∀ x y, x ≶ y → op z x ≶ op z y.
  Class StrongRightCancellation := strong_right_cancellation : ∀ x y, x ≶ y → op x z ≶ op y z.
End cancellation.

(* Common names for properties that hold in N, Z, Q, ... *)
Class ZeroProduct A `{Equiv A} `{!Mult A} `{!Zero A} : Prop
  := zero_product : ∀ x y, x * y = 0 → x = 0 ∨ y = 0.

Class ZeroDivisor {R} `{Equiv R} `{Zero R} `{Mult R} (x : R) : Prop
  := zero_divisor : x ≠ 0 ∧ ∃ y, y ≠ 0 ∧ x * y = 0.

Class NoZeroDivisors R `{Equiv R} `{Zero R} `{Mult R} : Prop
  := no_zero_divisors x : ¬ZeroDivisor x.

Instance zero_product_no_zero_divisors `{ZeroProduct A} : NoZeroDivisors A.
Proof. intros x [? [? [? E]]]. destruct (zero_product _ _ E); intuition. Qed.

Class RingUnit `{Equiv R} `{Mult R} `{One R} (x : R) : Prop
  := ring_unit : ∃ y, x * y = 1.

(* A common induction principle for both the naturals and integers *)
Class Biinduction R `{Equiv R} `{Zero R} `{One R} `{Plus R} : Prop
  := biinduction (P : R → Prop) `{!Proper ((=) ==> iff) P} : P 0 → (∀ n, P n ↔ P (1 + n)) → ∀ n, P n.
