Require Import Morphisms abstract_algebra.

(* 
In this file we describe interfaces for ordered structures. Since we are in a 
constructive setting we use a pseudo order instead of a total order. Therefore
we also have to include an apartness relation.

Obviously, in case we consider decidable structures these interfaces are quite
inconvenient. Hence we will, later on, provide means to go back and forth
between the usual classical notions and these constructive notions.
 
On the one hand, if we have an ordinary (total) partial order (≤) with a 
corresponding strict order (<), we will prove that we can construct a
StrictPartialOrder and PseudoPartialOrder, respectively.
  
On the other hand, if equality is decidable, we will prove that we have the
usual properties like Trichotomy (<) and TotalRelation (≤).
*)

Class PartialOrder `{e: Equiv A} (o : Le A) : Prop :=
  { po_setoid : Setoid A (* Making this a coercion makes instance search slow *)
  ; po_proper:> Proper ((=) ==> (=) ==> iff) (≤)
  ; po_preorder:> PreOrder (≤)
  ; po_antisym:> AntiSymmetric (≤) }.

(* The strict order from the standard library does not include (=) and thus
  does not require (<) to be Proper. *)
Class StrictSetoidOrder `{e : Equiv A} (o : Lt A) : Prop :=
  { strict_setoid_order_setoid : Setoid A
  ; strict_setoid_order_proper :> Proper ((=) ==> (=) ==> iff) (<)
  ; strict_setoid_order_strict :> StrictOrder (<) }.

(* The constructive notion of a total strict total order. Note that we get Proper (<) 
  from cotransitivity. We will prove that (<) is in fact a StrictSetoidOrder. *)
Class PseudoOrder `{e : Equiv A} `{ap : Apart A} (so : Lt A) : Prop :=
  { pseudo_order_setoid : StrongSetoid A
  ; pseudo_order_antisym : ∀ x y, ¬(x < y ∧ y < x)
  ; pseudo_order_cotrans :> CoTransitive (<) 
  ; apart_iff_total_lt : ∀ x y, x ⪥ y ↔ x < y ∨ y < x }.

(* A partial order (≤) with a corresponding (<). We will prove that (<) is in fact
  a StrictSetoidOrder *)
Class StrictPartialOrder `{e : Equiv A} `{ap : Apart A} (o : Le A) (so : Lt A) : Prop :=
  { strict_po_setoid : StrongSetoid A 
  ; strict_po_po :> PartialOrder (≤)
  ; strict_po_trans :> Transitive (<)
  ; lt_iff_le_apart : ∀ x y, x < y ↔ x ≤ y ∧ x ⪥ y }.

(* A pseudo order (<) with a corresponding (≤). We will prove that (≤) is in fact
  a PartialOrder. *)
Class FullPseudoOrder `{e : Equiv A} `{ap : Apart A} (Ale : Le A) (Alt : Lt A) : Prop :=
  { full_pseudo_order_pseudo :> PseudoOrder Alt 
  ; le_iff_not_lt_flip : ∀ x y, x ≤ y ↔ ¬y < x }.

Section order_maps.
  Context {A B : Type} {Ae: Equiv A} {Ale: Le A} {Alt: Lt A} {Be: Equiv B} {Ble: Le B} {Blt: Lt B} (f : A → B).

  (* An Order_Morphism is just the factoring out of the common parts of 
    OrderPreserving and OrderPreservingBack *)
  Class Order_Morphism := 
    { order_morphism_mor : Setoid_Morphism f
    ; order_morphism_proper_a :> Proper ((=) ==> (=) ==> iff) Ale
    ; order_morphism_proper_b :> Proper ((=) ==> (=) ==> iff) Ble }.

  Class StrictOrder_Morphism := 
    { strict_order_morphism_mor : Setoid_Morphism f
    ; strict_order_morphism_proper_a :> Proper ((=) ==> (=) ==> iff) Alt
    ; strict_order_morphism_proper_b :> Proper ((=) ==> (=) ==> iff) Blt }.

  Class OrderPreserving := 
    { order_preserving_morphism :> Order_Morphism 
    ; order_preserving : `(x ≤ y → f x ≤ f y) }.

  Class OrderPreservingBack := 
    { order_preserving_back_morphism :> Order_Morphism
    ; order_preserving_back : `(f x ≤ f y → x ≤ y) }.

  Class OrderEmbedding := 
    { order_embedding_preserving :> OrderPreserving
    ; order_embedding_back :> OrderPreservingBack }.

  Class OrderIsomorphism `{!Inverse f} := 
    { order_iso_embedding :> OrderEmbedding
    ; order_iso_surjective :> Surjective f }.

  Class StrictlyOrderPreserving := 
    { strictly_order_preserving_morphism :> StrictOrder_Morphism
    ; strictly_order_preserving : `(x < y → f x < f y) }.

  Class StrictlyOrderPreservingBack := 
    { strictly_order_preserving_back_morphism :> StrictOrder_Morphism
    ; strictly_order_preserving_back : `(f x < f y → x < y) }.

  Class StrictOrderEmbedding := 
    { strict_order_embedding_preserving :> StrictlyOrderPreserving
    ; strict_order_embedding_back :> StrictlyOrderPreservingBack }.
End order_maps.

(*
We define various classes to describe the order on the lower part of the
algebraic hierarchy. This results in the notion of a PseudoSemiRingOrder, which 
specifies the order on the naturals, integers, rationals and reals. This notion 
is quite similar to a strictly linearly ordered unital commutative protoring in 
Davorin Lešnik's PhD thesis.
*)
Class SemiRingOrder `{Equiv A} `{RingPlus A} `{RingMult A} 
    `{RingZero A} (Ale : Le A) :=
  { srorder_po :> PartialOrder Ale
  ; srorder_partial_minus : ∀ x y, x ≤ y → ∃ z, y = x + z
  ; srorder_plus :> ∀ z, OrderEmbedding (z +)
  ; nonneg_mult_compat : ∀ x y, PropHolds (0 ≤ x) → PropHolds (0 ≤ y) → PropHolds (0 ≤ x * y) }.

Class StrictSemiRingOrder `{Equiv A} `{RingPlus A} `{RingMult A} 
    `{RingZero A} (Alt : Lt A) :=
  { strict_srorder_so :> StrictSetoidOrder Alt
  ; strict_srorder_partial_minus : ∀ x y, x < y → ∃ z, y = x + z
  ; strict_srorder_plus :> ∀ z, StrictOrderEmbedding (z +)
  ; pos_mult_compat : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y) }.

Class PseudoSemiRingOrder `{Equiv A} `{Apart A} `{RingPlus A} 
    `{RingMult A} `{RingZero A} (Alt : Lt A) :=
  { pseudo_srorder_strict :> PseudoOrder Alt
  ; pseudo_srorder_partial_minus : ∀ x y, ¬y < x → ∃ z, y = x + z
  ; pseudo_srorder_plus :> ∀ z, StrictOrderEmbedding (z +)
  ; pseudo_srorder_mult_ext :> StrongSetoid_BinaryMorphism (.*.)
  ; pseudo_srorder_pos_mult_compat : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) → PropHolds (0 < x * y) }.

Class FullPseudoSemiRingOrder `{Equiv A} `{Apart A} `{RingPlus A} 
    `{RingMult A} `{RingZero A} (Ale : Le A) (Alt : Lt A) :=
  { full_pseudo_srorder_pso :> PseudoSemiRingOrder Alt
  ; full_pseudo_srorder_le_iff_not_lt_flip : ∀ x y, x ≤ y ↔ ¬y < x }.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 < _ * _)) => eapply @pos_mult_compat : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ _ * _)) => eapply @nonneg_mult_compat : typeclass_instances.

(*
Alternatively, we could have defined the standard notion of a RingOrder:

Class RingOrder `{Equiv A} `{RingPlus A} `{RingMult A} `{RingZero A} (Ale : Le A) :=
  { ringorder_po :> PartialOrder Ale
  ; ringorder_plus :> ∀ z, OrderPreserving (z +)
  ; ringorder_mult : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ x * y }.

Unfortunately, this notion is too weak when we consider semirings (e.g. the
naturals). Moreover, in case of rings, we prove that this notion is equivalent 
to our SemiRingOrder class (see orders.rings.from_ring_order). Hence we omit 
defining such a class.

Similarly we prove that a FullSemiRingOrder and a FullPseudoRingOrder are equivalent.

Class FullPseudoRingOrder `{Equiv A} `{Apart A} `{RingPlus A} 
    `{RingMult A} `{RingZero A} (Ale : Le A) (Alt : Lt A) :=
  { pseudo_ringorder_spo :> FullPseudoOrder Ale Alt
  ; pseudo_ringorder_mult_ext :> StrongSetoid_BinaryMorphism (.*.)
  ; pseudo_ringorder_plus :> ∀ z, StrictlyOrderPreserving (z +)
  ; pseudo_ringorder_mult : ∀ x y, 0 < x → 0 < y → 0 < x * y }.
*)
