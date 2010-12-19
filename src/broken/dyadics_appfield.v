Require Import
  Morphisms Ring Program RelationClasses
  abstract_algebra interfaces.integers interfaces.naturals interfaces.rationals 
  interfaces.additional_operations interfaces.appfield
  positive_integers_naturals dyadics.

Inductive rounding_mode := rounddown | roundup.

Section dyadics_appfield.
  Context `{Integers Z}.
 
  Let mode := roundup.
  Let N:=Pos Z.

  Context `{equiv_dec : ∀ (x y : Z), Decision (x = y)}  
    `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)}
    `{!NatPow Z N} 
    `{!ShiftLeft Z N} 
    `{!DivEuclid Z}
    `{!ShiftRight Z N}
    `{!Log (2:Z) N}
    `{!RingMinus Z}.
  
  Definition shift_with_round (x : Z) (k : N) : Z := 
    let y : Z := x ≫ k in
    match mode with
    | rounddown => if decide (0 ≤ y) then y else y + 1
    | roundup =>if decide (0 ≤ y) then y + 1 else y
    end.

  Program Definition log2_int (x : Z) : N := 
    if decide (x = 0) then 0 
    else if decide (0 ≤ x) then log (2:Z) x else log (2:Z) (-x).
  Next Obligation. 
    split. assumption. 
    apply not_symmetry. assumption. 
  Qed.
  
  Next Obligation with auto. 
    split. 
    apply semiring.sr_precedes_0_flip. rewrite rings.inv_involutive. apply orders.precedes_flip... 
    apply not_symmetry... intro E. rewrite <-rings.opp_0 in E. apply (injective group_inv) in E...
  Qed.

  (* Using cut_minus here is silly because we always have j > ε. *)
  Program Definition normalize (x : Dyadic Z) (ε : N) : Dyadic Z := 
    let j : N := log2_int (mant x) in
    if decide (j ≤ ε) then x
    else shift_with_round (mant x) (j ∸ ε) $ expo x + (j ∸ ε).

  Global Instance: AppRingPlus (Dyadic Z) N := λ x y, normalize (x + y).
  Global Instance: AppRingMult (Dyadic Z) N := λ x y, normalize (x * y).
  Global Instance: AppGroupInv (Dyadic Z) N := λ x, normalize (-x).

  Global Program Instance: AppMultInv (Dyadic Z) N := λ x ε, 
    let j : N := log2_int (mant x) in
    let r := match mode with rounddown => 0 | roundup => 1 end in
    div_euclid (r + (1 ≪ (ε + j))) (mant x) $ -(j + ε + (expo x)).
  Next Obligation. apply nonzero_mant. assumption. Qed.
  
  Context `{Rationals Q} 
    `{!Ring_Morphism (ZtoQ : Z → Q)}
    `{QtoZPair : !Inverse (λ p, ZtoQ (fst p) * / ZtoQ (snd p))}
    `{!Surjective (λ p, ZtoQ (fst p) * / ZtoQ (snd p))}.
  
  Program Definition QtoD (q : Q) (ε : N) := 
    let p := QtoZPair q in
    if decide (snd p = 0) then 0
    else (fst p $ 0) * ((///(snd p $ 0)) ε).
  Next Obligation. apply nonzero_mant. simpl. assumption. Qed.

End dyadics_appfield.
