Require Import 
  Relation_Definitions
  Morphisms
  abstract_algebra
  canonical_names
  interfaces.integers
  interfaces.rationals.

(* Move to a separate module *)
Class Ball A B := ball : B → relation A.
Notation "x ≈ y | ε" := (ball ε x y) (at level 70).

Section metric.
  Context A B {eA : Equiv A} `{Monoid B} `{!Ball A B}.

  Class HemiMetric : Prop := {
    m_setoid :> Setoid A ;
    m_proper :> Proper ((=) ==> (=) ==> (=) ==> iff) (_ : Ball A B) ;
    m_refl :> `(Reflexive (ball ε));
    m_triangle : `(x ≈ y | ε1 → y ≈ z | ε2 → x ≈ z | ε1 & ε2) ;
    m_closed : `((∀ δ, x ≈ y | ε & δ) → x ≈ y | ε) ;
    m_eq : `((∀ ε, x ≈ y | ε) → x = y)
  }.

  Context {metric : HemiMetric}.

  Lemma metric1 ε δ x y : x ≈ y | ε → x ≈ y | ε & δ.
  Proof with auto.
    intros D. 
    eapply m_triangle. apply D. apply m_refl.
  Qed.
End metric.

Class AppRingPlus A B := app_ring_plus: A → A → B → A.
Class AppRingMult A B := app_ring_mult: A → A → B → A.
Class AppGroupInv A B := app_group_inv: A → B → A.
Class AppMultInv A B `{Equiv A} `{RingZero A} := 
  app_mult_inv: { x: A | x ≠ ring_zero } → B → A.

Infix "✚" := app_ring_plus (at level 50).
Infix "✖" := app_ring_mult (at level 70).
Notation "▬ x" := (app_group_inv x) (at level 70).
Notation "/// x" := (app_mult_inv x) (at level 70). (* I'm unable to find a bold unicode / :( *)

Section approximate_field.

  Context A B `{Monoid B} {eA : Equiv A}.
  Context {a_plus : AppRingPlus A B} {a_mult : AppRingMult A B} 
    {a_zero : RingZero A} {a_one : RingOne A} 
    {a_inv : AppGroupInv A B} {a_mult_inv : AppMultInv A B}.
  Context `{Field R} {ball : Ball R B} {metric : HemiMetric R B}.
  Context {f : A → R} `{!Setoid_Morphism f} { preserves_zero : ∀ x , f x = 0 → x = 0 }
    {g : R → B → A} {gproper : Proper ((=) ==> (=) ==> (=)) g}.
  
  Program Definition app_mult_inv_spec' ε x (H : f 0 = 0) := f ((/// x) ε) ≈ // (f x) | ε.

  Class AppField : Prop := {
     app_spec : `(f (g x ε) ≈ x | ε) ;
     app_plus_spec : `(f ((x ✚ y) ε) ≈ f x + f y | ε) ;
     app_mult_spec : `(f ((x ✖ y) ε) ≈ f x * f y | ε) ;
     app_zero_spec : f 0 = 0 ;
     app_one_spec : f 1 = 1 ;
     app_inv_spec : `(f ((▬x) ε) ≈ -f x | ε) ;
     app_mult_inv_spec : `(app_mult_inv_spec' ε x app_zero_spec)
  }.

  Class Normalize := normalize_sig x ε : { z | z = f (g x ε) }.
  Global Program Instance: Normalize | 10 := {
    normalize_sig := λ x ε,  f (g x ε) 
  }.
  Next Obligation. apply reflexivity. Qed.
  Definition normalize x ε := proj1_sig (normalize_sig x ε).

End approximate_field.
