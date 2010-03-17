Set Automatic Introduction.

Require Import
  Relation_Definitions Morphisms Setoid Program canonical_names Basics.

Section Bijective2wBijective.

Context `{f:A→ B}`{Bijective _ _ f}.

Instance naam: Inv f := fun b => projT1 (bijective_surjective b).

Instance: BijectiveInv f.
 constructor.
  intro.
  change (projT1 (bijective_surjective (f x)) = x).
  set (bijective_surjective (f x)).
  destruct s. (* todo: this is silly *)
  firstorder.
 intro.
 change (f (projT1 (bijective_surjective x)) = x).
 set (bijective_surjective x).
 destruct s. (* todo: this is silly *)
 firstorder.
Qed.

End Bijective2wBijective.

Section andersom.

Context `{f:A→ B}`{BijectiveInv _ _ f}.

Instance: Bijective f.
 constructor.
  repeat intro.
  destruct H.
  pose proof (inv_r (f x)) .
  unfold id in H1.
  rewrite <- H1 in H0.

  simpl in H1.
  Check (finv0 x).


Require Export categories.
(** We prove that the two definitions of adjunction are equivalent.*)

Section Bijective2wBijective.
Class SurjectiveT {A} `{Equiv B} (f: A → B): Type := surjective: Π x: B, sigT (λ y => f y = x).

Class wBijective `{ea: Equiv A} `{eb: Equiv B} (f: A → B): Type :=
  { wbijective_injective:> Injective f
  ; wbijective_surjective:> SurjectiveT f }.

Context `{f:A→ B}`{wBijective _ _ f}.
Definition my_inverse: B → A.
intro b.
destruct (wbijective_surjective b) as [a _].
exact a.
Defined.


(*
Class Bijective' `{ea: Equiv A} `{eb: Equiv B} (f: A → B) (inv: B  → A): Prop :=
  { finv: inv ∘  f = id
  ; invf: f ∘  inv = id}.

Implicit Arguments Bijective' [[inv]].
*)


End Bijective2wBijective.