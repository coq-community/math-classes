Require Import 
  Morphisms abstract_algebra.

Class ScalarMult F G := scalar_mult: F → G → G.
Instance: Params (@scalar_mult) 3.

Infix "·" := scalar_mult (at level 50).
Notation "(·)" := scalar_mult (only parsing).
Notation "( x ·)" := (scalar_mult x) (only parsing).
Notation "(· x )" := (λ y, y · x) (only parsing).

Class VectorSpace (F G : Type) {Fe Fplus Fmult Fzero Fone Fnegate Frecip}
     {Ge Gop Gunit Gnegate} {sm : ScalarMult F G} := {
  vs_field :> @DecField F Fe Fplus Fmult Fzero Fone Fnegate Frecip ;
  vs_abgroup :> @AbGroup G Ge Gop Gunit Gnegate ;
  vs_distr_l :> LeftHeteroDistribute (·) (&) (&) ;
  vs_distr_r :> RightHeteroDistribute (·) (+) (&) ;
  vs_assoc :> HeteroAssociative (·) (·) (·) (.*.) ;
  vs_left_identity :> LeftIdentity (·) 1 
}.
