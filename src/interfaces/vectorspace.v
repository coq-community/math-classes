Require Import 
  Morphisms abstract_algebra.

Class ScalarMult F G := scalar_mult: F → G → G.
Instance: Params (@scalar_mult) 3.

Infix "·" := scalar_mult (at level 50).
Notation "(·)" := scalar_mult (only parsing).
Notation "( x ·)" := (scalar_mult x) (only parsing).
Notation "(· x )" := (λ y, y · x) (only parsing).

Class VectorSpace (F G : Type) {eF plusF multF zeroF oneF oppF invF}
     {eG opG unitG invG} {sm : ScalarMult F G} := {
  vs_field :> @Field F eF plusF multF zeroF oneF oppF invF ;
  vs_abgroup :> @AbGroup G eG opG unitG invG ;
  vs_distr_l :> LeftHeteroDistribute (·) (&) (&) ;
  vs_distr_r :> RightHeteroDistribute (·) (+) (&) ;
  vs_assoc :> HeteroAssociative (·) (·) (·) (.*.) ;
  vs_left_identity :> LeftIdentity (·) 1 
}.

