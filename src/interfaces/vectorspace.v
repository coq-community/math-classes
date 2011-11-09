Require Import 
  Morphisms abstract_algebra interfaces.orders.

(** Scalar multiplication function class *)
Class ScalarMult F G := scalar_mult: F → G → G.
Instance: Params (@scalar_mult) 3.

Infix "·" := scalar_mult (at level 50).
Notation "(·)" := scalar_mult (only parsing).
Notation "( x ·)" := (scalar_mult x) (only parsing).
Notation "(· x )" := (λ y, y · x) (only parsing).

(** The inproduct function class *)
Class Inproduct K V := inprod : V → V → K.
Instance: Params (@inprod) 3.

Notation "⟨ u , v ⟩" := (inprod u v) (at level 50).
Notation "x ⊥ y" := (⟨x,y⟩ = 0) (at level 70).

(* The norm function class *)
Class Norm V K := norm : V → K.
Instance: Params (@norm) 2.

Notation "∥ L ∥" := (norm L) (at level 50).
Notation "∥·∥" := norm (only parsing).

(** Vectorspace with scalars F *)
Class VectorSpace (F G : Type) {Fe Fplus Fmult Fzero Fone Fnegate Frecip}
     {Ge Gop Gunit Gnegate} {sm : ScalarMult F G} := {
  vs_field :> @DecField F Fe Fplus Fmult Fzero Fone Fnegate Frecip ;
  vs_abgroup :> @AbGroup G Ge Gop Gunit Gnegate ;
  vs_distr_l :> LeftHeteroDistribute (·) (&) (&) ;
  vs_distr_r :> RightHeteroDistribute (·) (+) (&) ;
  vs_assoc :> HeteroAssociative (·) (·) (·) (.*.) ;
  vs_left_identity :> LeftIdentity (·) 1 
}.

Section spaces.

Context K V `{VectorSpace K V}.

(** Given some vector space V over a ordered field K,
  we define the inner product space *)

Class InnerProductSpace `{Kle: Le K} (ip: Inproduct K V) :=
  { in_vectorspace :> VectorSpace K V
  ; in_srorder     :> SemiRingOrder Kle
  ; in_comm        :> Commutative inprod
  ; in_linear_l    :  ∀ a u v, ⟨a·u,v⟩ = a*⟨u,v⟩
  ; in_nonneg      :> ∀ v, PropHolds (0 ≤ ⟨v,v⟩) (* TODO Le to strong? *)
  }.

(*
 (* TODO complex conjugate? *)
 Section proof_in_linear_r.
 Context `{InnerProductSpace}.
 Lemma in_linear_r a u v : ⟨u,a·v⟩ = a*⟨u,v⟩.
 Proof. rewrite !(commutativity u). apply in_linear_l. Qed.
 End proof_in_linear_r.
*)

 Class  SemiNormedSpace `{Abs K} `(n: @Norm V K) :=
  { sn_vectorspace :> VectorSpace K V
  ; sn_scale       :  ∀ a v, ∥ a · v ∥ = (abs a) * ∥ v ∥   (* positive homgeneity *)
  ; sn_triangle    :  ∀ u v, ∥ u & v ∥ = ∥ u ∥ + ∥ v ∥     (* triangle inequality *)
  }.

(*
 Class NormedSpace `{Abs K} `(n: @Norm V K) :=
  { norm_semi :> SemiNormedSpace n
  ; norm_separates : ∀ (v:V), ∥v∥ = 0 ↔ v = unit.
  }.
*)

End spaces.