Require Import 
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.

(** Scalar multiplication function class *)
Class ScalarMult K V := scalar_mult: K → V → V.
Instance: Params (@scalar_mult) 3.

Infix "·" := scalar_mult (at level 50) : mc_scope.
Notation "(·)" := scalar_mult (only parsing) : mc_scope.
Notation "( x ·)" := (scalar_mult x) (only parsing) : mc_scope.
Notation "(· x )" := (λ y, y · x) (only parsing) : mc_scope.

(** The inproduct function class *)
Class Inproduct K V := inprod : V → V → K.
Instance: Params (@inprod) 3.

Notation "⟨ u , v ⟩" := (inprod u v) (at level 51) : mc_scope.
Notation "⟨ u , ⟩" := (λ v, ⟨u,v⟩) (at level 50, only parsing) : mc_scope.
Notation "⟨ , v ⟩" := (λ u, ⟨u,v⟩) (at level 50, only parsing) : mc_scope.
Notation "x ⊥ y" := (⟨x,y⟩ = 0) (at level 70) : mc_scope.

(** The norm function class *)
Class Norm K V := norm : V → K.
Instance: Params (@norm) 2.

Notation "∥ L ∥" := (norm L) (at level 50) : mc_scope.
Notation "∥·∥" := norm (only parsing) : mc_scope.

(** Let [M] be an R-Module. *)
Class Module (R M : Type)
  {Re Rplus Rmult Rzero Rone Rnegate}
  {Me Mop Munit Mnegate}
  {sm : ScalarMult R M}
:=
  { lm_ring     :>> @Ring R Re Rplus Rmult Rzero Rone Rnegate
  ; lm_group    :>> @AbGroup M Me Mop Munit Mnegate
  ; lm_distr_l  :> LeftHeteroDistribute (·) (&) (&)
  ; lm_distr_r  :> RightHeteroDistribute (·) (+) (&)
  ; lm_assoc    :> HeteroAssociative (·) (·) (·) (.*.)
  ; lm_identity :> LeftIdentity (·) 1
  }.

(* TODO K is commutative, so derive right module laws? *)

(** A module with a seminorm. *)
Class Seminormed
  {R Re Rplus Rmult Rzero Rone Rnegate Rle Rlt Rapart}
  {M Me Mop Munit Mnegate Smult}
 `{!Abs R} (n : Norm R M)
:=
  (* We have a module *)
  { snm_module      :>> @Module R M Re Rplus Rmult Rzero Rone Rnegate
                                  Me Mop Munit Mnegate Smult
  ; snm_order       :>> @FullPseudoSemiRingOrder R Re Rapart Rplus Rmult Rzero Rone Rle Rlt

  (* With respect to which our norm preserves the following: *)
  ; snm_scale       :  ∀ a v, ∥a · v∥ = (abs a) * ∥v∥   (* positive homgeneity *)
  ; snm_triangle    :  ∀ u v, ∥u & v∥ = ∥u∥ + ∥v∥     (* triangle inequality *)
  }.


(** A Vector space: This class says that [K] is the field
    of scalars, [V] the abelian group of vectors and together
    with the scalar multiplication they satisfy the laws
    of a vector space
*)
Class VectorSpace (K V : Type)
   {Ke Kplus Kmult Kzero Kone Knegate Krecip} (* scalar operations *)
   {Ve Vop Vunit Vnegate}                     (* vector operations *)
   {sm : ScalarMult K V}
 :=
   { vs_field         :>> @DecField K Ke Kplus Kmult Kzero Kone Knegate Krecip
   ; vs_abgroup       :>> @AbGroup V Ve Vop Vunit Vnegate
   ; vs_distr_l       :> LeftHeteroDistribute (·) (&) (&)
   ; vs_distr_r       :> RightHeteroDistribute (·) (+) (&)
   ; vs_assoc         :> HeteroAssociative (·) (·) (·) (.*.)
   ; vs_left_identity :> LeftIdentity (·) 1
   }.

(** Every vectorspace is trivially a module
*)
Instance vs_module `{VectorSpace K V}: Module K V.
Proof. repeat split; apply _. Qed.

(** Given some vector space V over a ordered field K,
  we define the inner product space
*)
Class InnerProductSpace (K V : Type)
   {Ke Kplus Kmult Kzero Kone Knegate Krecip} (* scalar operations *)
   {Ve Vop Vunit Vnegate}                     (* vector operations *)
   {sm : ScalarMult K V} {inp: Inproduct K V} {Kle: Le K}
 :=
   { in_vectorspace :>> @VectorSpace K V Ke Kplus Kmult Kzero Kone Knegate
                                    Krecip Ve Vop Vunit Vnegate sm
   ; in_srorder     :>> SemiRingOrder Kle
   ; in_comm        :> Commutative inprod
   ; in_linear_l    :  ∀ a u v, ⟨a·u,v⟩ = a*⟨u,v⟩
   ; in_nonneg      :> ∀ v, PropHolds (0 ≤ ⟨v,v⟩) (* TODO Le to strong? *)
   }.

(* TODO complex conjugate?
 Section proof_in_linear_r.
 Context `{InnerProductSpace}.
 Lemma in_linear_r a u v : ⟨u,a·v⟩ = a*⟨u,v⟩.
 Proof. rewrite !(commutativity u). apply in_linear_l. Qed.
 End proof_in_linear_r.
*)

(* This is probably a bad idea? (because ∣ ≠ |)
   Notation "∣ a ∣" := (abs a).
*)

Class SemiNormedSpace (K V : Type)
  `{a:Abs K} `{n : @Norm K V}                 (* scalar and vector norms *)
   {Ke Kplus Kmult Kzero Kone Knegate Krecip} (* scalar operations *)
   {Ve Vop Vunit Vnegate}                     (* vector operations *)
   {sm : ScalarMult K V}
 :=
   { sn_vectorspace :>> @VectorSpace K V Ke Kplus Kmult Kzero Kone Knegate
                                    Krecip Ve Vop Vunit Vnegate sm
   ; sn_scale       :  ∀ a v, ∥a · v∥ = (abs a) * ∥v∥   (* positive homgeneity *)
   ; sn_triangle    :  ∀ u v, ∥u & v∥ = ∥u∥ + ∥v∥     (* triangle inequality *)
   }.


(* For normed spaces:
   n_separates : ∀ (v:V), ∥v∥ = 0 ↔ v = unit
*)

(* - Induced metric:    d x y := ∥ x - y ∥

   - Induced norm. If the metric is

      1). translation invariant: d x y = d (x + a) (y + a)
      2). and homogeneous: d (α * x) (α * y) = ∣α∣ * (d x y)
     
     then we can define the norm as:
       
        ∥ x ∥ := d 0 x

   - Same for seminorm
*)