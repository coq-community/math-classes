Require Import
  abstract_algebra interfaces.orders orders.maps theory.lattices.

(*
We prove that the algebraic definition of a lattice corresponds to the
order theoretic one. Note that we do not make any of these instances global,
because that would cause loops.
*)
Section join_semilattice_order.
  Context `{JoinSemiLatticeOrder L}.

  Instance: Setoid L := po_setoid.

  Lemma join_ub_3_r x y z : z ≤ x ⊔ y ⊔ z.
  Proof. now apply join_ub_r. Qed.
  Lemma join_ub_3_m x y z : y ≤ x ⊔ y ⊔ z.
  Proof. transitivity (x ⊔ y). now apply join_ub_r. now apply join_ub_l. Qed.
  Lemma join_ub_3_l x y z : x ≤ x ⊔ y ⊔ z.
  Proof. transitivity (x ⊔ y); now apply join_ub_l. Qed.

  Lemma join_ub_3_assoc_l x y z : x ≤ x ⊔ (y ⊔ z).
  Proof. now apply join_ub_l. Qed.
  Lemma join_ub_3_assoc_m x y z : y ≤ x ⊔ (y ⊔ z).
  Proof. transitivity (y ⊔ z). now apply join_ub_l. now apply join_ub_r. Qed.
  Lemma join_ub_3_assoc_r x y z : z ≤ x ⊔ (y ⊔ z).
  Proof. transitivity (y ⊔ z); now apply join_ub_r. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) (⊔).
  Proof.
    intros ? ? E1 ? ? E2. apply (antisymmetry (≤)); apply join_lub.
       rewrite E1. now apply join_ub_l.
      rewrite E2. now apply join_ub_r.
     rewrite <-E1. now apply join_ub_l.
    rewrite <-E2. now apply join_ub_r.
  Qed.

  Instance join_sl_order_join_sl: JoinSemiLattice L.
  Proof.
    repeat (split; try apply _).
      intros x y z. apply (antisymmetry (≤)).
       apply join_lub.
        now apply join_ub_3_l.
       apply join_lub. now apply join_ub_3_m. now apply join_ub_3_r.
      apply join_lub.
       apply join_lub. now apply join_ub_3_assoc_l. now apply join_ub_3_assoc_m.
      now apply join_ub_3_assoc_r.
     intros x y. apply (antisymmetry (≤)); apply join_lub; first [apply join_ub_l | try apply join_ub_r].
    intros x. red. apply (antisymmetry (≤)). now apply join_lub. now apply join_ub_l.
  Qed.

  Lemma join_le_compat_r x y z : z ≤ x → z ≤ x ⊔ y.
  Proof. intros E. transitivity x. easy. apply join_ub_l. Qed.
  Lemma join_le_compat_l x y z : z ≤ y → z ≤ x ⊔ y.
  Proof. intros E. rewrite commutativity. now apply join_le_compat_r. Qed.

  Lemma join_l x y : y ≤ x → x ⊔ y = x.
  Proof. intros E. apply (antisymmetry (≤)). now apply join_lub. apply join_ub_l. Qed.
  Lemma join_r x y : x ≤ y → x ⊔ y = y.
  Proof. intros E. rewrite commutativity. now apply join_l. Qed.

  Lemma join_sl_le_spec x y : x ≤ y ↔ x ⊔ y = y.
  Proof. split; intros E. now apply join_r. rewrite <-E. now apply join_ub_l. Qed.

  Global Instance: ∀ z, OrderPreserving (z ⊔).
  Proof.
    intros. repeat (split; try apply _). intros.
    apply join_lub. now apply join_ub_l. now apply  join_le_compat_l.
  Qed.
  Global Instance: ∀ z, OrderPreserving (⊔ z).
  Proof. intros. apply maps.order_preserving_flip. Qed.

  Lemma join_le_compat x₁ x₂ y₁ y₂ : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ ⊔ y₁ ≤ x₂ ⊔ y₂.
  Proof.
    intros E1 E2. transitivity (x₁ ⊔ y₂).
     now apply (order_preserving (x₁ ⊔)).
    now apply (order_preserving (⊔ y₂)).
  Qed.

  Lemma join_le x y z : x ≤ z → y ≤ z → x ⊔ y ≤ z.
  Proof. intros. rewrite <-(idempotency (⊔) z). now apply join_le_compat. Qed.
End join_semilattice_order.

Section bounded_join_semilattice.
  Context `{JoinSemiLatticeOrder L} `{Bottom L} `{!BoundedJoinSemiLattice L}.

  Lemma above_bottom x : ⊥ ≤ x.
  Proof. rewrite join_sl_le_spec. now rewrite left_identity. Qed.

  Lemma below_bottom x : x ≤ ⊥ → x = ⊥.
  Proof. rewrite join_sl_le_spec. now rewrite right_identity. Qed.
End bounded_join_semilattice.

Section meet_semilattice_order.
  Context `{MeetSemiLatticeOrder L}.

  Instance: Setoid L := po_setoid.

  Lemma meet_lb_3_r x y z : x ⊓ y ⊓ z ≤ z.
  Proof. now apply meet_lb_r. Qed.
  Lemma meet_lb_3_m x y z : x ⊓ y ⊓ z ≤ y.
  Proof. transitivity (x ⊓ y). now apply meet_lb_l. now apply meet_lb_r. Qed.
  Lemma meet_lb_3_l x y z : x ⊓ y ⊓ z ≤ x.
  Proof. transitivity (x ⊓ y); now apply meet_lb_l. Qed.

  Lemma meet_lb_3_assoc_l x y z : x ⊓ (y ⊓ z) ≤ x.
  Proof. now apply meet_lb_l. Qed.
  Lemma meet_lb_3_assoc_m x y z : x ⊓ (y ⊓ z) ≤ y.
  Proof. transitivity (y ⊓ z). now apply meet_lb_r. now apply meet_lb_l. Qed.
  Lemma meet_lb_3_assoc_r x y z : x ⊓ (y ⊓ z) ≤ z.
  Proof. transitivity (y ⊓ z); now apply meet_lb_r. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) (⊓).
  Proof.
    intros ? ? E1 ? ? E2. apply (antisymmetry (≤)); apply meet_glb.
       rewrite <-E1. now apply meet_lb_l.
      rewrite <-E2. now apply meet_lb_r.
     rewrite E1. now apply meet_lb_l.
    rewrite E2. now apply meet_lb_r.
  Qed.

  Instance meet_sl_order_meet_sl: MeetSemiLattice L.
  Proof.
    repeat (split; try apply _).
      intros x y z. apply (antisymmetry (≤)).
       apply meet_glb.
        apply meet_glb. now apply meet_lb_3_assoc_l. now apply meet_lb_3_assoc_m.
       now apply meet_lb_3_assoc_r.
      apply meet_glb.
       now apply meet_lb_3_l.
      apply meet_glb. now apply meet_lb_3_m. now apply meet_lb_3_r.
     intros x y. apply (antisymmetry (≤)); apply meet_glb; first [apply meet_lb_l | try apply meet_lb_r].
    intros x. red. apply (antisymmetry (≤)). now apply meet_lb_l. now apply meet_glb.
  Qed.

  Lemma meet_le_compat_r x y z : x ≤ z → x ⊓ y ≤ z.
  Proof. intros E. transitivity x. apply meet_lb_l. easy. Qed.
  Lemma meet_le_compat_l x y z : y ≤ z → x ⊓ y ≤ z.
  Proof. intros E. rewrite commutativity. now apply meet_le_compat_r. Qed.

  Lemma meet_l x y : x ≤ y → x ⊓ y = x.
  Proof. intros E. apply (antisymmetry (≤)). apply meet_lb_l. now apply meet_glb. Qed.
  Lemma meet_r x y : y ≤ x → x ⊓ y = y.
  Proof. intros E. rewrite commutativity. now apply meet_l. Qed.

  Lemma meet_sl_le_spec x y : x ≤ y ↔ x ⊓ y = x.
  Proof. split; intros E. now apply meet_l. rewrite <-E. now apply meet_lb_r. Qed.

  Global Instance: ∀ z, OrderPreserving (z ⊓).
  Proof.
    intros. repeat (split; try apply _). intros.
    apply meet_glb. now apply meet_lb_l. now apply  meet_le_compat_l.
  Qed.
  Global Instance: ∀ z, OrderPreserving (⊓ z).
  Proof. intros. apply maps.order_preserving_flip. Qed.

  Lemma meet_le_compat x₁ x₂ y₁ y₂ : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ ⊓ y₁ ≤ x₂ ⊓ y₂.
  Proof.
    intros E1 E2. transitivity (x₁ ⊓ y₂).
     now apply (order_preserving (x₁ ⊓)).
    now apply (order_preserving (⊓ y₂)).
  Qed.

  Lemma meet_le x y z : z ≤ x → z ≤ y → z ≤ x ⊓ y.
  Proof. intros. rewrite <-(idempotency (⊓) z). now apply meet_le_compat. Qed.
End meet_semilattice_order.

Section lattice_order.
  Context `{LatticeOrder L}.

  Instance: JoinSemiLattice L := join_sl_order_join_sl.
  Instance: MeetSemiLattice L := meet_sl_order_meet_sl.

  Instance: Absorption (⊓) (⊔).
  Proof.
    intros x y. apply (antisymmetry (≤)).
     now apply meet_lb_l.
    apply meet_le. easy. now apply join_ub_l.
  Qed.

  Instance: Absorption (⊔) (⊓).
  Proof.
    intros x y. apply (antisymmetry (≤)).
     apply join_le. easy. now apply meet_lb_l.
    now apply join_ub_l.
  Qed.

  Instance lattice_order_lattice: Lattice L.
  Proof. split; try apply _. Qed.

  Lemma meet_join_distr_l_le x y z : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z).
  Proof.
    apply meet_le.
     apply join_le; now apply meet_lb_l.
    apply join_le.
     transitivity y. apply meet_lb_r. apply join_ub_l.
    transitivity z. apply meet_lb_r. apply join_ub_r.
  Qed.

  Lemma join_meet_distr_l_le x y z : x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z).
  Proof.
    apply meet_le.
     apply join_le.
      now apply join_ub_l.
     transitivity y. apply meet_lb_l. apply join_ub_r.
    apply join_le.
     apply join_ub_l.
    transitivity z. apply meet_lb_r. apply join_ub_r.
  Qed.
End lattice_order.

Definition default_join_sl_le `{JoinSemiLattice L} : Le L :=  λ x y, x ⊔ y = y.

Section join_sl_order_alt.
  Context `{JoinSemiLattice L} `{Le L} (le_correct : ∀ x y, x ≤ y ↔ x ⊔ y = y).

  Lemma alt_Build_JoinSemiLatticeOrder : JoinSemiLatticeOrder (≤).
  Proof.
    split; try (split; try apply _).
         intros ?? E1 ?? E2. now rewrite !le_correct, E1, E2.
        split.
         intros ?. rewrite !le_correct. now apply (idempotency _ _).
        intros ? ? ?. rewrite !le_correct. intros E1 E2. now rewrite <-E2, associativity, E1.
       intros ? ?. rewrite !le_correct. intros E1 E2. now rewrite <-E1, commutativity, <-E2 at 1.
      intros ? ?. now rewrite le_correct, associativity, (idempotency _ _).
     intros ? ?. now rewrite le_correct, commutativity, <-associativity, (idempotency _ _).
    intros ? ? ?. rewrite !le_correct. intros E1 E2. now rewrite <-associativity, E2.
  Qed.
End join_sl_order_alt.

Definition default_meet_sl_le `{MeetSemiLattice L} : Le L :=  λ x y, x ⊓ y = x.

Section meet_sl_order_alt.
  Context `{MeetSemiLattice L} `{Le L} (le_correct : ∀ x y, x ≤ y ↔ x ⊓ y = x).

  Lemma alt_Build_MeetSemiLatticeOrder : MeetSemiLatticeOrder (≤).
  Proof.
    split; try (split; try apply _).
         intros ?? E1 ?? E2. now rewrite !le_correct, E1, E2.
        split.
         intros ?. rewrite !le_correct. now apply (idempotency _ _).
        intros ? ? ?. rewrite !le_correct. intros  E1 E2. now rewrite <-E1, <-associativity, E2.
       intros ? ?. rewrite !le_correct. intros  E1 E2. now rewrite <-E2, commutativity, <-E1 at 1.
      intros ? ?. now rewrite le_correct, commutativity, associativity, (idempotency _ _).
     intros ? ?. now rewrite le_correct, <-associativity, (idempotency _ _).
    intros ? ? ?. rewrite !le_correct. intros  E1 E2. now rewrite associativity, E1.
  Qed.
End meet_sl_order_alt.

Section join_order_preserving.
  Context `{JoinSemiLatticeOrder L} `{JoinSemiLatticeOrder K} (f : L → K) `{!JoinSemiLattice_Morphism f}.

  Local Existing Instance join_sl_order_join_sl.

  Lemma join_sl_mor_preserving: OrderPreserving f.
  Proof.
    repeat (split; try apply _).
    intros ??. rewrite 2!join_sl_le_spec, <-preserves_join. intros E. now rewrite E.
  Qed.

  Lemma join_sl_mor_reflecting `{!Injective f}: OrderReflecting f.
  Proof.
    repeat (split; try apply _).
    intros ??. rewrite 2!join_sl_le_spec, <-preserves_join. intros. now apply (injective f).
  Qed.
End join_order_preserving.

Section meet_order_preserving.
  Context `{MeetSemiLatticeOrder L} `{MeetSemiLatticeOrder K} (f : L → K) `{!MeetSemiLattice_Morphism f}.

  Local Existing Instance meet_sl_order_meet_sl.

  Lemma meet_sl_mor_preserving: OrderPreserving f.
  Proof.
    repeat (split; try apply _).
    intros ??. rewrite 2!meet_sl_le_spec, <-preserves_meet. intros E. now rewrite E.
  Qed.

  Lemma meet_sl_mor_reflecting `{!Injective f}: OrderReflecting f.
  Proof.
    repeat (split; try apply _).
    intros ??. rewrite 2!meet_sl_le_spec, <-preserves_meet. intros. now apply (injective f).
  Qed.
End meet_order_preserving.

Section order_preserving_join_sl_mor.
  Context `{JoinSemiLatticeOrder L} `{JoinSemiLatticeOrder K}
    `{!TotalOrder (_ : Le L)} `{!TotalOrder (_ : Le K)} `{!OrderPreserving (f : L → K)}.

  Local Existing Instance join_sl_order_join_sl.
  Local Existing Instance order_morphism_mor.

  Lemma order_preserving_join_sl_mor: JoinSemiLattice_Morphism f.
  Proof.
    repeat (split; try apply _).
    intros x y. case (total (≤) x y); intros E.
     rewrite 2!join_r; try easy. now apply (order_preserving _).
    rewrite 2!join_l; try easy. now apply (order_preserving _).
  Qed.
End order_preserving_join_sl_mor.

Section order_preserving_meet_sl_mor.
  Context `{MeetSemiLatticeOrder L} `{MeetSemiLatticeOrder K}
    `{!TotalOrder (_ : Le L)} `{!TotalOrder (_ : Le K)} `{!OrderPreserving (f : L → K)}.

  Local Existing Instance meet_sl_order_meet_sl.
  Local Existing Instance order_morphism_mor.

  Lemma order_preserving_meet_sl_mor: SemiGroup_Morphism f.
  Proof.
    repeat (split; try apply _).
    intros x y. case (total (≤) x y); intros E.
     rewrite 2!meet_l; try easy. now apply (order_preserving _).
    rewrite 2!meet_r; try easy. now apply (order_preserving _).
  Qed.
End order_preserving_meet_sl_mor.
