Require Import
  theory.lattices varieties.monoids implementations.bool
  implementations.list_finite_set orders.lattices
  abstract_algebra interfaces.finite_sets interfaces.orders.

Definition fset_car_setoid A `{FSet A} : Setoid A := setoidmor_a singleton.

Section fset_props.
  Context `{FSet A}.

  Instance: Setoid A := fset_car_setoid A.

  Lemma fset_extend_correct_applied `{BoundedJoinSemiLattice B} (f : A → B) `{!Setoid_Morphism f} x :
    f x = fset_extend f {{ x }}.
  Proof. now apply fset_extend_correct. Qed.

  Lemma fset_extend_unique_applied `{Equiv B} `{Join B} `{Bottom B} (f : A → B) `{!Setoid_Morphism f}
      (h : set_type A → B) `{!BoundedJoinSemiLattice_Morphism (h : set_type A → B)} :
    (∀ x, f x = h {{ x }}) → ∀ x, h x = fset_extend f x.
  Proof.
    intros. apply setoids.ext_equiv_applied, (fset_extend_unique _ _).
    now apply setoids.ext_equiv_applied_iff.
  Qed.

  Let F (x y z : A) := if decide (z = x) then false else true.
  Instance: ∀ x y, Setoid_Morphism (F x y).
  Proof.
    split; try apply _. intros ?? E. unfold F.
    do 2 case (decide _); try reflexivity; rewrite E; contradiction.
  Qed.

  Global Instance: Injective (singleton : A → set_type A).
  Proof.
    split; try apply _. intros x y E1. apply stable; intros E2.
    assert (fset_extend (F x y) {{ x }} ≠ fset_extend (F x y) {{ y }}) as E3.
     rewrite <-!(fset_extend_correct_applied (F x y)).
     unfold F. do 2 case (decide _); firstorder.
    destruct E3. now rewrite E1.
  Qed.

  Lemma fset_singleton_ne_empty x : {{ x }} ≠ ∅.
  Proof.
    intros E1.
    set (g (z : A) := true).
    assert (Setoid_Morphism g) by (split; try apply _; firstorder).
    assert (fset_extend g {{ x }} ≠ ⊥) as E2.
     rewrite <-(fset_extend_correct_applied g). discriminate.
    destruct E2. now rewrite E1, preserves_bottom.
  Qed.

  Lemma fset_join_singletons x : {{ x ;  x }} = {{ x }}.
  Proof. now rewrite (idempotency (⊔) _). Qed.

  Lemma fset_join_singletons_eq_l x y : {{ x ;  y }} = {{ x }} ↔ x = y.
  Proof.
    split.
     intros E1. apply stable; intros E2.
     assert (fset_extend (F x y)  {{ x ; y }} ≠ fset_extend (F x y) {{ x }}) as E3.
      rewrite preserves_join, <-!(fset_extend_correct_applied (F x y)).
      unfold F. do 2 (case (decide _)); firstorder.
     destruct E3. now rewrite E1.
    intros E. now rewrite E, fset_join_singletons.
  Qed.

  Lemma fset_join_singletons_eq_r x y : {{ x ;  y }} = {{ y }} ↔ x = y.
  Proof. rewrite commutativity, fset_join_singletons_eq_l. intuition. Qed.
End fset_props.

Instance fset_map_mor `{FSet A} `{FSet B} (f : A → B) `{!Setoid_Morphism f} :
  BoundedJoinSemiLattice_Morphism (fset_map (H:=At) (H0:=At0) (SetSingleton0:=Asingle0)  f).
Proof. apply _. Qed.

Lemma fset_map_correct `{FSet A} `{FSet B} (f : A → B) `{!Setoid_Morphism f} :
  singleton ∘ f = fset_map f ∘ singleton.
Proof (fset_extend_correct _).

Lemma fset_map_correct_applied `{FSet A} `{FSet B} (f : A → B) `{!Setoid_Morphism f} x :
  {{ f x }} = fset_map f {{ x }}.
Proof.
  pose proof (fset_car_setoid A).
  now apply (setoids.ext_equiv_applied (fset_map_correct f)).
Qed.

Lemma fset_map_unique `{FSet A} `{FSet B} (f : A → B) `{!Setoid_Morphism f}
    (h : set_type A → set_type B) `{!BoundedJoinSemiLattice_Morphism h} :
  singleton ∘ f = h ∘ singleton → h = fset_map f.
Proof. intros. unfold fset_map. now apply (fset_extend_unique _ _). Qed.

Lemma fset_map_id `{FSet A} :
  fset_map id = id.
Proof.
  pose proof (fset_car_setoid A).
  symmetry. apply (fset_map_unique id id).
  now apply setoids.ext_equiv_refl.
Qed.

Lemma fset_map_id_applied `{FSet A} x :
  fset_map id x = x.
Proof. now apply fset_map_id. Qed.

Lemma fset_map_compose `{FSet A} `{FSet B} `{FSet C}
     (f : B → C) `{!Setoid_Morphism f} (g : A → B) `{!Setoid_Morphism g} :
  fset_map (f ∘ g) = fset_map f ∘ fset_map g.
Proof.
  pose proof (fset_car_setoid A).
  symmetry. apply (fset_map_unique (f ∘ g) _).
  rewrite compose_assoc.
  rewrite <-(fset_map_correct g).
  rewrite <-compose_assoc.
  rewrite (fset_map_correct f).
  now apply setoids.ext_equiv_refl.
Qed.

Section fset_map_inverse.
  Context `{FSet A} `{FSet B} (f : A → B) `{!Inverse f} `{!Bijective f}.

  Global Instance fset_map_inverse: Inverse (fset_map f) := fset_map (f⁻¹).

  Instance fset_map_surjective: Surjective (fset_map f).
  Proof.
    pose proof (fset_car_setoid A). pose proof (fset_car_setoid B).
    pose proof (injective_mor f). split; try apply _.
    unfold inverse, fset_map_inverse.
    rewrite <-(fset_map_compose _ _).
    symmetry. apply (fset_map_unique _ _).
    rewrite (surjective f).
    now apply setoids.ext_equiv_refl.
  Qed.
End fset_map_inverse.

Instance fset_map_bijective `{FSet A} `{FSet B}
  (f : A → B) `{!Inverse f} `{!Bijective f} : Bijective (fset_map f).
Proof.
  pose proof (fset_car_setoid A). pose proof (fset_car_setoid B).
  pose proof (injective_mor f).
  pose proof (fset_map_surjective f). pose proof (fset_map_surjective (f⁻¹)).
  repeat (split; try apply _). intros x y E.
  rewrite <-(jections.surjective_applied (fset_map (f⁻¹)) x).
  rewrite <-(jections.surjective_applied (fset_map (f⁻¹)) y).
  now apply sm_proper.
Qed.

Lemma preserves_in `{FullFSet A} `{FullFSet B} (f : A → B) `{!Inverse f} `{!Bijective f} x X :
  f x ∈ fset_map f X ↔ x ∈ X.
Proof.
  pose proof (injective_mor f).
  pose proof (join_sl_mor_preserving (fset_map f)).
  pose proof (join_sl_mor_reflecting (fset_map f)).
  rewrite !fset_in_singleton_le.
  split; intros E.
   apply (order_reflecting (fset_map f)).
   now rewrite <-(fset_map_correct_applied f).
  rewrite (fset_map_correct_applied f).
  now apply (order_preserving _).
Qed.

Lemma preserves_notin `{FullFSet A} `{FullFSet B} (f : A → B) `{!Inverse f} `{!Bijective f} x X :
  f x ∉ fset_map f X ↔ x ∉ X.
Proof. split; intros E ?; now apply E, (preserves_in f). Qed.

Section full_fset_props.
  Context `{FullFSet A}.

  Instance: Setoid A := fset_car_setoid A.

  Notation to_listset := (fset_map id : set_type A → @set_type _ (listset A)).
  Notation from_listset := (to_listset⁻¹).

  Lemma to_listset_preserves_in x X : x ∈ to_listset X ↔ x ∈ X.
  Proof preserves_in id x X.

  Lemma fset_induction (P : set_type A → Prop) `{proper : !Proper ((=) ==> iff) P} :
    P ∅ → (∀ x X, x ∉ X → P X → P ({{ x }} ⊔ X)) → ∀ X, P X.
  Proof.
    intros Pempty Padd X.
    mc_setoid_replace X with (from_listset (to_listset X))
     by (symmetry; apply (jections.bijective_applied _)).
    generalize (to_listset X). apply listset_induction.
      solve_proper.
     now rewrite preserves_bottom.
    intros x l E1 E2.
    change (P (fset_map id ({{x}} ⊔ l))).
    rewrite preserves_join, <-(fset_map_correct_applied _ x).
    apply Padd; auto. intros E3. destruct E1. now apply (preserves_in id x).
  Qed.

  Global Instance fset_in_proper : Proper ((=) ==> (=) ==> iff) ((∈): A → set_type A).
  Proof. intros x y E1 X Y E2. now rewrite !fset_in_singleton_le, E1, E2. Qed.

  Global Program Instance fset_in_dec_slow: ∀ x X, Decision (x ∈ X) | 50 := λ x X,
    match decide_rel (∈) x (to_listset X) with left E => left _ | right E => right _ end.
  Next Obligation. now apply to_listset_preserves_in. Qed.
  Next Obligation. intros F. destruct E. now apply to_listset_preserves_in. Qed.

  Lemma fset_notin_empty x : x ∉ ∅.
  Proof. intro. now apply fset_singleton_ne_empty with x, below_bottom, fset_in_singleton_le. Qed.

  Lemma fset_in_join X Y x : x ∈ X ⊔ Y ↔ x ∈ X ∨ x ∈ Y.
  Proof. rewrite <-!to_listset_preserves_in, preserves_join. apply listset_in_join. Qed.

  Lemma fset_notin_join X Y x : x ∉ X ⊔ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. rewrite fset_in_join. tauto. Qed.

  Lemma fset_in_singleton x : x ∈ {{ x }}.
  Proof. now rewrite fset_in_singleton_le, join_sl_le_spec, fset_join_singletons. Qed.

  Lemma fset_in_singleton_eq x y : x ∈ {{ y }} ↔ x = y.
  Proof.
    split; intros E.
     now apply fset_join_singletons_eq_r, join_sl_le_spec, fset_in_singleton_le.
    rewrite E. apply fset_in_singleton.
  Qed.

  Lemma fset_notin_singleton_neq x y : x ∉ {{ y }} ↔ x ≠ y.
  Proof. now rewrite fset_in_singleton_eq. Qed.

  Lemma fset_in_add y X x : y ∈ {{ x }} ⊔ X ↔ y = x ∨ y ∈ X.
  Proof.
    rewrite fset_in_join. split; intros [?|?]; try tauto.
     left. now apply fset_in_singleton_eq.
    left. now apply fset_in_singleton_eq.
  Qed.

  Lemma fset_notin_add y X x : y ∉ {{ x }} ⊔ X ↔ y ≠ x ∧ y ∉ X.
  Proof. rewrite fset_in_add. tauto. Qed.

  Lemma fset_in_inversion y X x : y ∈ {{ x }} ⊔ X → y = x ∨ y ∈ X.
  Proof.
    rewrite fset_in_join. intros [?|?]; try tauto.
    left. now apply fset_in_singleton_eq.
  Qed.

  Lemma fset_le_in X Y : X ≤ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof.
    pose proof (join_sl_mor_preserving to_listset).
    pose proof (join_sl_mor_reflecting to_listset).
    setoid_rewrite <-to_listset_preserves_in.
    split; intros E.
     now apply (order_preserving (to_listset)) in E.
    now apply (order_reflecting (to_listset)).
  Qed.

  Lemma fset_eq_in X Y : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof.
    setoid_rewrite <-to_listset_preserves_in.
    split.
     intros E. change (to_listset X = to_listset Y).
     now apply sm_proper.
    intros. now apply (injective (to_listset)).
  Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) (⊓).
  Proof. intros ?? E1 ?? E2. apply fset_eq_in. intros. now rewrite !fset_in_meet, E1, E2. Qed.
  Instance: Associative (⊓).
  Proof. repeat intro. apply fset_eq_in. intros. rewrite !fset_in_meet. tauto. Qed.
  Instance: Commutative (⊓).
  Proof. repeat intro. apply fset_eq_in. intros. rewrite !fset_in_meet. tauto. Qed.
  Instance: BinaryIdempotent (⊓).
  Proof. repeat intro. apply fset_eq_in. intros. rewrite !fset_in_meet. tauto. Qed.
  Instance: MeetSemiLattice (set_type A).
  Proof. repeat (split; try apply _). Qed.

  Global Instance: DistributiveLattice (set_type A).
  Proof.
    repeat (split; try apply _); repeat intro; apply fset_eq_in; intro;
      repeat (rewrite fset_in_meet || rewrite fset_in_join); tauto.
  Qed.

  Global Instance: MeetSemiLatticeOrder (≤).
  Proof.
    apply alt_Build_MeetSemiLatticeOrder. intros.
    rewrite fset_le_in, fset_eq_in. setoid_rewrite fset_in_meet. firstorder trivial.
  Qed.

  Lemma fset_meet_singletons x : {{ x }} ⊓ {{ x }} = {{ x }}.
  Proof. now rewrite (idempotency (⊔) _). Qed.

  Lemma fset_meet_singletons_eq_l x y : {{ x }} ⊓ {{ y }} = {{ x }} ↔ x = y.
  Proof.
    split; intros E.
     apply fset_in_singleton_eq.
     rewrite fset_eq_in in E. setoid_rewrite fset_in_meet in E.
     now destruct (proj2 (E x) (fset_in_singleton _)).
    now rewrite E, fset_meet_singletons.
  Qed.

  Lemma fset_meet_singletons_eq_r x y : {{ x }} ⊓ {{ y }} = {{ y }} ↔ x = y.
  Proof. rewrite commutativity, fset_meet_singletons_eq_l. intuition. Qed.

  Lemma fset_meet_distinct_singletons (x y: A) : x ≠ y → {{ x }} ⊓ {{ y }} = ∅.
  Proof.
    intros E1. apply fset_eq_in. intros z.
    rewrite fset_in_meet. split.
     intros [E2 E3]. destruct E1.
     apply fset_in_singleton_eq in E2. apply fset_in_singleton_eq in E3.
     now rewrite <-E2, <-E3.
    intro. now destruct (fset_notin_empty z).
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> (=)) (∖).
  Proof. intros ?? E1 ?? E2. apply fset_eq_in. intros. now rewrite !fset_in_difference, E1, E2. Qed.

  Global Instance fset_difference_empty_r: RightIdentity (∖) ∅.
  Proof.
    intro. apply fset_eq_in. intro. rewrite fset_in_difference.
    split; intuition. edestruct fset_notin_empty; eassumption.
  Qed.

  Global Instance fset_difference_empty_l: LeftAbsorb (∖) ∅.
  Proof.
    intro. apply fset_eq_in. intro. rewrite fset_in_difference.
    split; intuition. edestruct fset_notin_empty; eassumption.
  Qed.

  Global Instance diff_meet_distr_r: RightDistribute (∖) (⊓).
  Proof.
    intros X Y Z. apply fset_eq_in. intro.
    repeat (rewrite fset_in_meet || rewrite fset_in_difference). intuition.
  Qed.

  Global Instance diff_join_distr_r: RightDistribute (∖) (⊔).
  Proof.
    intros X Y Z. apply fset_eq_in. intro.
    repeat (rewrite fset_in_join || rewrite fset_in_difference). intuition.
  Qed.

  Lemma diff_meet_join_diff X Y Z : X ∖ (Y ⊓ Z) = X ∖ Y ⊔ X ∖ Z.
  Proof.
    apply fset_eq_in. intro.
    repeat (rewrite fset_in_join || rewrite fset_in_meet || rewrite fset_in_difference).
    split; try tauto. intros [??]. case (decide (x ∈ Y)); tauto.
  Qed.

  Lemma diff_join_diff_meet X Y Z : X ∖ (Y ⊔ Z) = X ∖ Y ⊓ X ∖ Z.
  Proof.
    apply fset_eq_in. intro.
    repeat (rewrite fset_in_join || rewrite fset_in_meet || rewrite fset_in_difference). tauto.
  Qed.
End full_fset_props.

Ltac split_sets :=
  repeat (match goal with
  | E : _ ∈ ∅ |- _ => apply fset_notin_empty in E; destruct E
  | E : _ ∈ {{ _ }} |- _ => apply fset_in_singleton_eq in E
  | E : _ ∉ {{ _ }} |- _ => apply fset_notin_singleton_neq in E
  | E : _ ∈ _ ⊔ _ |- _ => apply fset_in_join in E; destruct E
  | E : _ ∉ _ ⊔ _ |- _ => apply fset_notin_join in E; destruct E
  | E : _ ∈ _ ⊓ _ |- _ => apply fset_in_meet in E; destruct E
  | |-  context [_ ∈ _ ⊔ _] => rewrite !fset_in_join
  end).

Section iso_is_fset.
  Context `{Setoid A} `{At : SetType A}
    `{BoundedJoinSemiLattice (set_type A)} `{fsetB : FSet B}
    `{SetSingleton A} `{!Setoid_Morphism (singleton : A → At)}
    (A_to_B : A → B) `{!Inverse A_to_B} `{!Bijective A_to_B}
    (At_to_Bt : set_type A → set_type B) `{!Inverse At_to_Bt}
   `{!Bijective At_to_Bt} `{!BoundedJoinSemiLattice_Morphism At_to_Bt}
   `{∀ a₁ a₂ : A, Decision (a₁ = a₂)}
    (singleton_correct : At_to_Bt ∘ singleton = singleton ∘ A_to_B).

  Instance: Setoid B := fset_car_setoid B.

  Lemma singleton_correct_alt :
    At_to_Bt⁻¹ ∘ singleton = singleton ∘ A_to_B⁻¹.
  Proof.
    pose proof (injective_mor A_to_B). pose proof (injective_mor At_to_Bt).
    apply (jections.injective_compose_cancel At_to_Bt).
    rewrite <-!compose_assoc.
    rewrite (surjective At_to_Bt), singleton_correct.
    rewrite compose_assoc, (surjective A_to_B).
    rewrite compose_id_left, compose_id_right.
    now apply setoids.ext_equiv_refl.
  Qed.

  Instance iso_is_fset_extend: FSetExtend A := λ C _ _ f,
    fset_extend (f ∘ A_to_B⁻¹) ∘ At_to_Bt.

  Instance iso_is_fset: FSet A.
  Proof.
    pose proof (injective_mor A_to_B).
    split; unfold fset_extend, iso_is_fset_extend; try apply _.
     intros C ? ? ? ? f ?.
     rewrite compose_assoc, singleton_correct, <-compose_assoc.
     rewrite <-(fset_extend_correct (f ∘ A_to_B ⁻¹)).
     rewrite compose_assoc, (jections.bijective _), compose_id_right.
     now apply setoids.ext_equiv_refl.
    intros C ? ? ? f ? h ? E1.
    pose proof (bounded_join_slmor_b (f:=h)).
    rewrite <-(fset_extend_unique (f ∘ A_to_B⁻¹) (h ∘ At_to_Bt⁻¹)).
     rewrite compose_assoc, (jections.bijective _), compose_id_right.
     now apply setoids.ext_equiv_refl.
    rewrite E1, !compose_assoc, singleton_correct_alt.
    now apply setoids.ext_equiv_refl.
  Qed.
End iso_is_fset.
