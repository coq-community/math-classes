Require Import
  abstract_algebra interfaces.orders orders.orders theory.setoids theory.strong_setoids.

Local Existing Instance order_morphism_po_a.
Local Existing Instance order_morphism_po_b.
Local Existing Instance strict_order_morphism_so_a.
Local Existing Instance strict_order_morphism_so_b.
Local Existing Instance order_morphism_mor.
Local Existing Instance strict_order_morphism_mor.

(* If a function between strict partial orders is order preserving (back), we can
  derive that it is strictly order preserving (back) *)
Section strictly_order_preserving.
  Context `{FullPartialOrder A} `{FullPartialOrder B}.

  Global Instance strictly_order_preserving_inj  `{!OrderPreserving (f : A → B)} `{!StrongInjective f} :
    StrictlyOrderPreserving f | 20.
  Proof.
    repeat (split; try apply _).
    intros x y. rewrite !lt_iff_le_apart. intros [E1 E2]. split.
     now apply (order_preserving f).
    now apply (strong_injective f).
  Qed.

  Global Instance strictly_order_reflecting_mor `{!OrderReflecting (f : A → B)} `{!StrongSetoid_Morphism f} :
    StrictlyOrderReflecting f | 20.
  Proof.
    repeat (split; try apply _).
    intros x y. rewrite !lt_iff_le_apart. intros [E1 E2]. split.
     now apply (order_reflecting f).
    now apply (strong_extensionality f).
  Qed.
End strictly_order_preserving.

(* For structures with a trivial apartness relation we have a stronger result of the above *)
Section strictly_order_preserving_dec.
  Context `{FullPartialOrder A} `{!TrivialApart A} `{FullPartialOrder B} `{!TrivialApart B}.

  Local Existing Instance strict_po_setoid.

  Global Instance dec_strictly_order_preserving_inj  `{!OrderPreserving (f : A → B)} `{!Injective f} :
    StrictlyOrderPreserving f | 19.
  Proof. pose proof (dec_strong_injective f). apply _. Qed.

  Global Instance dec_strictly_order_reflecting_mor `{!OrderReflecting (f : A → B)} :
    StrictlyOrderReflecting f | 19.
  Proof. pose proof (order_morphism_mor f). pose proof (dec_strong_morphism f). apply _. Qed.
End strictly_order_preserving_dec.

Section pseudo_injective.
  Context `{PseudoOrder A} `{PseudoOrder B}.

  Local Existing Instance pseudo_order_setoid.

  Instance pseudo_order_embedding_ext `{!StrictOrderEmbedding (f : A → B)} :
    StrongSetoid_Morphism f.
  Proof.
    split; try apply _.
    intros x y. rewrite !apart_iff_total_lt.
    intros [|]; [left | right]; now apply (strictly_order_reflecting f).
  Qed.

  Lemma pseudo_order_embedding_inj `{!StrictOrderEmbedding (f : A → B)} :
    StrongInjective f.
  Proof.
    split; try apply _.
    intros x y. rewrite !apart_iff_total_lt.
    intros [|]; [left | right]; now apply (strictly_order_preserving f).
  Qed.
End pseudo_injective.

(* If a function between pseudo partial orders is strictly order preserving (back), we can
  derive that it is order preserving (back) *)
Section full_pseudo_strictly_preserving.
  Context `{FullPseudoOrder A} `{FullPseudoOrder B}.

  Local Existing Instance pseudo_order_setoid.

  Lemma full_pseudo_order_preserving `{!StrictlyOrderReflecting (f : A → B)} : OrderPreserving f.
  Proof.
    pose proof (strict_order_morphism_mor f).
    repeat (split; try apply _).
    intros x y. rewrite !le_iff_not_lt_flip.
    intros E1 E2. apply E1.
    now apply (strictly_order_reflecting f).
  Qed.

  Lemma full_pseudo_order_reflecting `{!StrictlyOrderPreserving (f : A → B)} : OrderReflecting f.
  Proof.
    pose proof (strict_order_morphism_mor f).
    repeat (split; try apply _).
    intros x y. rewrite !le_iff_not_lt_flip.
    intros E1 E2. apply E1.
    now apply (strictly_order_preserving f).
  Qed.
End full_pseudo_strictly_preserving.

(* Some helper lemmas to easily transform order preserving instances. *)
Section order_preserving_ops.
  Context `{Equiv R} `{Le R} `{Lt R}.

  Lemma order_preserving_flip `{!Commutative op} `{!Proper ((=) ==> (=) ==> (=)) op} `{!OrderPreserving (op z)} :
    OrderPreserving (λ y, op y z).
  Proof.
    pose proof (order_morphism_mor (op z)).
    pose proof (setoidmor_a (op z)).
    repeat (split; try apply _).
     solve_proper.
    intros x y E.
    rewrite 2!(commutativity _ z).
    now apply order_preserving.
  Qed.

  Lemma strictly_order_preserving_flip `{!Commutative op} `{!Proper ((=) ==> (=) ==> (=)) op} `{!StrictlyOrderPreserving (op z)} :
    StrictlyOrderPreserving (λ y, op y z).
  Proof.
    pose proof (strict_order_morphism_mor (op z)).
    pose proof (setoidmor_a (op z)).
    repeat (split; try apply _).
     solve_proper.
    intros x y E.
    rewrite 2!(commutativity _ z).
    now apply strictly_order_preserving.
  Qed.

  Lemma order_reflecting_flip `{!Commutative op} `{!Proper ((=) ==> (=) ==> (=)) op} `{!OrderReflecting (op z) } :
    OrderReflecting (λ y, op y z).
  Proof.
    pose proof (order_morphism_mor (op z)).
    pose proof (setoidmor_a (op z)).
    repeat (split; try apply _).
     solve_proper.
    intros x y E.
    apply (order_reflecting (op z)).
    now rewrite 2!(commutativity z).
  Qed.

  Lemma strictly_order_reflecting_flip `{!Commutative op} `{!Proper ((=) ==> (=) ==> (=)) op} `{!StrictlyOrderReflecting (op z) } :
    StrictlyOrderReflecting (λ y, op y z).
  Proof.
    pose proof (strict_order_morphism_mor (op z)).
    pose proof (setoidmor_a (op z)).
    repeat (split; try apply _).
     solve_proper.
    intros x y E.
    apply (strictly_order_reflecting (op z)).
    now rewrite 2!(commutativity z).
  Qed.

  Lemma order_preserving_nonneg (op : R → R → R) `{!Zero R} `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (op z)} z :
    0 ≤ z → ∀ x y, x ≤ y → op z x ≤ op z y.
  Proof. firstorder. Qed.

  Lemma order_preserving_flip_nonneg (op : R → R → R) `{!Zero R} `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (λ y, op y z)} z :
    0 ≤ z → ∀ x y, x ≤ y → op x z ≤ op y z.
  Proof. firstorder. Qed.

  Lemma strictly_order_preserving_pos (op : R → R → R) `{!Zero R} `{∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (op z)} z :
    0 < z → ∀ x y, x < y → op z x < op z y.
  Proof. firstorder. Qed.

  Lemma strictly_order_preserving_flip_pos (op : R → R → R) `{!Zero R} `{∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (λ y, op y z)} z :
    0 < z → ∀ x y, x < y → op x z < op y z.
  Proof. firstorder. Qed.

  Lemma order_reflecting_pos (op : R → R → R) `{!Zero R} `{∀ z, PropHolds (0 < z) → OrderReflecting (op z)} z :
    0 < z → ∀ x y, op z x ≤ op z y → x ≤ y.
  Proof. firstorder. Qed.

  Lemma order_reflecting_flip_pos (op : R → R → R) `{!Zero R} `{∀ z, PropHolds (0 < z) → OrderReflecting (λ y, op y z)} z :
    0 < z → ∀ x y, op x z ≤ op y z → x ≤ y.
  Proof. firstorder. Qed.
End order_preserving_ops.

Lemma projected_partial_order `{Equiv A} `{Ale : Le A} `{Equiv B} `{Ble : Le B}
  (f : A → B) `{!Injective f} `{!PartialOrder Ble} : (∀ x y, x ≤ y ↔ f x ≤ f y) → PartialOrder Ale.
Proof.
  pose proof (injective_mor f).
  pose proof (setoidmor_a f).
  pose proof (setoidmor_b f).
  intros P. split; try apply _.
    intros ? ? E1 ? ? E2. now rewrite 2!P, E1, E2.
   split.
    intros x. now apply P.
   intros x y z E1 E2. apply P.
   transitivity (f y); now apply P.
  intros x y E1 E2. apply (injective f).
  apply (antisymmetry (≤)); now apply P.
Qed.

Lemma projected_total_order `{Equiv A} `{Ale : Le A} `{Equiv B} `{Ble : Le B}
  (f : A → B) `{!TotalRelation Ble} : (∀ x y, x ≤ y ↔ f x ≤ f y) → TotalRelation Ale.
Proof.
  intros P x y.
  destruct (total (≤) (f x) (f y)); [left | right]; now apply P.
Qed.

Lemma projected_strict_order `{Equiv A} `{Alt : Lt A} `{Equiv B} `{Blt : Lt B}
  (f : A → B) `{!StrictOrder Blt} : (∀ x y, x < y ↔ f x < f y) → StrictOrder Alt.
Proof.
  intros P. split.
   intros x E. destruct (irreflexivity (<) (f x)). now apply P.
  intros x y z E1 E2. apply P. transitivity (f y); now apply P.
Qed.

Lemma projected_strict_setoid_order `{Equiv A} `{Alt : Lt A} `{Equiv B} `{Blt : Lt B}
  (f : A → B) `{!Setoid_Morphism f} `{!StrictSetoidOrder Blt} : (∀ x y, x < y ↔ f x < f y) → StrictSetoidOrder Alt.
Proof.
  pose proof (setoidmor_a f).
  intros P. split; try apply _.
   intros ? ? E1 ? ? E2. now rewrite 2!P, E1, E2.
  now apply (projected_strict_order f).
Qed.

Lemma projected_pseudo_order `{Equiv A} `{Apart A} `{Alt : Lt A} `{Equiv B} `{Apart B} `{Blt : Lt B}
  (f : A → B) `{!StrongInjective f} `{!PseudoOrder Blt} : (∀ x y, x < y ↔ f x < f y) → PseudoOrder Alt.
Proof.
  pose proof (strong_injective_mor f).
  pose proof (strong_setoidmor_a f).
  pose proof (strong_setoidmor_b f).
  intros P. split; try apply _.
    intros x y E. destruct (pseudo_order_antisym (f x) (f y)). split; now apply P.
   intros x y E z. apply P in E.
   destruct (cotransitive E (f z)); [left | right]; now apply P.
  intros x y; split; intros E.
   apply (strong_injective f) in E.
   apply apart_iff_total_lt in E. destruct E; [left | right]; now apply P.
  apply (strong_extensionality f).
  apply apart_iff_total_lt. destruct E; [left | right]; now apply P.
Qed.

Lemma projected_full_pseudo_order `{Equiv A} `{Apart A} `{Ale : Le A} `{Alt : Lt A}
  `{Equiv B} `{Apart B} `{Ble : Le B} `{Blt : Lt B}
  (f : A → B) `{!StrongInjective f} `{!FullPseudoOrder Ble Blt} : (∀ x y, x ≤ y ↔ f x ≤ f y) → (∀ x y, x < y ↔ f x < f y) → FullPseudoOrder Ale Alt.
Proof.
  intros P1 P2. split.
   now apply (projected_pseudo_order f).
  intros x y; split; intros E.
   intros F. destruct (le_not_lt_flip (f y) (f x)); firstorder.
  apply P1. apply not_lt_le_flip.
  intros F. destruct E. now apply P2.
Qed.

Instance id_order_morphism `{PartialOrder A} : Order_Morphism (@id A).
Proof. pose proof po_setoid. repeat (split; try apply _). Qed.

Instance id_order_preserving `{PartialOrder A} : OrderPreserving (@id A).
Proof. split; try apply _. easy. Qed.

Instance id_order_reflecting `{PartialOrder A} : OrderReflecting (@id A).
Proof. split; try apply _. easy. Qed.

Section composition.
  Context `{Equiv A} `{Equiv B} `{Equiv C}
    `{Le A} `{Le B} `{Le C} (f : A → B) (g : B → C).

  Instance compose_order_morphism:
    Order_Morphism f → Order_Morphism g → Order_Morphism (g ∘ f).
  Proof. split; [ apply _ | apply (order_morphism_po_a f) | apply (order_morphism_po_b g) ]. Qed.

  Instance compose_order_preserving:
    OrderPreserving f → OrderPreserving g → OrderPreserving (g ∘ f).
  Proof.
    repeat (split; try apply _).
    intros. unfold compose.
    now do 2 apply (order_preserving _).
  Qed.

  Instance compose_order_reflecting:
    OrderReflecting f → OrderReflecting g → OrderReflecting (g ∘ f).
  Proof.
    split; try apply _.
    intros x y E. unfold compose in E.
    now do 2 apply (order_reflecting _) in E.
  Qed.

  Instance compose_order_embedding:
    OrderEmbedding f → OrderEmbedding g → OrderEmbedding (g ∘ f) := {}.
End composition.

Hint Extern 4 (Order_Morphism (_ ∘ _)) => class_apply @compose_order_morphism : typeclass_instances.
Hint Extern 4 (OrderPreserving (_ ∘ _)) => class_apply @compose_order_preserving : typeclass_instances.
Hint Extern 4 (OrderReflecting (_ ∘ _)) => class_apply @compose_order_reflecting : typeclass_instances.
Hint Extern 4 (OrderEmbedding (_ ∘ _)) => class_apply @compose_order_embedding : typeclass_instances.

Section propers.
  Context `{Equiv A} `{Equiv B} `{Le A} `{Le B}.

  Global Instance order_morphism_proper: Proper ((=) ==> iff) (@Order_Morphism A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → Order_Morphism f → Order_Morphism g) as P.
     intros f g E [[? ? ?] ?].
     split; auto. apply morphism_proper with f. easy. split; easy.
    firstorder.
  Qed.

  Global Instance order_preserving_proper: Proper ((=) ==> iff) (@OrderPreserving A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderPreserving f → OrderPreserving g) as P.
     intros f g E [[[? ?] ? ?] ?].
     split.
      eapply order_morphism_proper; eauto. now repeat (split; try apply _).
     intros x y ?. rewrite (E x x), (E y y); now auto.
    firstorder.
  Qed.

  Global Instance order_reflecting_proper: Proper ((=) ==> iff) (@OrderReflecting A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderReflecting f → OrderReflecting g) as P.
     intros f g E [[[? ?] ? ?] ?].
     split.
      eapply order_morphism_proper; eauto. now repeat (split; try apply _).
     intros x y F. rewrite (E x x), (E y y) in F; now auto.
    firstorder.
  Qed.

  Global Instance order_embedding_proper: Proper ((=) ==> iff) (@OrderEmbedding A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderEmbedding f → OrderEmbedding g) as P.
     intros f g E.
     split.
      eapply order_preserving_proper; eauto. now apply _.
     eapply order_reflecting_proper; eauto. now apply _.
    intros f g ?; split; intro E.
     apply P with f. destruct E as [[[[? ?]]]]. now symmetry. easy.
    now apply P with g.
  Qed.
End propers.
