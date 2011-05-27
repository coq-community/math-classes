Require Import 
  abstract_algebra interfaces.orders orders.orders theory.setoids theory.strong_setoids.

(* If a function between strict partial orders is order preserving (back), we can 
  derive that it is strcitly order preserving (back) *)
Section strictly_order_preserving.
  Context `{FullPartialOrder A} `{FullPartialOrder B}.

  Global Instance strictly_order_preserving_inj  `{!OrderPreserving (f : A → B)} `{!StrongInjective f} : 
    StrictlyOrderPreserving f | 20.
  Proof.
    pose proof (order_morphism_mor f).
    repeat (split; try apply _).
    intros x y. rewrite !lt_iff_le_apart. intros [E1 E2]. split.
     now apply (order_preserving f).
    now apply (strong_injective f).
  Qed.

  Global Instance strictly_order_preserving_back_mor `{!OrderPreservingBack (f : A → B)} `{!StrongSetoid_Morphism f} : 
    StrictlyOrderPreservingBack f | 20.
  Proof.
    pose proof (order_morphism_mor f).
    repeat (split; try apply _).
    intros x y. rewrite !lt_iff_le_apart. intros [E1 E2]. split.
     now apply (order_preserving_back f).
    now apply (strong_extensionality f).
  Qed.
End strictly_order_preserving.

(* For structures with a trivial apartness relation we have a stronger result of the above *)
Section strictly_order_preserving_dec.
  Context `{FullPartialOrder A} `{!TrivialApart A} `{FullPartialOrder B} `{!TrivialApart B}.

  Instance: StrongSetoid A := strict_po_setoid.
  Instance: StrongSetoid B := strict_po_setoid.

  Global Instance dec_strictly_order_preserving_inj  `{!OrderPreserving (f : A → B)} `{!Injective f} : 
    StrictlyOrderPreserving f | 19.
  Proof. pose proof (dec_strong_injective f). apply _. Qed.

  Global Instance dec_strictly_order_preserving_back_mor `{!OrderPreservingBack (f : A → B)} : 
    StrictlyOrderPreservingBack f | 19.
  Proof. pose proof (order_morphism_mor f). pose proof (dec_strong_morphism f). apply _. Qed.
End strictly_order_preserving_dec.

Section pseudo_injective.
  Context `{PseudoOrder A} `{PseudoOrder B}.

  Existing Instance pseudo_order_setoid.

  Instance pseudo_order_embedding_ext `{!StrictOrderEmbedding (f : A → B)} :
    StrongSetoid_Morphism f.
  Proof.
    split; try apply _.
    intros x y. rewrite !apart_iff_total_lt.
    intros [|]; [left | right]; now apply (strictly_order_preserving_back f).
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

  Existing Instance pseudo_order_setoid.

  Lemma full_pseudo_order_preserving `{!StrictlyOrderPreservingBack (f : A → B)} : OrderPreserving f.
  Proof.
    pose proof (strict_order_morphism_mor f).
    repeat (split; try apply _).
    intros x y. rewrite !le_iff_not_lt_flip.
    intros E1 E2. apply E1.
    now apply (strictly_order_preserving_back f).
  Qed.

  Lemma full_pseudo_order_preserving_back `{!StrictlyOrderPreserving (f : A → B)} : OrderPreservingBack f.
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

  Lemma order_preserving_back_flip `{!Commutative op} `{!Proper ((=) ==> (=) ==> (=)) op} `{!OrderPreservingBack (op z) } : 
    OrderPreservingBack (λ y, op y z).
  Proof.
    pose proof (order_morphism_mor (op z)).
    pose proof (setoidmor_a (op z)).
    repeat (split; try apply _).
     solve_proper.
    intros x y E.
    apply (order_preserving_back (op z)).
    now rewrite 2!(commutativity z).
  Qed.

  Lemma strictly_order_preserving_back_flip `{!Commutative op} `{!Proper ((=) ==> (=) ==> (=)) op} `{!StrictlyOrderPreservingBack (op z) } : 
    StrictlyOrderPreservingBack (λ y, op y z).
  Proof.
    pose proof (strict_order_morphism_mor (op z)).
    pose proof (setoidmor_a (op z)).
    repeat (split; try apply _).
     solve_proper.
    intros x y E.
    apply (strictly_order_preserving_back (op z)).
    now rewrite 2!(commutativity z).
  Qed.

  Lemma order_preserving_nonneg (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (op z)} z :
    0 ≤ z → OrderPreserving (op z).
  Proof. auto. Qed.

  Lemma order_preserving_flip_nonneg (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (λ y, op y z)} z :
    0 ≤ z → OrderPreserving (λ y, op y z).
  Proof. auto. Qed.

  Lemma strictly_order_preserving_pos (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (op z)} z :
    0 < z → StrictlyOrderPreserving (op z).
  Proof. auto. Qed.

  Lemma strictly_order_preserving_flip_pos (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (λ y, op y z)} z :
    0 < z → StrictlyOrderPreserving (λ y, op y z).
  Proof. auto. Qed.

  Lemma order_preserving_back_pos (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → OrderPreservingBack (op z)} z :
    0 < z → OrderPreservingBack (op z).
  Proof. auto. Qed.

  Lemma order_preserving_back_flip_pos (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → OrderPreservingBack (λ y, op y z)} z :
    0 < z → OrderPreservingBack (λ y, op y z).
  Proof. auto. Qed.
End order_preserving_ops. 

Lemma projected_partial_order `{Equiv A} `{Ale : Le A} `{Equiv B} `{Ble : Le B} 
  (f : A → B) `{!OrderEmbedding f} `{!Injective f} `{!PartialOrder Ble} : PartialOrder Ale.
Proof.
  pose proof (order_morphism_mor f).
  pose proof (setoidmor_a f).
  pose proof (setoidmor_b f).
  repeat (split; try apply _).
    intros x. now apply (order_preserving_back f).
   intros x y z E1 E2. apply (order_preserving_back f).
   transitivity (f y); now apply (order_preserving f).
  intros x y E1 E2. apply (injective f).
  apply (antisymmetry (≤)); now apply (order_preserving f).
Qed.

Lemma projected_total_order `{Equiv A} `{Ale : Le A} `{Equiv B} `{Ble : Le B} 
  (f : A → B) `{!OrderEmbedding f} `{!TotalRelation Ble} : TotalRelation Ale.
Proof.
  intros x y. 
  destruct (total (≤) (f x) (f y)); [left | right]; now apply (order_preserving_back f).
Qed.

Lemma projected_strict_order `{Equiv A} `{Alt : Lt A} `{Equiv B} `{Blt : Lt B} 
  (f : A → B) `{!StrictOrderEmbedding f} `{!StrictSetoidOrder Blt} : StrictSetoidOrder Alt.
Proof.
  pose proof (strict_order_morphism_mor f).
  pose proof (setoidmor_a f).
  repeat (split; try apply _).
   intros x E. destruct (irreflexivity (<) (f x)).
   now apply (strictly_order_preserving _).
  intros x y z E1 E2. apply (strictly_order_preserving_back f).
  transitivity (f y); now apply (strictly_order_preserving f).
Qed.

Lemma projected_strict_setoid_order `{Equiv A} `{Alt : Lt A} `{Equiv B} `{Blt : Lt B} 
  (f : A → B) `{!StrictOrderEmbedding f} `{!StrictOrder Blt} : StrictOrder Alt.
Proof.
  repeat (split; try apply _).
   intros x E. destruct (irreflexivity (<) (f x)).
   now apply (strictly_order_preserving _).
  intros x y z E1 E2. apply (strictly_order_preserving_back f).
  transitivity (f y); now apply (strictly_order_preserving f).
Qed.

Lemma projected_pseudo_order `{Equiv A} `{Apart A} `{Alt : Lt A} `{Equiv B} `{Apart B} `{Blt : Lt B} 
  (f : A → B) `{!StrictOrderEmbedding f} `{!StrongInjective f} `{!PseudoOrder Blt} : PseudoOrder Alt.
Proof.
  pose proof (strong_injective_mor f).
  pose proof (strong_setoidmor_a f).
  pose proof (strong_setoidmor_b f).
  split; try apply _.
    intros x y E. 
    destruct (pseudo_order_antisym (f x) (f y)).
    split; now apply (strictly_order_preserving _).
   intros x y E z.
   apply (strictly_order_preserving f) in E.
   destruct (cotransitive E (f z)); [left | right]; now apply (strictly_order_preserving_back f).
  intros x y; split; intros E.
   apply (strong_injective f) in E.
   apply apart_iff_total_lt in E. 
   destruct E; [left | right]; now apply (strictly_order_preserving_back f).
  apply (strong_extensionality f).
  apply apart_iff_total_lt.
  destruct E; [left | right]; now apply (strictly_order_preserving _).
Qed.

Lemma projected_full_pseudo_order `{Equiv A} `{Apart A} `{Ale : Le A} `{Alt : Lt A} 
  `{Equiv B} `{Apart B} `{Ble : Le B} `{Blt : Lt B} 
  (f : A → B) `{!OrderEmbedding f} `{!StrictOrderEmbedding f} `{!StrongInjective f} 
  `{!FullPseudoOrder Ble Blt} : FullPseudoOrder Ale Alt.
Proof.
  split.
   now apply (projected_pseudo_order f).
  intros x y; split; intros E.
   intros F. destruct (le_not_lt_flip (f y) (f x)).
    now apply (order_preserving f).
   now apply (strictly_order_preserving f).
  apply (order_preserving_back f).
  apply not_lt_le_flip.
  intros F. destruct E. now apply (strictly_order_preserving_back f).
Qed.

Instance id_order_morphism `{Setoid A} `{Le A} `{!Proper ((=) ==> (=) ==> iff) (≤)} : Order_Morphism (@id A) := {}.

Instance id_order_preserving `{Setoid A} `{Le A} `{!Proper ((=) ==> (=) ==> iff) (≤)} : OrderPreserving (@id A).
Proof. split; try apply _. easy. Qed.

Instance id_order_preserving_back `{Setoid A} `{Le A} `{!Proper ((=) ==> (=) ==> iff) (≤)} : OrderPreservingBack (@id A).
Proof. split; try apply _. easy. Qed.

Section composition.
  Context `{Equiv A} `{Equiv B} `{Equiv C} `{Le A} `{Le B} `{Le C}.

  Instance compose_order_morphism `{!Order_Morphism (f : A → B)} `{!Order_Morphism (g : B → C)} : 
    Order_Morphism (g ∘ f).
  Proof.
    pose proof (order_morphism_mor f).
    pose proof (order_morphism_mor g).
    split; [ apply _ | apply _ | apply (order_morphism_proper_b g) ].
  Qed.

  Instance compose_order_preserving `{!OrderPreserving (f : A → B)} `{!OrderPreserving (g : B → C)} : 
    OrderPreserving (g ∘ f).
  Proof.
    repeat (split; try apply _).
    intros. unfold compose.
    now do 2 apply (order_preserving _).
  Qed.

  Instance compose_order_preserving_back `{!OrderPreservingBack (f : A → B)} `{!OrderPreservingBack (g : B → C)} : 
    OrderPreservingBack (g ∘ f).
  Proof.
    split; try apply _.
    intros x y E. unfold compose in E.
    now do 2 apply (order_preserving_back _) in E.
  Qed.

  Instance compose_order_embedding `{!OrderEmbedding (f : A → B)} `{!OrderEmbedding (g : B → C)} : 
    OrderEmbedding (g ∘ f) := {}.
End composition.

Hint Extern 4 (Order_Morphism (_ ∘ _)) => eapply @compose_order_morphism : typeclass_instances.
Hint Extern 4 (OrderPreserving (_ ∘ _)) => eapply @compose_order_preserving : typeclass_instances.
Hint Extern 4 (OrderPreservingBack (_ ∘ _)) => eapply @compose_order_preserving_back : typeclass_instances.
Hint Extern 4 (OrderEmbedding (_ ∘ _)) => eapply @compose_order_embedding : typeclass_instances.

Section propers.
  Context `{Equiv A} `{Equiv B} `{Le A} `{Le B}.

  Global Instance order_morphism_proper: Proper ((=) ==> iff) (@Order_Morphism A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → Order_Morphism f → Order_Morphism g) as P.
     intros f g E [[? ? ?] ?].
     split; auto.
     rewrite E. now split.
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

  Global Instance order_preserving_back_proper: Proper ((=) ==> iff) (@OrderPreservingBack A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderPreservingBack f → OrderPreservingBack g) as P.
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
     eapply order_preserving_back_proper; eauto. now apply _.
    intros f g ?; split; intro E.
     apply P with f. destruct E as [[[[? ?]]]]. now symmetry. easy.
    now apply P with g.
  Qed.
End propers.
