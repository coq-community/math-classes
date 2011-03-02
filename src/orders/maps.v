Require Import 
  Program Morphisms Setoid 
  abstract_algebra orders.orders theory.setoids.

Instance order_iso_injective `{OrderIsomorphism A B f} `{!PartialOrder (precedes (A:=A))} `{!PartialOrder (precedes (A:=B))} : 
  Injective f.
Proof.
  split; try apply _.
  pose proof (poset_setoid : Setoid B).
  intros x y E.
  apply (antisymmetry (≤)); apply (order_preserving_back f); apply equiv_precedes.
   assumption.
  now symmetry.
Qed.

Instance strictly_order_preserving_inj `{OrderPreserving A B f} `{!Injective f} : StrictlyOrderPreserving f | 10.
Proof.
  split; try apply _.
  intros x y [E1 E2].
  split.
   now apply (order_preserving f).
  intro. apply E2. now apply (injective f).
Qed.

Lemma strictly_order_preserving_back `(f : A → B) `{OrderPreservingBack A B f}  x y : f x < f y → x < y.
Proof.
  intros [E1 E2].
  split.
   now apply (order_preserving_back f).
  intro. apply E2. 
  pose proof (order_morphism_mor f). now apply sm_proper.
Qed.

(* Some helper lemmas *)
Section order_preserving_ops.
  Context `{Equiv R} `{Order R}.

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

  Lemma order_preserving_ge_0 (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (op z)} z :
    0 ≤ z → OrderPreserving (op z).
  Proof. auto. Qed.

  Lemma order_preserving_flip_ge_0 (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (λ y, op y z)} z :
    0 ≤ z → OrderPreserving (λ y, op y z).
  Proof. auto. Qed.

  Lemma strictly_order_preserving_gt_0 (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (op z)} z :
    0 < z → StrictlyOrderPreserving (op z).
  Proof. auto. Qed.

  Lemma strictly_order_preserving_flip_gt_0 (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (λ y, op y z)} z :
    0 < z → StrictlyOrderPreserving (λ y, op y z).
  Proof. auto. Qed.

  Lemma order_preserving_back_gt_0 (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → OrderPreservingBack (op z)} z :
    0 < z → OrderPreservingBack (op z).
  Proof. auto. Qed.

  Lemma order_preserving_back_flip_gt_0 (op : R → R → R) `{!RingZero R} `{∀ z, PropHolds (0 < z) → OrderPreservingBack (λ y, op y z)} z :
    0 < z → OrderPreservingBack (λ y, op y z).
  Proof. auto. Qed.
End order_preserving_ops. 

Section order_embedding.
  Context `{Equiv A} `{Equiv B} `{oA : Order A} `{oB : Order B} (f : B → A)
     `{!Setoid_Morphism f} `{!OrderEmbedding f}.

  Lemma embed_partialorder `{!Injective f} `{!PartialOrder oA} : PartialOrder oB.
  Proof.
    pose proof (setoidmor_b f : Setoid A).
    pose proof (setoidmor_a f : Setoid B).
    repeat (split; try apply _).
      intros x. now apply (order_preserving_back f).
     intros x y z E1 E2. apply (order_preserving_back f).
     transitivity (f y); now apply (order_preserving f).
    intros x y E1 E2. apply (injective f).
    apply (antisymmetry _); now apply (order_preserving f).
  Qed.

  Lemma embed_totalorder `{!TotalOrder oA} : TotalOrder oB.
  Proof.
    intros x y. 
    destruct (total_order (f x) (f y)); [left | right]; now apply (order_preserving_back f).
  Qed.
End order_embedding.

Instance id_order_morphism `{Setoid A} `{Order A} `{!Proper ((=) ==> (=) ==> iff) (≤)} : Order_Morphism (@id A).

Instance id_order_preserving `{Setoid A} `{Order A} `{!Proper ((=) ==> (=) ==> iff) (≤)} : OrderPreserving (@id A).
Proof. split; try apply _. easy. Qed.

Instance id_order_preserving_back `{Setoid A} `{Order A} `{!Proper ((=) ==> (=) ==> iff) (≤)} : OrderPreservingBack (@id A).
Proof. split; try apply _. easy. Qed.

Section composition.
  Context `{Equiv A} `{Equiv B} `{Equiv C} `{Order A} `{Order B} `{Order C}.

  Global Instance compose_order_morphism `{!Order_Morphism (f : A → B)} `{!Order_Morphism (g : B → C)} : 
    Order_Morphism (g ∘ f).
  Proof.
    pose proof (order_morphism_mor f).
    pose proof (order_morphism_mor g).
    split; apply _.
  Qed.

  Global Instance compose_order_preserving `{!OrderPreserving (f : A → B)} `{!OrderPreserving (g : B → C)} : 
    OrderPreserving (g ∘ f).
  Proof.
    repeat (split; try apply _).
    intros. unfold compose.
    now do 2 apply (order_preserving _).
  Qed.

  Global Instance compose_order_preserving_back `{!OrderPreservingBack (f : A → B)} `{!OrderPreservingBack (g : B → C)} : 
    OrderPreservingBack (g ∘ f).
  Proof.
    split; try apply _.
    intros x y E. unfold compose in E.
    now do 2 apply (order_preserving_back _) in E.
  Qed.

  Global Instance compose_order_embedding_back `{!OrderEmbedding (f : A → B)} `{!OrderEmbedding (g : B → C)} : 
    OrderEmbedding (g ∘ f).
End composition.

Section propers.
  Context `{Equiv A} `{Equiv B} `{Order A} `{Order B}.

  Global Instance order_morphism_proper: Proper ((=) ==> iff) (@Order_Morphism A _ _ B _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → Order_Morphism f → Order_Morphism g) as P.
     intros f g E [[? ? ?] ?].
     split; auto.
     rewrite E. now split.
    firstorder.
  Qed.

  Global Instance order_preserving_proper: Proper ((=) ==> iff) (@OrderPreserving A _ _ B _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderPreserving f → OrderPreserving g) as P.
     intros f g E [[[? ?] ? ?] ?].
     split.
      rewrite E. repeat (split; try apply _).
     intros x y ?. rewrite (E x x), (E y y); now auto.
    firstorder.
  Qed.

  Global Instance order_preserving_back_proper: Proper ((=) ==> iff) (@OrderPreservingBack A _ _ B _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderPreservingBack f → OrderPreservingBack g) as P.
     intros f g E [[[? ?] ? ?] ?].
     split.
      rewrite E. repeat (split; try apply _).
     intros x y F. rewrite (E x x), (E y y) in F; now auto.
    firstorder.
  Qed.

  Global Instance order_embedding_proper: Proper ((=) ==> iff) (@OrderEmbedding A _ _ B _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderEmbedding f → OrderEmbedding g) as P.
     intros f g E.
     split; rewrite E; now apply _.
    intros f g ?; split; intro E.
     apply P with f. destruct E as [[[[? ?]]]]. now symmetry. easy.
    now apply P with g.
  Qed.
End propers.
