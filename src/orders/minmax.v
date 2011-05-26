Require Import
  RelationClasses
  abstract_algebra interfaces.orders orders.orders theory.setoids.

Section contents.
  Context `{Setoid A} `{Le A} `{∀ x y: A, Decision (x ≤ y)} `{!PartialOrder (≤)} `{!TotalRelation (≤)}.

  Definition sort (x y: A) : A * A := if decide_rel (≤) x y then (x, y) else (y, x).

  Definition min (x y: A) := fst (sort x y).
  Definition max (x y: A) := snd (sort x y).

  Lemma min_lb_l x y : min x y ≤ x.
  Proof. unfold min, sort. case (decide_rel _); firstorder. Qed.

  Lemma min_lb_r x y : min x y ≤ y.
  Proof. unfold min, sort. case (decide_rel _); firstorder. Qed.

  Lemma min_l x y : x ≤ y → min x y = x.
  Proof. unfold min, sort. case (decide_rel _); firstorder. Qed.

  Lemma min_r x y : y ≤ x → min x y = y.
  Proof. unfold min, sort. case (decide_rel _); firstorder. Qed.

  Lemma min_diag x: min x x = x.
  Proof. unfold min, sort. case (decide_rel _); reflexivity. Qed.

  Lemma max_ub_l x y : x ≤ max x y.
  Proof. unfold max, sort. case (decide_rel _); firstorder. Qed.

  Lemma max_ub_r x y : y ≤ max x y.
  Proof. unfold max, sort. case (decide_rel _); firstorder. Qed.

  Lemma max_l x y : y ≤ x → max x y = x.
  Proof. unfold max, sort. case (decide_rel _); firstorder. Qed.

  Lemma max_r x y : x ≤ y → max x y = y.
  Proof. unfold max, sort. case (decide_rel _); firstorder. Qed.

  Lemma max_diag x: max x x = x.
  Proof. unfold max, sort. case (decide_rel _); reflexivity. Qed.
  
  Global Instance sort_proper `{!Proper ((=) ==> (=) ==> iff) (≤)} : Proper ((=) ==> (=) ==> (=)) sort.
  Proof.
    intros x y E x' y' E'.
    unfold sort.
    do 2 case (decide_rel _); simpl.
        firstorder. 
       intros F ?. destruct F. now rewrite <-E, <-E'.
      intros ? F. destruct F. now rewrite E, E'.
    firstorder.
  Qed.

  Global Instance min_proper `{!Proper ((=) ==> (=) ==> iff) (≤)} : Proper ((=) ==> (=) ==> (=)) min.
  Proof. unfold min. repeat intro. apply sm_proper. now apply sort_proper. Qed.

  Global Instance max_proper `{!Proper ((=) ==> (=) ==> iff) (≤)} : Proper ((=) ==> (=) ==> (=)) max.
  Proof. unfold max. repeat intro. apply sm_proper. now apply sort_proper. Qed.

  Global Instance min_commutative: Commutative min.
  Proof. 
    intros x y. unfold min, sort. 
    do 2 case (decide_rel _); simpl; try reflexivity; intros. 
     now apply (antisymmetry (≤)).
    now apply (antisymmetry (≤)); apply le_flip.
  Qed.

  Global Instance max_commutative: Commutative max.
  Proof.
    intros x y. unfold max, sort. 
    do 2 case (decide_rel _); simpl; try reflexivity; intros. 
     now apply (antisymmetry (≤)).
    now apply (antisymmetry (≤)); apply le_flip.
  Qed.

  Global Instance min_associative: Associative min.
  Proof.
     intros x y z. unfold min, sort.
     case (decide_rel (≤) y z); simpl; intros E1; case (decide_rel (≤) x y); simpl; intros E2; 
       case (decide_rel (≤) x z); simpl; intros E3; case (decide_rel (≤) y z); simpl; intros E4; try easy.
     destruct E3. now transitivity y.
     destruct E4. transitivity x. now apply le_flip. easy.
  Qed.

  Global Instance max_associative `{!AntiSymmetric (≤)} `{!Transitive (≤)} `{!TotalOrder (≤)} : Associative max.
  Proof.
     intros x y z. unfold max, sort.
     case (decide_rel (≤) y z); simpl; intros E1; case (decide_rel (≤) x y); simpl; intros E2; 
       case (decide_rel (≤) x z); simpl; intros E3; case (decide_rel (≤) y z); simpl; intros E4; try easy.
     destruct E3. now transitivity y.
     destruct E4. transitivity x. now apply le_flip. easy.
  Qed.
End contents.

Instance: Params (@sort) 3.
Instance: Params (@min) 3.
Instance: Params (@max) 3.

Section order_preserving.
  Context `{PartialOrder A} `{PartialOrder B} {f : A → B} `{!OrderPreserving f}
    `{!TotalRelation (A:=A) (≤)} `{!TotalRelation (A:=B) (≤)}
    `{∀ x y: A, Decision (x ≤ y)} `{∀ x y: B, Decision (x ≤ y)}. 

  Instance: Setoid A := po_setoid.
  Instance: Setoid B := po_setoid.

  Lemma preserves_min x y : f (min x y) = min (f x) (f y).
  Proof.
    symmetry. unfold min at 2. unfold sort.
    case (decide_rel _); simpl; intros E.
     apply min_l. now apply (order_preserving _).
    apply min_r. apply (order_preserving _). now apply le_flip.
  Qed.

  Lemma preserves_max x y : f (max x y) = max (f x) (f y).
  Proof.
    symmetry. unfold max at 2. unfold sort.
    case (decide_rel _); simpl; intros E.
     apply max_r. now apply (order_preserving _).
    apply max_l. apply (order_preserving _). now apply le_flip.
  Qed.
End order_preserving.

(* hm, min should just be max on the inverse order. would be nice if we could do that niftyly 
 
 I just took the naive way and proved all properties twice... 
 Yet, it would be cool if we could do the above. 
*)
