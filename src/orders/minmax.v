Require Import
  RelationClasses Morphisms
  abstract_algebra orders.orders theory.setoids.

(* This is ugly, maybe we should let TotalOrder live in Type to get rid of the Decision stuff *)
Section contents.
  Context `{Setoid A} `{Order A} `{prec_decide : ∀ x y: A, Decision (x ≤ y)}.

  Definition sort (x y: A) : A * A := if prec_decide x y then (x, y) else (y, x).

  Definition min (x y: A) := fst (sort x y).
  Definition max (x y: A) := snd (sort x y).

  Lemma min_lb_l x y `{!Reflexive (≤)} `{!TotalOrder (≤)} : min x y ≤ x.
  Proof. unfold min, sort. case (prec_decide _); firstorder. Qed.

  Lemma min_lb_r `{!Reflexive (≤)} x y : min x y ≤ y.
  Proof. unfold min, sort. case (prec_decide _); firstorder. Qed.

  Lemma min_l x y : x ≤ y → min x y = x.
  Proof. unfold min, sort. case (prec_decide _); firstorder. Qed.

  Lemma min_r `{!AntiSymmetric (≤)} x y : y ≤ x → min x y = y.
  Proof. unfold min, sort. case (prec_decide _); firstorder. Qed.

  Lemma min_diag x: min x x = x.
  Proof. unfold min, sort. case (prec_decide _); reflexivity. Qed.

  Lemma max_ub_l `{!Reflexive (≤)} x y : x ≤ max x y.
  Proof. unfold max, sort. case (prec_decide _); auto. Qed.

  Lemma max_ub_r `{!Reflexive (≤)} `{!TotalOrder (≤)} x y : y ≤ max x y.
  Proof. unfold max, sort. case (prec_decide _); firstorder. Qed.

  Lemma max_l `{!AntiSymmetric (≤)} x y : y ≤ x → max x y = x.
  Proof. unfold max, sort. case (prec_decide _); firstorder. Qed.

  Lemma max_r x y : x ≤ y → max x y = y.
  Proof. unfold max, sort. case (prec_decide _); firstorder. Qed.

  Lemma max_diag x: max x x = x.
  Proof. unfold max, sort. case (prec_decide _); reflexivity. Qed.
  
  Global Instance sort_proper `{!Proper ((=) ==> (=) ==> iff) (≤)} : Proper ((=) ==> (=) ==> (=)) sort.
  Proof with assumption.
    intros x y E x' y' E'.
    unfold sort.
    do 2 case (prec_decide _); simpl.
        firstorder. 
       intros F ?. destruct F. rewrite <-E, <-E'...
      intros ? F. destruct F. rewrite E, E'...
    firstorder.
  Qed.

  Global Instance min_proper `{!Proper ((=) ==> (=) ==> iff) (≤)} : Proper ((=) ==> (=) ==> (=)) min.
  Proof. unfold min. repeat intro. apply sm_proper. apply sort_proper; assumption. Qed.

  Global Instance max_proper `{!Proper ((=) ==> (=) ==> iff) (≤)} : Proper ((=) ==> (=) ==> (=)) max.
  Proof. unfold max. repeat intro. apply sm_proper. apply sort_proper; assumption. Qed.

  Global Instance min_commutative `{!AntiSymmetric (≤)} `{!TotalOrder (≤)} : Commutative min.
  Proof. intros x y. unfold min, sort. do 2 case (prec_decide _); firstorder. Qed.

  Global Instance max_commutative `{!AntiSymmetric (≤)} `{!TotalOrder (≤)} : Commutative max.
  Proof. intros x y. unfold max, sort. do 2 case (prec_decide _); firstorder. Qed.

  Global Instance min_associative `{!AntiSymmetric (≤)} `{!Transitive (≤)} `{!TotalOrder (≤)} : Associative min.
  Proof with auto; try reflexivity; try contradiction.
     intros x y z. unfold min, sort.
     case (prec_decide y z); simpl; intros E1; case (prec_decide x y); simpl; intros E2; 
       case (prec_decide x z); simpl; intros E3; case (prec_decide y z); simpl; intros E4...
     destruct E3. transitivity y...
     destruct E4. transitivity x... apply orders.precedes_flip... 
  Qed.

  Global Instance max_associative `{!AntiSymmetric (≤)} `{!Transitive (≤)} `{!TotalOrder (≤)} : Associative max.
  Proof with auto; try reflexivity; try contradiction.
     intros x y z. unfold max, sort.
     case (prec_decide y z); simpl; intros E1; case (prec_decide x y); simpl; intros E2; 
       case (prec_decide x z); simpl; intros E3; case (prec_decide y z); simpl; intros E4...
     destruct E3. transitivity y...
     destruct E4. transitivity x... apply orders.precedes_flip... 
  Qed.
End contents.

Instance: Params (@sort) 3.
Instance: Params (@min) 3.
Instance: Params (@max) 3.

Section order_preserving.
  Context `{PartialOrder A} `{PartialOrder B} {f : A → B} `{!OrderPreserving f}
    `{!TotalOrder (precedes (A:=A))} `{!TotalOrder (precedes (A:=B))}
    `{prec_decideA : ∀ x y: A, Decision (x ≤ y)} `{prec_decideB : ∀ x y: B, Decision (x ≤ y)}. 

  Instance: Setoid A. apply poset_setoid. Qed.
  Instance: Setoid B. apply poset_setoid. Qed.

  Lemma preserves_min x y : f (min x y) = min (f x) (f y).
  Proof with auto.
    symmetry. unfold min at 2. unfold sort.
    case (prec_decideA _); simpl; intros E.
     apply min_l. apply (order_preserving _)...
    apply min_r. apply (order_preserving _). apply precedes_flip...
  Qed.

  Lemma preserves_max x y : f (max x y) = max (f x) (f y).
  Proof with auto.
    symmetry. unfold max at 2. unfold sort.
    case (prec_decideA _); simpl; intros E.
     apply max_r. apply (order_preserving _)...
    apply max_l. apply (order_preserving _). apply precedes_flip...
  Qed.
End order_preserving.

(* hm, min should just be max on the inverse order. would be nice if we could do that niftyly 
 
 I just took the naive way and proved all properties twice... 
 Yet, it would be cool if we could do the above. 
*)
