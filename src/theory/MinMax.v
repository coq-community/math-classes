Require Import
  RelationClasses Morphisms
  abstract_algebra.

Section contents.

  Context `{e: Setoid A} `{Order A} `{∀ x y: A, Decision (x ≤ y)}.

  Definition sort (x y: A): prod A A := if decide (x ≤ y) then (x, y) else (y, x).

  Definition min (x y: A) := fst (sort x y).

  Instance max: SemiGroupOp A := λ x y, snd (sort x y).

  Lemma max_ub_l `{Reflexive _ precedes} x y: x ≤ x & y.
  Proof. unfold sg_op, max, sort. case (decide _); firstorder. Qed.

  Lemma max_r x y: x ≤ y → x & y = y.
  Proof. unfold sg_op, max, sort. intros. case (decide _); firstorder. Qed.

  Lemma max_idem x: max x x = x.
  Proof. intros. unfold max, sort. case (decide _); reflexivity. Qed.

  Global Instance max_proper `{p: !Proper (equiv ==> equiv ==> iff) precedes}: Proper (equiv ==> equiv ==> equiv) max.
  Proof with assumption.
   intros x y E x' y' E'.
   unfold max, sort.
   do 2 case (decide _); simpl.
      firstorder. 
     intros n ?. exfalso. apply n. apply -> (p x y E x')...
    intros ? n. exfalso. apply n. apply <- (p x y E x' y')...
   firstorder.
  Qed.

  Section more_props.

    Context `{!TotalOrder precedes} `{!PartialOrder precedes}.

    Lemma max_comm (x y: A): max x y = max y x.
    Proof. intros. unfold max, sort. case (decide _); case (decide _); firstorder. Qed.

    Lemma max_ub_r (x y: A): y ≤ max x y.
    Proof. intros. rewrite max_comm. apply max_ub_l. Qed.

    Global Instance: Associative max.
    Proof with try assumption.
     intros x y z.
     unfold max, sort.
     intros.
     do 4 case (decide _); try reflexivity; try intuition; simpl in *.
      exfalso.
      apply n.
      transitivity y...
     destruct (total_order x y); intuition.
     destruct (total_order y z); intuition.
     apply (antisymmetry precedes)...
     transitivity y...
    Qed.

    Lemma max_l x y: x ≤ y → max y x = y.
    Proof. intros. rewrite max_comm, max_r; firstorder. Qed.

    Global Instance max_semigroup: SemiGroup A.

  End more_props.

End contents.

(* hm, min should just be max on the inverse order. would be nice if we could do that niftyly *)
