Require Import
  abstract_algebra interfaces.orders orders.orders
  orders.lattices theory.setoids.

Section contents.
  Context `{TotalOrder A} `{∀ x y: A, Decision (x ≤ y)}.

  Instance: Setoid A := po_setoid.

  Definition sort (x y: A) : A * A := if decide_rel (≤) x y then (x, y) else (y, x).

  Global Instance: Proper ((=) ==> (=) ==> (=)) sort.
  Proof.
    intros ? ? E1 ? ? E2. unfold sort. do 2 case (decide_rel _); simpl.
        firstorder.
       intros F ?. destruct F. now rewrite <-E1, <-E2.
      intros ? F. destruct F. now rewrite E1, E2.
    firstorder.
  Qed.

  Global Instance min: Meet A := λ x y, fst (sort x y).
  Global Instance max: Join A := λ x y, snd (sort x y).

  Global Instance: LatticeOrder (≤).
  Proof.
    repeat (split; try apply _); unfold join, meet, max, min, sort;
     intros; case (decide_rel _); try easy; now apply le_flip.
  Qed.

  Instance: LeftDistribute max min.
  Proof.
    intros x y z. unfold min, max, sort.
    repeat case (decide_rel _); simpl; try solve [intuition].
     intros. apply (antisymmetry (≤)); [|easy]. now transitivity y; apply le_flip.
    intros. now apply (antisymmetry (≤)).
  Qed.

  Instance: Lattice A := lattice_order_lattice.

  Global Instance: DistributiveLattice A.
  Proof. repeat (split; try apply _). Qed.
End contents.

