Require Import
  Coq.MSets.MSetInterface Coq.MSets.MSetFacts Coq.MSets.MSetProperties
  MathClasses.implementations.list MathClasses.implementations.list_finite_set MathClasses.theory.finite_sets
  MathClasses.interfaces.finite_sets MathClasses.interfaces.orders MathClasses.interfaces.abstract_algebra.

Module MSet_FSet (E : DecidableType) (Import set : WSetsOn E).

Module facts := WFactsOn E set.
Module props := WPropertiesOn E set.

Instance mset: SetType elt := t.

Instance mset_in: SetContains elt := In.
Instance mset_car_eq: Equiv elt := E.eq.
Instance mset_eq: SetEquiv elt := Equal.
Instance mset_le: SetLe elt := Subset.

Instance mset_singleton: SetSingleton elt := singleton.
Instance mset_empty: EmptySet elt := empty.
Instance mset_join: SetJoin elt := union.
Instance mset_meet: SetMeet elt := inter.
Instance mset_difference: SetDifference elt := diff.

Instance mset_car_dec: ∀ x y : elt, Decision (x = y) := E.eq_dec.
Instance mset_dec: ∀ x y : t, Decision (x = y) := eq_dec.

Local Instance: Setoid elt.
Proof. split; try apply _. Qed.

Local Instance: BoundedJoinSemiLattice mset.
Proof.
  Local Opaque Equal.
  repeat (split; try apply _); repeat intro.
      symmetry. now apply props.union_assoc.
     now apply props.empty_union_1, empty_spec.
    now apply props.empty_union_2, empty_spec.
   now apply props.union_sym.
  apply props.union_subset_equal, props.subset_refl.
  Local Transparent Equal.
Qed.

Local Instance: Setoid_Morphism singleton.
Proof. split; try apply _. Qed.

Definition to_listset (X : @set_type _ mset) : @set_type _ (listset elt)
  := props.to_list X↾elements_spec2w X.
Instance from_listset: Inverse to_listset := λ l, props.of_list (`l).

Local Instance: Setoid_Morphism to_listset.
Proof.
  split; try apply _. intros X Y E x.
  change (InA E.eq x (props.to_list X) ↔ InA E.eq x (props.to_list Y)).
  now rewrite <-!props.of_list_1, 2!props.of_list_3, E.
Qed.

Instance: Bijective to_listset.
Proof.
  split; split; try apply _.
   intros X Y E x. rewrite <-!elements_spec1. now apply E.
  intros ?? E. rewrite <-E. now rapply props.of_list_2.
Qed.

Instance: BoundedJoinSemiLattice_Morphism to_listset.
Proof.
  split; try apply _; split; try apply _.
   split; try apply _. intros X Y z.
   setoid_rewrite listset_in_join.
   repeat setoid_rewrite elements_spec1.
   apply union_spec.
  intros z. compute. rewrite props.elements_empty. tauto.
Qed.

Instance mset_extend: FSetExtend elt := iso_is_fset_extend id to_listset.

Local Instance: FSet elt.
Proof.
  apply (iso_is_fset id to_listset).
  intros x y E z.
  change (InA E.eq z (elements (singleton x)) ↔ InA E.eq z [y]).
  now rewrite elements_spec1, singleton_spec, E, InA_singleton.
Qed.

Instance: FullFSet elt.
Proof.
  split; try apply _. split.
     apply lattices.alt_Build_JoinSemiLatticeOrder.
     intros X Y. split; intros E.
      now apply props.union_subset_equal.
     rewrite <-E. now apply props.union_subset_1.
    intros x X. split; intros E.
     transitivity (add x empty).
      now apply props.subset_equal, props.singleton_equal_add.
     apply props.subset_add_3. auto. now apply props.subset_empty.
    apply props.union_subset_equal in E. rewrite <-E.
    now apply facts.union_2, singleton_spec.
   now apply inter_spec.
  now apply diff_spec.
Qed.
End MSet_FSet.
