Require Import
  List SetoidList
  abstract_algebra interfaces.finite_sets interfaces.orders
  theory.lattices orders.lattices.

(* The below belongs in the stdlib *)
Section equivlistA_misc.
  Context `{Equivalence A eqA}.

  Lemma NoDupA_singleton x : NoDupA eqA [x].
  Proof. apply NoDupA_cons. intros E. inversion E. auto. Qed.

  Global Instance equivlistA_cons_proper: Proper (eqA ==> equivlistA eqA ==> equivlistA eqA) cons.
  Proof.
    assert (∀ x₁ x₂ l₁ l₂ x, eqA x₁ x₂ → equivlistA eqA l₁ l₂ → InA eqA x (x₁ :: l₁) → InA eqA x (x₂ :: l₂)) as aux.
     intros ? ? ? ? ? E1 E2 E3. inversion_clear E3.
      apply InA_cons_hd. now rewrite <-E1.
     apply InA_cons_tl. now rewrite <-E2.
    split; eapply aux; auto; now symmetry.
  Qed.

  Lemma InA_singleton x y : InA eqA x [y] ↔ eqA x y.
  Proof.
    split; intros E.
     inversion_clear E; auto. now destruct (proj1 (InA_nil eqA x)).
    rewrite E. intuition.
  Qed.

  Lemma equivlistA_cons_nil x l : ¬equivlistA eqA (x :: l) [].
  Proof. intros E. now eapply InA_nil, E, InA_cons_hd. Qed.

  Lemma equivlistA_nil_eq l : equivlistA eqA l [] → l ≡ [].
  Proof. induction l. easy. intros E. edestruct equivlistA_cons_nil; eauto. Qed.

  Lemma InA_double_head z x l : InA eqA z (x :: x :: l) ↔ InA eqA z (x :: l).
  Proof. split; intros E1; auto. inversion_clear E1; auto. Qed.
  Lemma InA_permute_heads z x y l : InA eqA z (x :: y :: l) → InA eqA z (y :: x :: l).
  Proof. intros E1. inversion_clear E1 as [|?? E2]; auto. inversion_clear E2; auto. Qed.

  Lemma equivlistA_double_head x l : equivlistA eqA (x :: x :: l) (x :: l).
  Proof. split; apply InA_double_head. Qed.
  Lemma equivlistA_permute_heads x y l : equivlistA eqA (x :: y :: l) (y :: x :: l).
  Proof. split; apply InA_permute_heads. Qed.

  Lemma InA_app_ass z l₁ l₂ l₃ : InA eqA z (l₁ ++ (l₂ ++ l₃)) ↔ InA eqA z ((l₁ ++ l₂) ++ l₃).
  Proof. now rewrite app_ass. Qed.
  Lemma InA_app_nil_l z l : InA eqA z ([] ++ l) ↔ InA eqA z l.
  Proof. firstorder. Qed.
  Lemma InA_app_nil_r z l : InA eqA z (l ++ []) ↔ InA eqA z l.
  Proof. now rewrite app_nil_r. Qed.

  Lemma equivlistA_app_ass l₁ l₂ l₃ : equivlistA eqA (l₁ ++ (l₂ ++ l₃)) ((l₁ ++ l₂) ++ l₃).
  Proof. now rewrite app_ass. Qed.
  Lemma equivlistA_app_nil_l l : equivlistA eqA ([] ++ l) l.
  Proof. reflexivity. Qed.
  Lemma equivlistA_app_nil_r l : equivlistA eqA (l ++ []) l.
  Proof. now rewrite app_nil_r. Qed.

  Lemma InA_comm z l₁ l₂ : InA eqA z (l₁ ++ l₂) → InA eqA z (l₂ ++ l₁).
  Proof. rewrite !(InA_app_iff _). tauto. Qed.

  Lemma equivlistA_app_comm l₁ l₂ : equivlistA eqA (l₁ ++ l₂) (l₂ ++ l₁).
  Proof. split; apply InA_comm. Qed.

  Lemma InA_app_idem z l : InA eqA z (l ++ l) ↔ InA eqA z l.
  Proof. rewrite (InA_app_iff _). tauto. Qed.

  Lemma equivlistA_app_idem l : equivlistA eqA (l ++ l) l.
  Proof. split; apply InA_app_idem. Qed.

  Global Instance: Proper (equivlistA eqA ==> equivlistA eqA ==> equivlistA eqA) (@app A).
  Proof. intros ?? E1 ?? E2 ?. rewrite !(InA_app_iff _), E1, E2. tauto. Qed.

  Inductive PermutationA : list A → list A → Prop :=
    | permA_nil: PermutationA [] []
    | permA_skip x₁ x₂ l₁ l₂ : eqA x₁ x₂ → PermutationA l₁ l₂ → PermutationA (x₁ :: l₁) (x₂ :: l₂)
    | permA_swap x y l : PermutationA (y :: x :: l) (x :: y :: l)
    | permA_trans l₁ l₂ l₃ : PermutationA l₁ l₂ → PermutationA l₂ l₃ -> PermutationA l₁ l₃.
  Hint Constructors PermutationA.

  Global Instance: Equivalence PermutationA.
  Proof.
    split.
      intros l. induction l; intuition.
     intros l₁ l₂. induction 1; eauto. apply permA_skip; intuition.
    intros ???. now apply permA_trans.
  Qed.

  Global Instance PermutationA_cons :
    Proper (eqA ==> PermutationA ==> PermutationA) (@cons A).
  Proof. repeat intro. now apply permA_skip. Qed.

  Lemma PermutationA_app_head l₁ l₂ k :
    PermutationA l₁ l₂ → PermutationA (k ++ l₁) (k ++ l₂).
  Proof. intros. induction k. easy. apply permA_skip; intuition. Qed.

  Global Instance PermutationA_app :
    Proper (PermutationA ==> PermutationA ==> PermutationA) (@app A).
  Proof.
    intros  l₁ l₂ Pl k₁ k₂ Pk.
    induction Pl.
       easy.
      now apply permA_skip.
     etransitivity.
      rewrite <-!app_comm_cons. now apply permA_swap.
     rewrite !app_comm_cons. now apply PermutationA_app_head.
    do 2 (etransitivity; try eassumption).
    apply PermutationA_app_head. now symmetry.
  Qed.

  Lemma PermutationA_app_tail l₁ l₂ k :
    PermutationA l₁ l₂ → PermutationA (l₁ ++ k) (l₂ ++ k).
  Proof. intros E. now rewrite E. Qed.

  Lemma PermutationA_cons_append l x :
    PermutationA (x :: l) (l ++ x :: nil).
  Proof. induction l. easy. simpl. rewrite <-IHl. intuition. Qed.

  Lemma PermutationA_app_comm l₁ l₂ :
    PermutationA (l₁ ++ l₂) (l₂ ++ l₁).
  Proof.
    induction l₁.
     now rewrite app_nil_r.
    rewrite <-app_comm_cons, IHl₁.
    now rewrite app_comm_cons, PermutationA_cons_append, <-app_assoc.
  Qed.

  Lemma PermutationA_cons_app l l₁ l₂ x :
    PermutationA l (l₁ ++ l₂) → PermutationA (x :: l) (l₁ ++ x :: l₂).
  Proof.
    intros E. rewrite E.
    now rewrite app_comm_cons, PermutationA_cons_append, <-app_assoc.
  Qed.

  Lemma PermutationA_middle l₁ l₂ x :
    PermutationA (x :: l₁ ++ l₂) (l₁ ++ x :: l₂).
  Proof. now apply PermutationA_cons_app. Qed.

  Lemma PermutationA_equivlistA l₁ l₂ :
    PermutationA l₁ l₂ → equivlistA eqA l₁ l₂.
  Proof.
    induction 1.
       reflexivity.
      now apply equivlistA_cons_proper.
     now apply equivlistA_permute_heads.
    etransitivity; eassumption.
  Qed.

  Lemma NoDupA_equivlistA_PermutationA l₁ l₂ :
    NoDupA eqA l₁ → NoDupA eqA l₂ → equivlistA eqA l₁ l₂ → PermutationA l₁ l₂.
  Proof.
    intros Pl₁. revert l₂. induction Pl₁ as [|x l₁ E1].
     intros. now rewrite equivlistA_nil_eq by now symmetry.
    intros l₂ Pl₂ E2.
    destruct (@InA_split _ eqA l₂ x) as [l₂h [y [l₂t [E3 ?]]]].
     rewrite <-E2. intuition.
    subst. transitivity (y :: l₁); [intuition |].
    apply PermutationA_cons_app, IHPl₁.
     now apply NoDupA_split with y.
    apply equivlistA_NoDupA_split with x y; intuition.
  Qed.
End equivlistA_misc.

Implicit Arguments PermutationA [[A]].

(*
We define finite sets as unordered lists. This implementation is slow,
but quite convenient as a reference implementation to lift properties to
arbitrary finite set instances.
*)
Instance listset A `{Equiv A} : SetType A | 30 := sig (NoDupA (=)).

Section listset.
Context `{Setoid A} `{∀ a₁ a₂ : A, Decision (a₁ = a₂)}.

Instance listset_in_raw: Contains A (list A) := InA (=).
Instance listset_equiv_raw: Equiv (list A) := equivlistA (=).
Instance: Setoid (list A) := {}.

Instance listset_empty_raw: Bottom (list A) := [].
Instance listset_join_raw: Join (list A) := @app A.
Instance: BoundedJoinSemiLattice (list A).
Proof.
  split. split. split. split. apply _.
       repeat intro. now apply equivlistA_app_ass.
      apply _.
     repeat intro. now apply equivlistA_app_nil_l.
    repeat intro. now apply equivlistA_app_nil_r.
   repeat intro. now apply equivlistA_app_comm.
  repeat intro. now apply equivlistA_app_idem.
Qed.

Global Instance listset_to_list: Cast (set_type A) (list A) := @proj1_sig _ _.
Global Instance listset_in: SetContains A := λ x l, x ∈ 'l.
Global Instance listset_le: SetLe A := λ l k, ∀ x, x ∈ l → x ∈ k.
Global Instance listset_equiv: SetEquiv A := λ l k, ∀ x, x ∈ l ↔ x ∈ k.

Instance: Setoid (set_type A).
Proof. now apply (setoids.projected_setoid listset_to_list). Qed.

Global Instance: Setoid_Morphism listset_to_list.
Proof. firstorder. Qed.
Global Instance: Injective listset_to_list.
Proof. firstorder. Qed.

Global Instance: Proper ((=) ==> (=) ==> iff) listset_in.
Proof.
  intros x y E1 l k E2.
  transitivity (listset_in x k). easy.
  unfold listset_in. now rewrite E1.
Qed.

Fixpoint listset_add_raw (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | y :: l => y :: if decide_rel (=) x y then l else listset_add_raw x l
  end.

Lemma listset_add_raw_cons l x :
  x :: l = listset_add_raw x l.
Proof.
  induction l; simpl; try reflexivity.
  case (decide_rel _); intros E.
   now rewrite E, equivlistA_double_head.
  now rewrite equivlistA_permute_heads, IHl.
Qed.

Lemma listset_add_raw_InA (l : list A) (x y : A) :
  y ∈ listset_add_raw x l → y = x ∨ y ∈ l.
Proof.
  unfold contains, listset_in_raw. induction l; simpl.
   intros E. inversion_clear E; auto.
  case (decide_rel _); auto; intros E1 E2.
  inversion_clear E2; intuition.
Qed.

Lemma listset_add_raw_NoDupA (l : list A) (x : A) :
  NoDupA (=) l → NoDupA (=) (listset_add_raw x l).
Proof.
  intros Pl. induction l; simpl.
   now apply NoDupA_singleton.
  case (decide_rel _); intros E1; auto.
  inversion_clear Pl.
  apply NoDupA_cons; auto.
  intros E2. destruct (listset_add_raw_InA _ _ _ E2); intuition.
Qed.

Global Program Instance listset_empty: EmptySet A := [].
Global Program Instance listset_singleton: SetSingleton A := λ x, [x].
Next Obligation. now apply NoDupA_singleton. Qed.
Global Program Instance listset_join: SetJoin A := λ l k, fold_right listset_add_raw (`k) (`l)↾_.
Next Obligation.
  destruct l as [l Pl], k as [k Pk].
  induction l; intros; simpl in *; auto.
  apply listset_add_raw_NoDupA, IHl. now inversion Pl.
Qed.

Instance: Setoid_Morphism listset_singleton.
Proof.
  split; try apply _. intros ? ? E.
  apply (injective listset_to_list). change ([x] = [y]). now rewrite E.
Qed.

Lemma listset_to_list_preserves_join l k :
  listset_to_list (l ⊔ k) = listset_to_list l ⊔ listset_to_list k.
Proof.
  destruct l as [l Pl], k as [k Pk].
  unfold join, listset_join, listset_join_raw. simpl. clear Pk Pl.
  induction l; simpl; intros; [easy|].
  now rewrite <-IHl, listset_add_raw_cons.
Qed.

Instance: BoundedJoinSemiLattice (set_type A).
Proof.
  apply (projected_bounded_sl listset_to_list).
   intros. now apply listset_to_list_preserves_join.
  reflexivity.
Qed.

Lemma listset_in_join l k x : x ∈ l ⊔ k ↔ x ∈ l ∨ x ∈ k.
Proof.
  unfold contains, listset_in_raw, listset_in.
  rewrite listset_to_list_preserves_join.
  now apply InA_app_iff.
Qed.

Instance: JoinSemiLatticeOrder listset_le.
Proof.
  apply alt_Build_JoinSemiLatticeOrder. intros l k.
  unfold le, listset_le, equiv, listset_equiv.
  setoid_rewrite listset_in_join. firstorder auto.
Qed.

Lemma listset_induction (P : set_type A → Prop) `{proper : !Proper ((=) ==> iff) P} :
  P ∅ → (∀ x l, x ∉ l → P l → P ({{ x }} ⊔ l)) → ∀ l, P l.
Proof.
  intros Pempty Padd.
  intros [l Pl]. induction l as [|x l].
   apply proper with ∅; firstorder.
  inversion_clear Pl as [|??? Pl'].
  apply proper with ({{ x }} ⊔ l↾Pl'); auto.
  intros z. change (z ∈ x :: l ↔ z ∈ listset_add_raw x l).
  now rewrite listset_add_raw_cons.
Qed.

Fixpoint listset_extend_raw `{Bottom B} `{Join B} (f : A → B) (l : list A) : B :=
  match l with
  | [] => ⊥
  | x :: l => f x ⊔ listset_extend_raw f l
  end.

Global Instance list_extend: FSetExtend A := λ _ _ _ f l, listset_extend_raw f (`l).

Section listset_extend.
  Context `{BoundedJoinSemiLattice B} `{!Setoid_Morphism (f : A → B)}.

  Lemma listset_extend_raw_permute (l k : list A) :
    PermutationA (=) l k → listset_extend_raw f l = listset_extend_raw f k.
  Proof.
    induction 1; simpl.
       reflexivity.
      apply sg_op_proper. now apply sm_proper. easy.
     now rewrite !associativity, (commutativity (f _)).
    etransitivity; eassumption.
  Qed.

  Instance list_extend_proper: Proper (equiv ==> equiv) (fset_extend f).
  Proof.
    intros [??][??] ?.
    apply listset_extend_raw_permute. now apply NoDupA_equivlistA_PermutationA.
  Qed.

  Lemma list_extend_empty:
    fset_extend f ∅ = ⊥.
  Proof. reflexivity. Qed.

  Lemma list_extend_add x l :
    fset_extend f ({{x}} ⊔ l) = f x ⊔ fset_extend f l.
  Proof.
    destruct l as [l Pl]. unfold fset_extend, list_extend. simpl. clear Pl.
    induction l; simpl; [easy|].
    case (decide_rel _); intros E.
     now rewrite E, associativity, (idempotency (&) _).
    now rewrite IHl, 2!associativity, (commutativity (f _)).
  Qed.

  Instance list_extend_mor:
    BoundedJoinSemiLattice_Morphism (fset_extend f).
  Proof.
    repeat (split; try apply _).
     intros l k. change (fset_extend f (l ⊔ k) = fset_extend f l ⊔ fset_extend f k).
     pattern l. apply listset_induction; clear l.
       solve_proper.
      now rewrite list_extend_empty, 2!left_identity.
     intros x l E1 E2.
     now rewrite <-associativity, 2!list_extend_add, E2, associativity.
    reflexivity.
  Qed.
End listset_extend.

Local Existing Instance list_extend_mor.

Global Instance: FSet A.
Proof.
  split; try apply _.
   intros B ???? f ? x y E.
   unfold compose, fset_extend, list_extend. simpl.
   now rewrite E, right_identity.
  intros B ??? f ? h ? E1 k l E2.
  pose proof (bounded_join_slmor_b (f:=h)).
  rewrite E2. clear k E2. pattern l.
  apply listset_induction; clear l.
    solve_proper.
   now rewrite preserves_bottom.
  intros x l E2 E3. rewrite list_extend_add, preserves_join, E3.
  apply sg_op_proper; [|easy]. symmetry. now apply E1.
Qed.

Instance: FSetContainsSpec A.
Proof.
  split; try apply _. unfold le, listset_le.
  intros x X; split; intros E1.
   intros z E2. inversion_clear E2 as [?? E3|?? E3].
    now rewrite E3.
   now inversion E3.
  apply E1. now rapply InA_cons_hd.
Qed.

Instance listset_in_raw_dec: ∀ x (l : list A), Decision (x ∈ l) := λ x l, InA_dec (decide_rel (=)) x l.
Global Instance listset_in_dec: ∀ x (l : set_type A), Decision (x ∈ l) := λ x l, InA_dec (decide_rel (=)) x ('l).

Instance listset_meet_raw: Meet (list A) :=
  fix listset_meet_raw l k :=
    match l with
    | [] => []
    | x :: l => if decide_rel (∈) x k then x :: listset_meet_raw l k else listset_meet_raw l k
    end.

Lemma listset_in_meet_raw l k x :
  x ∈ l ⊓ k ↔ x ∈ l ∧ x ∈ k.
Proof.
  unfold meet, contains, listset_in_raw. split.
   intros E; split; revert E.
    induction l; simpl.
     intuition.
    case (decide_rel _); intros ? E; intuition.
    inversion_clear E; intuition.
   induction l; simpl.
    intros E1; inversion E1.
   case (decide_rel _); intros ? E1; intuition.
   inversion_clear E1 as [?? E2|]; auto. now rewrite E2.
  intros [E1 E2]. induction l; simpl; [easy|].
  case (decide_rel _); intros E3.
   inversion_clear E1; intuition.
  inversion_clear E1 as [?? E4|]; intuition.
  destruct E3. now rewrite <-E4.
Qed.

Lemma listset_meet_raw_NoDupA (l k : list A) :
  NoDupA (=) l → NoDupA (=) (l ⊓ k).
Proof.
  unfold meet. intros Pl. induction l; simpl; auto.
  inversion_clear Pl as [|? ? E1].
  case (decide_rel _); intros; auto.
  apply NoDupA_cons; auto.
  intros E2. destruct E1. now apply (listset_in_meet_raw l k _).
Qed.

Global Program Instance listset_meet: SetMeet A := λ l k, listset_meet_raw l k.
Next Obligation. apply listset_meet_raw_NoDupA. now destruct l. Qed.

Instance listset_diff_raw: Difference (list A) :=
  fix listset_diff_raw l k :=
    match l with
    | [] => []
    | x :: l => if decide_rel (∈) x k then listset_diff_raw l k else x :: listset_diff_raw l k
    end.

Lemma listset_in_diff_raw l k x :
  x ∈ l ∖ k ↔ x ∈ l ∧ x ∉ k.
Proof.
  unfold difference, contains, listset_in_raw. split.
   intros E; split; revert E.
    induction l; simpl.
     intuition.
    case (decide_rel _); intros ? E; intuition.
    inversion_clear E; intuition.
   induction l; simpl.
    intros E1; inversion E1.
   case (decide_rel _); intros ? E1.
    intuition.
   inversion_clear E1 as [?? E2|]; auto. now rewrite E2.
  intros [E1 E2]. induction l; simpl; [easy|].
  case (decide_rel _); intros E3.
   inversion_clear E1 as [?? E4|]; intuition.
   destruct E2. now rewrite E4.
  inversion_clear E1; intuition.
Qed.

Lemma listset_diff_raw_NoDupA (l k : list A) :
  NoDupA (=) l → NoDupA (=) (l ∖ k).
Proof.
  unfold difference. intros Pl. induction l; simpl; auto.
  inversion_clear Pl as [|? ? E1].
  case (decide_rel _); intros; auto.
  apply NoDupA_cons; auto.
  intros E2. destruct E1. now apply (listset_in_diff_raw l k _).
Qed.

Global Program Instance listset_diff: SetDifference A := λ l k, listset_diff_raw l k.
Next Obligation. apply listset_diff_raw_NoDupA. now destruct l. Qed.

Global Instance: FullFSet A | 30.
Proof.
  split; try apply _.
   intros [??] [??]. now rapply listset_in_meet_raw.
  intros [??] [??]. now rapply listset_in_diff_raw.
Qed.
End listset.
