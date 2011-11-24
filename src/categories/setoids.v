Require Import
  Relation_Definitions abstract_algebra theory.categories.

Inductive Object := object { T:> Type; e: Equiv T; setoid_proof: Setoid T }.

Existing Instance e.
Existing Instance setoid_proof.

Section contents.
  Global Instance Arrow: Arrows Object := λ A B, sig (@Setoid_Morphism A B _ _).

  Global Program Instance: ∀ x y: Object, Equiv (x ⟶ y) := λ _ _, respectful (=) (=).

  Global Instance: ∀ x y: Object, Setoid (x ⟶ y).
  Proof with intuition.
   intros x y.
   constructor.
     intros [? ?] ? ? E. now rewrite E.
    intros ? ? E ? ? ?. symmetry...
   intros [f Pf] [g Pg] [h Ph] E1 E2 a b E3. simpl.
   transitivity (g a)...
  Qed.

  Global Program Instance: CatId Object := λ _, id.

  Local Obligation Tactic := idtac.
  Global Program Instance: CatComp Object := λ _ _ _, compose.
  Next Obligation. intros ? ? ? [? ?] [? ?]. apply _. Qed.

  Instance: ∀ x y z: Object, Proper ((=) ==> (=) ==> (=)) (comp x y z).
  Proof. repeat intro. simpl. firstorder. Qed.

  Global Instance: Category Object.
  Proof.
   constructor; try apply _.
     intros ? ? ? ? [??] [??] [??] ? ? E. simpl. now rewrite E.
    intros ? ? [??] ? ? E. simpl. now rewrite E.
   intros ? ? [??] ? ? E. simpl. now rewrite E.
  Qed.

  Global Instance: Producer Object := λ _ c, object (∀ i, c i) (λ x y, ∀ i, x i = y i) _.
    (* todo: use pointwise_relation or something like that *)

  Section product.
    Context {Index: Type} (c: Index → Object).

    Global Program Instance: ElimProduct c (product c) := λ i x, x i.
    Next Obligation. constructor; try apply _. firstorder. Qed.

    Global Program Instance: IntroProduct c (product c) := λ d df x y, df y x.
    Next Obligation. constructor; try apply _. repeat intro. destruct df. simpl. firstorder. Qed.

    Global Instance: Product c (product c).
    Proof.
     split.
      intros ? ? ? E. simpl. unfold compose. destruct ccomp. rewrite E. reflexivity.
     intros ? E' ? x E i. simpl in *.
     symmetry in E |- *.
     apply (E' i _ _ E).
    Qed.
  End product.

  Global Instance: HasProducts Object := {}.

  Global Instance mono (X Y: Object) (a: X ⟶ Y): Injective (` a) → Mono a.
  Proof. intros A ??? E1 ?? E2. apply A. apply (E1 _ _ E2). Qed.
End contents.

Implicit Arguments object [] [[setoid_proof]] [[e] [setoid_proof]].
