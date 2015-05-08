Require
  MathClasses.misc.JMrelation.
Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.functors MathClasses.theory.categories.

Record Object := object
  { obj:> Type
  ; Arrows_inst: Arrows obj
  ; Equiv_inst: ∀ x y: obj, Equiv (x ⟶ y)
  ; CatId_inst: CatId obj
  ; CatComp_inst: CatComp obj
  ; Category_inst: Category obj }.

Arguments object _ {Arrows_inst Equiv_inst CatId_inst CatComp_inst Category_inst}.
Existing Instance Arrows_inst.
Existing Instance Equiv_inst.
Existing Instance CatId_inst.
Existing Instance CatComp_inst.
Existing Instance Category_inst.

Record Arrow (x y: Object): Type := arrow
  { map_obj:> obj x → obj y
  ; Fmap_inst: Fmap map_obj
  ; Functor_inst: Functor map_obj _ }.

Arguments arrow {x y} _ _ _.
Arguments map_obj {x y} _ _.
Existing Instance Fmap_inst.
Existing Instance Functor_inst.

Instance: Arrows Object := Arrow.
(* Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances. *)

Section contents.
  Section more_arrows.
    Context (x y: Object).

    Global Instance e: Equiv (x ⟶ y) := λ a b,
      (∀ v, a v ≡ b v) ∧
      (∀ `(f: v ⟶ w), JMrelation.R (=) (fmap a f) _ (=) (fmap b f)).

    Instance e_refl: Reflexive e.
    Proof.
     intro a. unfold e. intuition.
     apply JMrelation.reflexive, _.
    Qed.

    Instance e_sym: Symmetric e.
    Proof with intuition.
     unfold e. intros ?? [P Q]...
     apply JMrelation.symmetric...
    Qed.

    Instance e_trans: Transitive e.
    Proof with intuition.
     unfold e. intros a b c [P Q] [R S]...
      transitivity (b v)...
     apply JMrelation.transitive with _ (=) (fmap b f)...
    Qed.

    Global Instance: Setoid (x ⟶ y).
    Proof. split; apply _. Qed.
  End more_arrows.

  Global Instance: CatId Object := λ _, arrow id _ _.

  Global Program Instance: CatComp Object := λ _ _ _ x y, arrow (x ∘ y) _ _.

  Global Instance: ∀ x y z: Object, Proper ((=) ==> (=) ==> (=)) ((◎): (y ⟶ z) → (x ⟶ y) → (x ⟶ z)).
  Proof with intuition; try apply _.
   unfold equiv, e.
   intros x y z a b [P Q] c d [R S].
   split; intros.
    change (a (c v) ≡ b (d v)). congruence.
   change (JMrelation.R (=) (fmap a (fmap c f)) _ (=) (fmap b (fmap d f))).
   apply JMrelation.transitive with _ (=) (fmap a (fmap d f))...
   specialize (S _ _ f). revert S.
   generalize (fmap c f) (fmap d f).
   repeat rewrite R.
   intros. apply JMrelation.relate.
   rewrite (JMrelation.unJM _ _ _ _ _ S)... (* <- uses K *)
  Qed.

  Global Instance: Category Object.
  Proof. repeat (split; try apply _); intuition; apply reflexivity. Qed.
End contents.
