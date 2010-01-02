Set Automatic Introduction.

Require Import
  Morphisms Setoid abstract_algebra Program
  universal_algebra categories.ua_variety theory.categories.
Require
  categories.setoid categories.product.

Module setoidcat := categories.setoid.
Module productcat := categories.product.

Section contents.

  Variable et: EquationalTheory.

  Let TargetObject := productcat.Object (sorts et) (fun _ => setoidcat.Object).
  Let TargetArrow := productcat.Arrow (sorts et) (fun _ => setoidcat.Object) (fun _ => setoidcat.Arrow).

  Definition forget_object (v: Variety et): TargetObject := fun i => @setoidcat.Build_Object (v i) equiv _.

  Definition forget_arrow (x y: Variety et) (a: Arrow et x y): TargetArrow (forget_object x) (forget_object y)
    := fun i => setoidcat.Build_Arrow (forget_object x i) (forget_object y i)
      (proj1_sig a i) (@homo_proper et _ _ _ _ _ _ _ (proj2_sig a) i).

  Instance: forall a b, Setoid_Morphism (forget_arrow a b).
  Proof.
   constructor; try apply _.
   intros x y E i A B F. simpl in *.
   pose proof (@homo_proper _ _ _ _ _ _ _ (proj1_sig x) (proj2_sig x)).
     (* todo: shouldn't be necessary. perhaps an [Existing Instance] for
       a specialization of proj2_sig is called for. *)
   rewrite F. apply E.
  Qed.

  Instance forget: Functor forget_object forget_arrow.
  Proof.
   constructor. apply _. repeat intro. assumption.
   intros x y z f g i v w E.
   simpl in *. unfold compose.
   pose proof (@homo_proper _ _ _ _ _ _ _ (proj1_sig f) (proj2_sig f)).
   pose proof (@homo_proper _ _ _ _ _ _ _ (proj1_sig g) (proj2_sig g)).
   rewrite E. reflexivity.
  Qed.

  (* Unfortunately we cannot also define the arrow in Cat because this leads to
   universe inconsistencies. Todo: look into this. *)

End contents.
