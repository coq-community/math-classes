(* "Forgetting" an algebra's operations (but keeping the setoid equality) is a trivial functor.

This functor should nicely compose with the one forgetting variety laws. *)

Require Import
  Morphisms Setoid abstract_algebra universal_algebra theory.categories.
Require
  categories.setoid categories.product categories.algebra.

Section contents.

  Variable sign: Signature.

  Notation TargetObject := (product.Object (sorts sign) (fun _ => setoid.Object)).
  Notation TargetArrow := (product.Arrow (sorts sign) (fun _ => setoid.Object) (fun _ => setoid.Arrow)).

  Definition object (v: algebra.Object sign): TargetObject := fun i => setoid.object (v i) equiv _.
 
  Definition arrow (x y: algebra.Object sign) (a: algebra.Arrow sign x y): TargetArrow (object x) (object y)
    := fun i => setoid.arrow (object x i) (object y i)
      (proj1_sig a i) (@homo_proper sign _ _ _ _ _ _ _ (proj2_sig a) i).

  Global Instance: @ForgetOps _ (algebra.Arrow sign) _ TargetArrow :=
    { forget_object := object; forget_arrow := arrow }.

  Instance: Setoid_Morphism (arrow a b).
  Proof.
   constructor; try apply _.
   intros x y E i A B F. simpl in *.
   destruct (@homo_proper _ _ _ _ _ _ _ (proj1_sig x) (proj2_sig x) i).
     (* todo: shouldn't be necessary. perhaps an [Existing Instance] for
       a specialization of proj2_sig is called for. *)
   rewrite F. apply E.
  Qed.

  Global Instance forget: Functor object arrow.
  Proof.
   constructor. apply _. repeat intro. assumption.
   intros ? ? ? f g i ? ? E.
   simpl in *. unfold Basics.compose.
   destruct (@homo_proper _ _ _ _ _ _ _ (proj1_sig f) (proj2_sig f) i). (* todo: clean up *)
   destruct (@homo_proper _ _ _ _ _ _ _ (proj1_sig g) (proj2_sig g) i).
   rewrite E. reflexivity.
  Qed.

  (* Unfortunately we cannot also define the arrow in Cat because this leads to
   universe inconsistencies. Todo: look into this. *)

End contents.
