(* "Forgetting" a variety's laws (but keeping the algebraic operations) is a trivial functor. *)

Require Import abstract_algebra universal_algebra theory.categories.
Require categories.variety categories.algebra categories forget_algebra.

Section contents.

  Variable et: EquationalTheory.

  Global Instance forget: @ForgetOps
    (variety.Object et) (variety.Arrow et)
    (algebra.Object et) (algebra.Arrow et) :=
    { forget_object := fun v => algebra.object et v
    ; forget_arrow := fun x y => id }.

  Instance functor: ForgetFunctor.
  Proof. constructor. intros. apply _. reflexivity. repeat intro. reflexivity. Qed.

  (* Composing this with forget_algebra gives: *)
(*
  Definition forget_object' (v: variety.Object et): product.Object (sorts et) (fun _ => setoid.Object).
   intros.
   apply (@forget_algebra.object et).
   apply object.
   exact v.
  Qed.
   

 := setoid.object (variety.variety_carriers et v).
*)

End contents.
