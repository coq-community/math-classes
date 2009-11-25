Require Import Program Relation_Definitions Structures Morphisms RingOps CatStuff.

Section contents.

  Inductive O: Type := MkO A `{Ring A}.

  Definition A (X Y: O): Type :=
    match X, Y with
    | MkO XT _ _ _ _ _ _ _, MkO YT _ _ _ _ _ _ _ => sig (@Ring_Morphism XT YT _ _ _ _ _ _ _ _ _ _ _ _)
    end.

  Global Program Instance: CatId O A := fun o =>
    match o with
    | MkO X _ _ _ _ _ _ _ => id
    end.

  Next Obligation. repeat (constructor; try apply _); intros; reflexivity. Qed.

  Global Program Instance: CatComp O A := fun x y z =>
   match x, y, z with
   | MkO X _ _ _ _ _ _ _, MkO Y _ _ _ _ _ _ _, MkO Z _ _ _ _ _ _ _ => fun f g v => f (g v)
   end.

  Next Obligation. Proof. apply _. Qed.

  Global Instance o_equiv: Equiv O := eq.
  Global Instance a_equiv (x y: O): Equiv (A x y) :=
    match x, y return relation (A x y) with
    | MkO XT _ _ _ _ _ _ _, MkO YT _ _ _ _ _ _ _ => fun a a' => pointwise_relation _ equiv (proj1_sig a) (proj1_sig a')
    end.

  Global Instance: Category O A.
  Proof with auto.
   constructor; try apply _.
       intros.
       unfold a_equiv.
       destruct x. destruct y.
       constructor; repeat intro.
         reflexivity.
        symmetry...
       transitivity ((`y) a)...
      intros x y z. destruct x. destruct y. destruct z.
      intros [x r] [y r0] H2 [x0 r1] [y0 r2] H3 a.
      simpl. rewrite (H3 a). apply H2.
     intros. destruct w. destruct y. destruct z. destruct x. intro. reflexivity.
    intros. destruct x. destruct y. intro. reflexivity.
   intros. destruct x. destruct y. intro. reflexivity.
  Qed.

End contents.
