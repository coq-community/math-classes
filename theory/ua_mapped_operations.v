Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.universal_algebra.

Section contents.
  Variable Sorts: Set.

  Section map_op.
    (* Given maps between two realizations of the sorts, there are maps between the corresponding op_types*)
    Context {A B: Sorts → Type}
      `{∀ a, Equiv (A a)} `{∀ a, Equiv (B a)}
      (ab: ∀ a, A a → B a)
      (ba: ∀ a, B a → A a)
      `{∀ a, Proper ((=) ==> (=)) (ab a)}
      `{∀ a, Proper ((=) ==> (=)) (ba a)}.

    Fixpoint map_op {o: OpType Sorts}: op_type A o → op_type B o :=
      match o return op_type A o → op_type B o with
      | ne_list.one u => ab u
      | ne_list.cons _ _ => λ x y, map_op (x (ba _ y))
      end.

    Global Instance map_op_proper o: Proper ((=) ==> (=)) (@map_op o).
    Proof. unfold equiv. induction o; simpl; firstorder. Qed.
      (* todo: can't we make this nameless? *)
  End map_op.

  (* If the maps between the sorts are eachother's inverse, then so are the two generated op_type maps: *)

  Context {A B: Sorts → Type} {e: ∀ a, Equiv (B a)} `{∀ b, Equivalence (e b)}
   (ab: ∀ a, A a → B a) (ba: ∀ a, B a → A a).

  Arguments ab [a] _.
  Arguments ba [a] _.

  Context `(iso: ∀ a (x: B a), ab (ba x) = x).

  Lemma map_iso o (x: op_type B o) (xproper: Proper (=) x):
    map_op ab ba (map_op ba ab x) = x.
  Proof with auto; try reflexivity.
   induction o; simpl; intros...
   intros x0 y H0.
   change (map_op ab ba (map_op ba ab (x (ab (ba x0)))) = x y).
   transitivity (x (ab (ba x0))).
    apply IHo, xproper...
   apply xproper. rewrite iso, H0...
  Qed.
End contents.
