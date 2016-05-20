Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.universal_algebra MathClasses.interfaces.monads.

Section contents.
  Context (operation: Set) (operation_type: operation → OpType unit).

  Let sign := Build_Signature unit operation operation_type.

  (* The monad's type constructor: *)
  Definition M (T: Type): Type := Term sign T (ne_list.one tt).

  (* We first define equality for arbitrary arities, and then instantiate for constants. *)
  Section equality.
    Context `{Setoid A}.

    Fixpoint geneq {s s'} (x: Term sign A s) (y: Term sign A s'): Prop :=
      match x, y with
      | Var _ _ v _, Var _ _ w _ => v = w
      | App _ _ _ z t t', App _ _ _ z' t'' t''' => geneq t t'' ∧ geneq t' t'''
      | Op _ _ o, Op _ _ o' => o ≡ o'
      | _, _ => False
      end.

    Lemma geneq_sym s (x: Term sign A s): ∀ s' (y: Term sign A s'), geneq x y → geneq y x.
    Proof with intuition.
     induction x.
       destruct y...
       simpl. symmetry...
      destruct y0... simpl in *...
     destruct y... simpl in *...
    Qed.

    Lemma geneq_trans s (x: Term sign A s): ∀ s' (y: Term sign A s') s'' (z: Term sign A s''),
      geneq x y → geneq y z → geneq x z.
    Proof with simpl in *; intuition.
     induction x; simpl.
       destruct y, z...
      destruct y0...
      destruct z... eauto. eauto.
     destruct y, z...
     transitivity o0...
    Qed.

    Global Instance gen_equiv: Equiv (M A) := geneq.

    Global Instance: Setoid (M A).
    Proof.
      split.
        intros x. unfold M, equiv, gen_equiv in *. induction x; simpl; intuition.
       repeat intro. now apply geneq_sym.
      repeat intro. now apply geneq_trans with _ y.
    Qed.
  End equality.

  (* For bind, we do the same: *)
  Definition gen_bind_aux {A B: Type} (f: A → M B): ∀ {s}, Term sign A s → Term sign B s
    := fix F {s} (t: Term sign A s): Term sign B s :=
      match t with
      | Var _ _ v tt => f v
      | App _ _ o z x y => App _ _ _ z (F x) (F y)
      | Op _ _ o => Op _ _ o
      end.

  Arguments gen_bind_aux {A B} _ {s} _.

  Instance gen_bind: MonadBind M := λ _ _ f z, gen_bind_aux f z.

  Instance: ∀ `{Equiv A} `{Equiv B},
    Proper (((=) ==> (=)) ==> (=) ==> (=)) (@bind M _ A B).
  Proof with intuition.
   intros A H1 B H2 x0 y0 E' x y E.
   revert x y E.
   change (∀ x y : M A, geneq x y → geneq (gen_bind_aux x0 x) (gen_bind_aux y0 y)).
   cut (∀ s (x: Term sign A s) s' (y: Term sign A s'),
      geneq x y → geneq (gen_bind_aux x0 x) (gen_bind_aux y0 y))...
   revert s' y H.
   induction x.
     destruct y... simpl in *.
     destruct a, a1. apply E'...
    simpl in *. destruct y... destruct y...
    simpl in *... destruct y...
  Qed.

  (* return: *)
  Instance gen_ret: MonadReturn M := λ _ x, Var sign _ x tt.

  Instance: ∀ `{Equiv A}, Proper ((=) ==> (=)) (@ret M _ A).
  Proof. repeat intro. assumption. Qed.

  (* What remains are the laws: *)
  Instance: Monad M.
  Proof with intuition.
   constructor; intros; try apply _.
     (* law 1 *)
     now apply setoids.ext_equiv_refl.
    (* law 2 *)
    intros m n E. rewrite <-E. clear E n. unfold M in m.
    change (geneq (gen_bind_aux (λ x : A, Var sign A x tt) m) m).
    induction m; simpl...
    destruct a... simpl...
   (* law 3 *)
   intros m n E. rewrite E. clear E m.
   unfold bind, gen_bind, equiv, gen_equiv.
   revert n. assert (∀ o (m : Term sign A o),
     geneq (gen_bind_aux f (gen_bind_aux g m))
     (gen_bind_aux (λ x : A, gen_bind_aux f (g x)) m)) as H.
    induction m; simpl...
    destruct a.
    change (gen_bind_aux f (g v) = gen_bind_aux f (g v))...
   now apply H.
  Qed.
End contents.
