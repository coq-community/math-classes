Require Import
  abstract_algebra universal_algebra interfaces.monads canonical_names.

Section contents.

  Context (operation: Set) (operation_type: operation → OpType unit).

  Let sign := Build_Signature unit operation operation_type.

  (* The monad's type constructor: *)

  Definition M (T: Type): Type := Term sign T (ne_list.one tt).

  (* We first define equality for arbitrary arities, and then instantiate for constants. *)

  Section equality.

    Context {A: Type} `{Setoid A}.

    Fixpoint geneq {s s'} (x: Term sign A s) (y: Term sign A s'): Prop :=
      match x, y with
      | Var v _, Var w _ => v = w
      | App _ z t t', App _ z' t'' t''' => geneq t t'' ∧ geneq t' t'''
      | Op o, Op o' => o ≡ o'
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
       destruct y, z... transitivity a0...
      destruct y0...
      destruct z... eauto. eauto.
     destruct y, z...
     transitivity o0...
    Qed.

    Global Instance Me: Equiv (M A) := geneq.

    Instance: Symmetric Me.
    Proof. repeat intro. apply geneq_sym. assumption. Qed.

    Instance: Transitive Me.
    Proof. repeat intro. apply geneq_trans with _ y; assumption. Qed.

    Instance: Reflexive Me.
    Proof with intuition.
     unfold Me, Reflexive, M.
     induction x; simpl; intuition.
    Qed.

    Global Instance: Setoid (M A).
    Proof. split; apply _. Qed.
  End equality.

  (* For bind, we do the same: *)

  Definition gen_bind {A B: Type} (f: A → M B): ∀ {s}, Term sign A s → Term sign B s
    := fix F {s} (t: Term sign A s): Term sign B s :=
      match t with
      | Var v tt => f v
      | App o z x y => App _ _ _ z (F x) (F y)
      | Op o => Op _ _ o
      end.

  Implicit Arguments gen_bind [[A] [B] [s]].

  Instance: MonadBind M := λ _ _ z f, gen_bind f z.

  Instance: ∀ `{Equiv A} `{Equiv B},
    Proper ((=) ==> ((=) ==> (=)) ==> (=)) (@bind M _ A B).
  Proof with intuition.
   intros A H1 B H2 x y E x0 y0 E'.
   revert x y E.
   change (∀ x y : M A, geneq x y → geneq (gen_bind x0 x) (gen_bind y0 y)).
   cut (∀ s (x: Term sign A s) s' (y: Term sign A s'),
      geneq x y → geneq (gen_bind x0 x) (gen_bind y0 y))...
   revert s' y H.
   induction x.
     destruct y... simpl in *.
     destruct a, a1. apply E'...
    simpl in *. destruct y... destruct y...
    simpl in *... destruct y...
  Qed.

  (* return: *)

  Instance: MonadReturn M := λ _ x, Var sign _ x tt.

  Instance: ∀ `{Equiv A}, Proper ((=) ==> (=)) (@ret M _ A).
  Proof. repeat intro. assumption. Qed.

  (* What remains are the laws: *)

  Instance: Monad M.
  Proof with intuition.
   constructor; intros; try apply _.
     (* law 1 *)
     reflexivity.
    (* law 2 *)
    unfold M in *.
    change (geneq (gen_bind (λ x : A, Var sign A x tt) m) m).
    induction m; simpl...
    destruct a... simpl...
   (* law 3 *)
   unfold M, bind.
   unfold MonadBind_instance_0.
   unfold equiv, Me.
   unfold M in n.
   revert n.
   cut (∀ o (n: Term sign A o),
     geneq (gen_bind g (gen_bind f n))
     (gen_bind (λ x : A, gen_bind g (f x)) n))...
   induction n; simpl...
   destruct a.
   change (gen_bind g (f v) = gen_bind g (f v))...
  Qed.

End contents.
