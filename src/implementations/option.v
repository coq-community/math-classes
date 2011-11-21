Require Import
  Morphisms Program
  abstract_algebra interfaces.monads jections.

Inductive option_equiv A `{Equiv A} : Equiv (option A) :=
  | option_equiv_Some : Proper ((=) ==> (=)) Some
  | option_equiv_None : None = None.

Existing Instance option_equiv.
Hint Constructors option_equiv.

Section contents.
  Context `{Setoid A}.

  Lemma Some_ne_None x : Some x ≠ None.
  Proof. intros E. inversion E. Qed.

  Lemma None_ne_Some x : None ≠ Some x.
  Proof. intros E. inversion E. Qed.

  Global Instance: Setoid (option A).
  Proof.
    split.
      intros [x|]. now apply option_equiv_Some. now apply option_equiv_None.
     red. induction 1. now apply option_equiv_Some. now apply option_equiv_None.
    intros x y z E. revert z. induction E.
     intros z E2. inversion_clear E2.
     apply option_equiv_Some. etransitivity; eassumption.
    easy.
  Qed.

  Global Instance: Setoid_Morphism Some.
  Proof. split; try apply _. now apply option_equiv_Some. Qed.

  Global Instance: Injective Some.
  Proof. split; try apply _. intros ? ? E. now inversion E. Qed.

  Lemma option_equiv_alt x y :
    x = y ↔ (∀ n, x = Some n ↔ y = Some n).
  Proof.
    split; intros E1.
     intro. now rewrite E1.
    destruct x, y.
       now apply E1.
      symmetry. now apply E1.
     now apply E1.
    easy.
  Qed.

  Program Instance option_dec `(A_dec : ∀ x y : A, Decision (x = y))
     : ∀ x y : option A, Decision (x = y) := λ x y,
    match x with
    | Some r =>
      match y with
      | Some s => match A_dec r s with left _ => left _ | right _ => right _ end
      | None => right _
      end
    | None =>
      match y with
      | Some s => right _
      | None => left _
      end
    end.
  Next Obligation. now apply sm_proper. Qed.
  Next Obligation. now apply (injective_ne Some). Qed.
  Next Obligation. apply Some_ne_None. Qed.
  Next Obligation. apply None_ne_Some. Qed.
End contents.

Hint Extern 10 (Equiv (option _)) => apply @option_equiv : typeclass_instances.

Instance option_ret: MonadReturn option := λ A x, Some x.
Instance option_bind: MonadBind option := λ A B x f,
  match x with
  | Some a => f a
  | None => None
  end.

Instance option_ret_proper `{Equiv A} : Proper ((=) ==> (=)) (option_ret A).
Proof. intros x y E. now apply option_equiv_Some. Qed.

Instance option_bind_proper `{Setoid A} `{Setoid B}: Proper (=) (option_bind A B).
Proof.
  intros x₁ x₂. destruct 1.
   intros f₁ f₂ E₂. unfold option_bind. simpl. now apply E₂.
  easy.
Qed.

Instance: Monad option.
Proof.
  repeat (split; try apply _); unfold bind, ret, option_bind, option_ret.
    easy.
   now intros ? ? ? [x|].
  intros ? ? ? ? ? ? ? ? ? [x|] f g.
   now destruct (f x).
  easy.
Qed.

Section map.
  Context `{Setoid A} `{Setoid B} `{!Injective (f : A → B)}.

  Global Instance: Injective (map f).
  Proof.
    pose proof (injective_mor f).
    repeat (split; try apply _).
    intros [x|] [y|] E; try solve [inversion E | easy].
    apply sm_proper. apply (injective f). now apply (injective Some).
  Qed.
End map.
