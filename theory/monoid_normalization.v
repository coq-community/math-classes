Require Import Coq.omega.Omega.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.theory.ua_packed.
Require MathClasses.interfaces.universal_algebra MathClasses.varieties.monoids.

Notation msig := varieties.monoids.sig.
Notation Op := (universal_algebra.Op msig False).
Notation App := (universal_algebra.App msig False _ _).

Import universal_algebra.

Section contents.
  (* Ideally, we would like to operate exclusively on the universal term representation(s).
   If Coq had decent support for dependent pattern matching, this would be no problem.
   Unfortunately, Coq does not, and so we resort to defining an ad-hoc data type for
   monoidal expressions, with nasty conversions to and from the universal term
   representation(s): *)

  Context (V: Type).

  Notation uaTerm := (universal_algebra.Term0 msig V tt).
  Notation Applied := (@ua_packed.Applied msig V tt).

  Inductive Term := Var (v: V) | Unit | Comp (x y: Term).

  Fixpoint to_ua (e: Term): Applied :=
    match e with
    | Var v => ua_packed.AppliedVar msig v tt
    | Unit => ua_packed.AppliedOp msig monoids.one (ua_packed.NoMoreArguments msig tt)
    | Comp x y => ua_packed.AppliedOp msig monoids.mult
       (MoreArguments msig tt _ (to_ua x) (MoreArguments msig tt _ (to_ua y) (NoMoreArguments msig tt)))
    end.

  Definition from_ua (t: Applied): { r: Term | to_ua r ≡ t }.
  Proof with reflexivity.
    refine (better_Applied_rect msig (λ s,
       match s return (ua_packed.Applied msig s → Type) with
       | tt => λ t, {r : Term | to_ua r ≡ t}
       end) _ _ t).
    simpl.
    intros []; simpl.
     intros.
     exists (Comp (` (fst (forallSplit msig _ _ X)))
       (` ((fst (forallSplit msig _ _ (snd (forallSplit msig _ _ X))))))).
     do 3 dependent destruction x.
     simpl in *.
     destruct X. destruct p, s. destruct s0.
     simpl. subst...
    exists Unit.
    dependent destruction x...
   intros v [].
   exists (Var v)...
  Defined.

  Fixpoint measure (e: Term): nat :=
    match e with
    | Var v => 0%nat
    | Unit => 1%nat
    | Comp x y => S (2 * measure x + measure y)
    end.

  Context `{Monoid M}.

  Notation eval vs := (universal_algebra.eval msig (λ _, (vs: V → M))).

  Program Fixpoint internal_simplify (t: Term) {measure (measure t)}:
      { r: Term | ∀ v, eval v (curry (to_ua r)) = eval v (curry (to_ua t)) } :=
    match t with
    | Var _ => t
    | Unit => t
    | Comp Unit y => internal_simplify y
    | Comp x Unit => internal_simplify x
    | Comp ((Var _) as x) y => Comp x (internal_simplify y)
    | Comp (Comp x y) z => internal_simplify (Comp x (Comp y z))
    end.

  Solve Obligations with (program_simpl; simpl; try apply reflexivity; omega).

  Next Obligation.
   destruct internal_simplify.
   simpl.
   rewrite e.
   transitivity (mon_unit & universal_algebra.eval msig (λ _, v) (curry (to_ua y))).
    symmetry.
    apply left_identity.
   reflexivity.
  Qed.

  Next Obligation.
   destruct internal_simplify.
   simpl.
   rewrite e.
   transitivity (universal_algebra.eval msig (λ _, v) (curry (to_ua x)) & mon_unit).
    symmetry.
    apply right_identity.
   reflexivity.
  Qed.

  Next Obligation. destruct internal_simplify. simpl. rewrite e. reflexivity. Qed.
  Next Obligation. destruct internal_simplify. simpl. rewrite e. simpl. apply associativity. Qed.

  Program Definition simplify (t: uaTerm): { r: uaTerm | ∀ v, eval v r = eval v t } :=
    curry (to_ua (internal_simplify (from_ua (decode0 t)))).

  Next Obligation.
   destruct @internal_simplify. simpl.
   destruct @from_ua in e. simpl in *.
   rewrite e.
   rewrite e0.
   rewrite @curry_decode0.
   reflexivity.
  Qed.

  (* This would be a nice theorem to prove:

  Require varieties.open_terms.

  Instance: Equiv V := eq.

  Goal ∀ (x y: uaTerm), open_terms.ee msig msig monoids.Laws (ne_list.one tt) x y →
   ` (simplify x) ≡ ` (simplify y).
  Proof.

  *)

End contents.
