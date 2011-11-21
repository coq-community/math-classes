Require Import
  canonical_names universal_algebra Program.

Section packed.
  Context (σ: Signature) {V: Type}.

  Inductive Applied: sorts σ → Type :=
    | AppliedOp o: Arguments (σ o) → Applied (result _ (σ o))
    | AppliedVar: V → ∀ s, Applied s
  with Arguments: OpType (sorts σ) → Type :=
    | NoMoreArguments s: Arguments (ne_list.one s)
    | MoreArguments o' o: Applied o' → Arguments o → Arguments (ne_list.cons o' o).

  Definition head_arg x y (a: Arguments (ne_list.cons x y)): Applied x :=
    match a with
    | MoreArguments k l m n => m
    | NoMoreArguments _ => False
    end.

  Definition tail_args x y (a: Arguments (ne_list.cons x y)): Arguments y :=
    match a with
    | MoreArguments k l m n => n
    | NoMoreArguments _ => False
    end.

  Context (P: ∀ {s}, Applied s → Type).
  Implicit Arguments P [[s]].

  Section forallArgs.

    Fixpoint forallArgs {o} (a: Arguments o): Type :=
      match a with
      | NoMoreArguments _ => True
      | MoreArguments _ _ z v => prod (P z) (forallArgs v)
      end.

    Definition PofSplit {o}: Arguments o → Type :=
      match o with
      | ne_list.one _ => λ _, unit
      | ne_list.cons x y => λ a, prod (P (head_arg x y a)) (forallArgs (tail_args _ _ a))
      end.

    Definition forallSplit `(a: Arguments (ne_list.cons y z)):
      forallArgs a → prod (P (head_arg y z a)) (forallArgs (tail_args _ _ a)).
    Proof.
     intro.
     change (PofSplit a).
     destruct a; simpl.
      exact tt.
     assumption.
    Defined. (* todo: write as term *)

  End forallArgs.

  Context
    (Pop: ∀ o x, forallArgs x → P (AppliedOp o x))
    (Pvar: ∀ v s, P (AppliedVar v s)).

  Fixpoint better_Applied_rect {o} (a: Applied o): P a :=
    match a with
    | AppliedOp x y => Pop x y (better_args y)
    | AppliedVar x v => Pvar x v
    end
  with better_args {o} (a: Arguments o): forallArgs a :=
    match a with
    | NoMoreArguments _ => I
    | MoreArguments _ _ x y => (better_Applied_rect x, better_args y)
    end.

End packed.

(* Conversion /from/ packed representation: *)

Fixpoint curry {σ} {V} {o} (a: Applied σ o): Term σ V (ne_list.one o) :=
  match a in (Applied _ s) (*return (Term σ V (ne_list.one s))*) with
  | AppliedOp op y => apply_args y (app_tree σ (Op σ V op))
  | AppliedVar v x => Var σ V v x
  end
with apply_args {σ} {V} {o} (a: @Arguments σ V o): op_type (Term0 σ V) o → Term0 σ V (result _ o) :=
  match a with
  | NoMoreArguments y => id
  | MoreArguments x y u q => λ z, apply_args q (z (curry u))
  end.

(* Conversion /to/ packed representation: *)

Fixpoint decode `(t: Term σ V o): Arguments σ o → Applied σ (result _ o) :=
  match t with
  | Var x y => λ z, AppliedVar σ x y
  | Op x => AppliedOp σ x
  | App x y z w => λ p, decode z (MoreArguments σ y x (decode w (NoMoreArguments σ _)) p)
  end.

(* Back and forth: *)

Definition curry_decode `(t: Term σ V o) (a: Arguments σ o):
  curry (decode t a) ≡ apply_args a (app_tree σ t).
Proof with simpl in *; try reflexivity.
 induction t...
  dependent destruction a... (* DANGER: uses JMeq_eq *)
 rewrite IHt1...
 rewrite IHt2...
Qed.

(* Nullary specializations: *)

Definition decode0 `(t: Term0 σ V s): Applied σ s := decode t (NoMoreArguments σ _).

Definition curry_decode0 `(t: Term0 σ V o): curry (decode0 t) ≡ t.
Proof. apply (curry_decode t). Qed.
