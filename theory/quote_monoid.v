Require Import MathClasses.interfaces.abstract_algebra.
Require MathClasses.interfaces.universal_algebra.

Module ua := universal_algebra.

Require MathClasses.varieties.monoids.
Require MathClasses.theory.monoid_normalization.

Notation msig := varieties.monoids.sig.
Notation Op := (ua.Op msig False).
Notation App := (ua.App msig False _ _).
Notation Term V := (ua.Term0 msig V tt).

Section contents.
  Context `{Monoid M}.

  Definition Vars V := V → M.

  Definition novars: Vars False := False_rect _.
  Definition singlevar (x: M): Vars unit := fun _ => x.
  Definition merge {A B} (a: Vars A) (b: Vars B): Vars (A+B) :=
    fun i => match i with inl j => a j | inr j => b j end.

  Section Lookup.
    Class Lookup {A} (x: M) (f: Vars A) := { lookup: A; lookup_correct: f lookup ≡ x }.

    Global Arguments lookup {A} _ _ {Lookup}.

    Context (x: M) {A B} (va: Vars A) (vb: Vars B).

    Global Instance lookup_left `{!Lookup x va}: Lookup x (merge va vb)
      := { lookup := inl (lookup x va) }.
    Proof. apply lookup_correct. Defined.

    Global Instance lookup_right `{!Lookup x vb}: Lookup x (merge va vb)
      := { lookup := inr (lookup x vb) }.
    Proof. apply lookup_correct. Defined.

    Global Program Instance: Lookup x (singlevar x) := { lookup := tt }.
  End Lookup.

  Instance: MonUnit (Term V) := λ V, ua.Op msig _ monoids.one.
  Instance: SgOp (Term V) :=
    λ V x, ua.App msig _ _ _ (ua.App msig _ _ _ (ua.Op msig _ monoids.mult) x).

  Notation eval V vs := (ua.eval _ (λ _, (vs: Vars V))).

  Section Quote.
    Class Quote {V} (l: Vars V) (n: M) {V'} (r: Vars V') :=
      { quote: Term (V + V')
      ; eval_quote: @eval (V+V') (merge l r) quote ≡ n }.

    Arguments quote {V l} _ {V' r Quote}.

    Global Program Instance quote_zero V (v: Vars V): Quote v mon_unit novars := { quote := mon_unit }.

    Global Program Instance quote_mult V (v: Vars V) n V' (v': Vars V') m V'' (v'': Vars V'')
      `{!Quote v n v'} `{!Quote (merge v v') m v''}: Quote v (n & m) (merge v' v'') :=
        { quote := ua.map_var msig (obvious: (V+V')→(V+(V'+V''))) (quote n) & ua.map_var msig (obvious:((V+V')+V'')→(V+(V'+V''))) (quote m) }.

    Next Obligation. Proof with auto.
     destruct Quote0, Quote1.
     subst. simpl.
     simpl.
     do 2 rewrite ua.eval_map_var.
     unfold ua_basic.algebra_op.
     simpl.
     f_equal; apply ua.eval_strong_proper; auto; repeat intro; intuition.
    Qed.

    Global Program Instance quote_old_var V (v: Vars V) x {i: Lookup x v}:
      Quote v x novars | 8 := { quote := ua.Var msig _ (inl (lookup x v)) tt }.
    Next Obligation. Proof. apply lookup_correct. Qed.

    Global Program Instance quote_new_var V (v: Vars V) x: Quote v x (singlevar x) | 9
      := { quote := ua.Var msig _ (inr tt) tt }.
  End Quote.

  Definition quote': ∀ x {V'} {v: Vars V'} {d: Quote novars x v}, Term _ := @quote _ _.

  Definition eval_quote': ∀ x {V'} {v: Vars V'} {d: Quote novars x v},
    eval _ (merge novars v) quote ≡ x
      := @eval_quote _ _.

  Arguments quote' _ {V' v d}.
  Arguments eval_quote' _ {V' v d}.

  Lemma quote_equality `{v: Vars V} `{v': Vars V'} (l r: M) `{!Quote novars l v} `{!Quote v r v'}:
    let heap := (merge v v') in
    eval _ heap (ua.map_var msig (obvious: False + V → V + V') quote) = eval _ heap quote → l = r.
  Proof with intuition.
   intros heap.
   destruct Quote0, Quote1.
   subst. subst heap. simpl.
   intro.
   rewrite <- H0.
   rewrite ua.eval_map_var.
   cut (eval _ (merge novars v) quote0 ≡ ua.eval msig (λ _, merge v v' ∘ obvious) quote0).
    intro E. simpl in *. rewrite E. reflexivity.
   apply (@ua.eval_strong_proper msig (λ _, M) _ _ (ne_list.one tt))...
   repeat intro...
  Qed.

  Lemma equal_by_normal `{v: Vars V} `{v': Vars V'} (l r: M) `{!Quote novars l v} `{!Quote v r v'}:
   ` (monoid_normalization.simplify _ (ua.map_var msig (obvious: False + V → V + V') quote)) ≡
   ` (monoid_normalization.simplify _ quote) → l = r.
  Proof with intuition.
   do 2 destruct monoid_normalization.simplify.
   simpl. intros. subst.
   apply (quote_equality l r) .
   rewrite <- e, <- e0...
  Qed.

  Ltac monoid := apply (equal_by_normal _ _); vm_compute; reflexivity.

  Example ex x y z: x & (y & z) & mon_unit = mon_unit & (x & y) & z.
  Proof. monoid. Qed.
End contents.
