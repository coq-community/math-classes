Require Import Coq.Setoids.Setoid MathClasses.interfaces.canonical_names.

(*
When math-classes is used as part of another development setoid_replace
often uses an incorrect equality due to low cost instances of DefaultRelation.
We provide mc_setoid_replace to ensure that (=) is used.
*)
Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y) :=
  setoidreplace ((=) x y) idtac.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "at" int_or_var_list(o) :=
  setoidreplaceat ((=) x y) idtac o.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id) :=
  setoidreplacein ((=) x y) id idtac.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id)
  "at" int_or_var_list(o) :=
  setoidreplaceinat ((=) x y) id idtac o.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "by" tactic3(t) :=
  setoidreplace ((=) x y) ltac:t.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "at" int_or_var_list(o)
  "by" tactic3(t) :=
  setoidreplaceat ((=) x y) ltac:t o.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id)
  "by" tactic3(t) :=
  setoidreplacein ((=) x y) id ltac:t.

Tactic Notation "mc_setoid_replace" constr(x) "with" constr(y)
  "in" hyp(id)
  "at" int_or_var_list(o)
  "by" tactic3(t) :=
  setoidreplaceinat ((=) x y) id ltac:t o.

Ltac setoid_subst :=
  repeat (match goal with
  | E : ?x = ?e |- _ => is_var x; lazymatch e with context [x] => fail | _ => rewrite ?E in *; clear x E end
  | E : ?e = ?x |- _ => is_var x; lazymatch e with context [x] => fail | _ => rewrite <-?E in *; clear x E end
  | E : ?x ≡ ?e |- _ => is_var x; lazymatch e with context [x] => fail | _ => rewrite ?E in *; clear x E end
  | E : ?e ≡ ?x |- _ => is_var x; lazymatch e with context [x] => fail | _ => rewrite <-?E in *; clear x E end
  end).

Ltac setoid_discriminate :=
  repeat intro; exfalso;
  match goal with
  | E : _ = _ |- _ => solve [inversion E]
  | E : _ ≡ _ |- _ => discriminate E
  end.
