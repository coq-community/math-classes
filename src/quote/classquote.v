Require Import Morphisms Program Unicode.Utf8.

(* First, two ways to do quoting in the naive scenario without
 holes/variables in the expression: *)

Module simple.

  (* An example term language and evaluation: *)

  Inductive Expr := Plus (a b: Expr) | Mult (a b: Expr) | Zero | One.

  Fixpoint eval (e: Expr): nat :=
    match e with
    | Plus a b => eval a + eval b
    | Mult a b => eval a * eval b
    | Zero => 0
    | One => 1
    end.

  (* First up is the simplest approach I can think of. *)

  Module approach_A.

    Class Quote (n: nat) := quote: Expr.

    Implicit Arguments quote [[Quote]].

    Section instances.

      Context n m `{Quote n} `{Quote m}.

      Global Instance: Quote 0 := Zero.
      Global Instance: Quote 1 := One.
      Global Instance: Quote (n + m) := Plus (quote n) (quote m).
      Global Instance: Quote (n * m) := Mult (quote n) (quote m).

    End instances.

    Ltac do_quote :=
      match goal with
      |- (?a = ?b) => change (eval (quote a) = eval (quote b))
      end.

    Lemma example: (1 + 0 + 1) * (1 + 1) = (1 + 1) + (1 + 1).
     do_quote.
    Admitted.

  End approach_A.

  (* This works, but there's something unsatisfying about this quotation, because
  the actual Quote instances are not validated until we get to the [change] tactic,
  which validates the quotation by requiring convertibility.

  Next, we show an alternative implementation where the Quote instances
  are all proved locally correct at their definition: *)

  Module approach_B.

    Class Quote (n: nat) := { quote: Expr; eval_quote: n = eval quote  }.

    Implicit Arguments quote [[Quote]].
    Implicit Arguments eval_quote [[Quote]].

    Section instances.

      Context n m `{Quote n} `{Quote m}.

      Global Program Instance: Quote 0 := { quote := Zero }.
      Global Program Instance: Quote 1 := { quote := One }.

      Global Instance: Quote (n + m) := { quote := Plus (quote n) (quote m) }.
      Proof. simpl. do 2 rewrite <- eval_quote. reflexivity. Qed.

      Global Instance: Quote (n * m) := { quote := Mult (quote n) (quote m) }.
      Proof. simpl. do 2 rewrite <- eval_quote. reflexivity. Qed.

    End instances.

    Lemma do_quote {n m} `{Quote n} `{Quote m}: eval (quote n) = eval (quote m) → n = m.
    Proof. intros. rewrite (eval_quote n), (eval_quote m). assumption. Qed.

    Lemma example: (1 + 0 + 1) * (1 + 1) = (1 + 1) + (1 + 1).
     apply do_quote.
    Admitted.

  End approach_B.

End simple.

(* So far so good, but the variable-less scenario isn't really interesting. We now rework approach B
 to include quotation of holes/variables, including recognition of syntactically identical ones. *)

Module with_vars.

(* Some random utilities: *)

Lemma sum_assoc {A B C}: (A+B)+C → A+(B+C). intuition. Defined.
Lemma bla {A B C}: (A+B) → A+(B+C). intuition. Defined.
Lemma monkey {A B}: False + A → A + B. intuition. Defined.


Section obvious.

  Class Obvious (T: Type) := obvious: T.

  Context (A B C: Type).

  Global Instance: Obvious (A → A) := id.
  Global Instance: Obvious (False → A) := False_rect _.
  Global Instance: Obvious (A → A + B) := inl.
  Global Instance: Obvious (A → B + A) := inr.
  Global Instance obvious_sum_src  `{Obvious (A → C)} `{Obvious (B → C)}: Obvious (A+B → C). repeat intro. intuition. Defined.
  Global Instance obvious_sum_dst_l `{Obvious (A → B)}: Obvious (A → B+C). repeat intro. intuition. Defined.
  Global Instance obvious_sum_dst_r `{Obvious (A → B)}: Obvious (A → C+B). repeat intro. intuition. Defined.

End obvious.

(* Again our example term language, this time without plus/one (they're boring), but with Var
 added: *)

Inductive Expr (V: Type) := Mult (a b: Expr V) | Zero | Var (v: V).

Implicit Arguments Var [[V]].
Implicit Arguments Zero [[V]].
Implicit Arguments Mult [[V]].

(*
Require Import monads canonical_names.

Instance: MonadReturn Expr := fun _ => Var.

Instance expr_bind: MonadBind Expr := fun A B =>
  fix F (m: Expr A) (f: A → Expr B): Expr B :=
    match m with
    | Zero => Zero
    | Mult x y => Mult (F x f) (F y f)
    | Var v => f v
    end.

Section eqs.

  Context `{e: Equiv A} `{Equivalence _ e}.

  Global Instance expr_eq: Equiv (Expr A) :=
    fix F (x y: Expr A) :=
      match x, y with
      | Var v, Var w => v = w
      | Mult v w, Mult p q => F v p ∧ F w q
      | Zero, Zero => True
      | _, _ => False
      end.

  Instance: Reflexive expr_eq.
  Proof. intro. induction x; simpl; intuition. Qed.

  Instance: Symmetric expr_eq.
  Proof. intro. induction x; destruct y; simpl in *; intuition. Qed.

  Instance: Transitive expr_eq.
  Admitted.

  Global Instance expr_equivalence: Equivalence expr_eq.

End eqs.

Instance: ∀ `{Equiv A}, Proper ((=) ==> (=)) (ret Expr).
 repeat intro.
 assumption.
Qed.

Instance bind_proper: ∀ `{Equiv A} `{Equiv B},
 Proper ((=) ==> pointwise_relation A (=) ==> (=)) (@expr_bind A B).
Proof.
 intros A H B H0 x y E.
(*
 induction x.
  destruct y; intuition.
  intros f g E'.
  simpl.
  red.
  simpl.
  split.
   red in E.
   simpl in E.

   apply IHx2.

  simpl in *.

 unfold expr_bind.

 simpl.
*)
Admitted.


Instance: Monad Expr.
  *)



(* The expression type is parameterized over the set of variable indices. Hence, we diverge
 from Claudio, who uses nat indices for variables, thereby introducing bounds problems and
 dummy variables and other nastiness. *)

(* An expression is only meaningful in the context of a variable assignment: *)

Definition Value := nat.
Definition Vars V := V → Value.

Fixpoint eval {V} (vs: Vars V) (e: Expr V): Value :=
  match e with
  | Zero => 0
  | Mult a b => eval vs a * eval vs b
  | Var v => vs v
  end.

Instance eval_proper V: Proper (pointwise_relation _ eq ==> eq ==> eq) (@eval V).
Proof.
 repeat intro. subst.
 induction y0; simpl.
   congruence.
  reflexivity.
 apply H.
Qed.

(* Some simple combinators for variable packs: *)

Definition novars: Vars False := False_rect _.
Definition singlevar (x: Value): Vars unit := fun _ => x.
Definition merge {A B} (a: Vars A) (b: Vars B): Vars (A+B) :=
  fun i => match i with inl j => a j | inr j => b j end.

(* These last two combinators are the "constructors" of an implicitly defined subset of
 Gallina terms (representing Claudio's "heaps") for which we implement syntactic
 lookup with type classes: *)

Section Lookup.

  (* Given a heap and value, Lookup instances give the value's index in the heap: *)

  Class Lookup {A} (x: Value) (f: Vars A) := { lookup: A; lookup_correct: f lookup = x }.

  Global Implicit Arguments lookup [[A] [Lookup]].

  Context (x: Value) {A B} (va: Vars A) (vb: Vars B).

  (* If the heap is a merge of two heaps and we can find the value's index in the left heap,
   we can access it by indexing the merged heap: *)

  Global Instance lookup_left `{!Lookup x va}: Lookup x (merge va vb)
    := { lookup := inl (lookup x va) }.
  Proof. apply lookup_correct. Defined.

  (* And vice-versa: *)

  Global Instance lookup_right `{!Lookup x vb}: Lookup x (merge va vb)
    := { lookup := inr (lookup x vb) }.
  Proof. apply lookup_correct. Defined.

  (* If the heap is just a singlevar, we can easily index it. *)

  Global Program Instance: Lookup x (singlevar x) := { lookup := tt }.

  (* Note that we don't have any fallback/default instances at this point. We /will/ introduce
  such an instance for our Quote class later on, which will add a new variable to the heap
  if another Quote instance that relies on Lookup into the "current" heap fails. *)

End Lookup.

(* One useful operation we need before we get to Quote relates to variables and expression
 evaluation. As its name suggests, map_var maps an expression's variable indices. *)

Definition map_var {V W: Type} (f: V → W): Expr V → Expr W :=
  fix F (e: Expr V): Expr W :=
    match e with
    | Mult a b => Mult (F a) (F b)
    | Zero => Zero
    | Var v => Var (f v)
    end.

(* An obvious identity is: *)

Lemma eval_map_var {V W} (f: V → W) v e:
  eval v (map_var f e) = eval (v ∘ f) e.
Proof.
 induction e; simpl; try reflexivity.
 rewrite IHe1, IHe2.
 reflexivity.
Qed.

(* Finally, Quote itself: *)

Section Quote.

  (* In Quote, the idea is that V, l, and n are all "input" variables, while V' and r are "output"
  variables (in the sense that we will rely on unification to generate them. V and l represent
  the "current heap", n represents the value we want to quote, and V' and r' represent the
  heap of newly encountered variables during the quotation.
    This explains the type of quote: it is an expression that refers either to variables from
  the old heap, or to newly encountered variables.
    eval_quote is the usual correctness property, which now merges the two heaps. *)

  Class Quote {V} (l: Vars V) (n: Value) {V'} (r: Vars V') :=
    { quote: Expr (V + V')
    ; eval_quote: @eval (V+V') (merge l r) quote = n }.

  Implicit Arguments quote [[V] [l] [V'] [r] [Quote]].

  (* Our first instance for Zero is easy. The "novars" in the result type reflects the fact that no new
   variables are encountered. The correctness proof is easy enough for Program. *)

  Global Program Instance quote_zero V (v: Vars V): Quote v 0 novars := { quote := Zero }.

  (* The instance for multiplication is a bit more complex. The first line is just boring
   variable declarations. The second line is important. "Quote x y z" must be read as
   "quoting y with existing heap x generates new heap z", so the second line
   basically just shuffles heaps around.
     The third line has some ugly map_var's in it because the heap shuffling must be reflected
   in the variable indices, but apart from that it's just constructing a Mult
   term with quoted subterms. *)

  Global Program Instance quote_mult V (v: Vars V) n V' (v': Vars V') m V'' (v'': Vars V'')
    `{!Quote v n v'} `{!Quote (merge v v') m v''}: Quote v (n * m) (merge v' v'') :=
      { quote := Mult (map_var bla (quote n)) (map_var sum_assoc (quote m)) }.

  Next Obligation. Proof with auto.
   destruct Quote0, Quote1.
   subst. simpl.
   do 2 rewrite eval_map_var.
   f_equal; apply eval_proper; auto; intro; intuition.
  Qed.

  (* Now follows the instance where we recognize values that are already in the heap. This
   is expressed by the Lookup requirement, which will only be fulfilled if the Lookup instances
   defined above can find the value in the heap. The novars in the [Quote v x novars] result
   reflects that this quotation does not generate new variables. *)

  Global Program Instance quote_old_var V (v: Vars V) x {i: Lookup x v}:
    Quote v x novars | 8 := { quote := Var (inl (lookup x v)) }.
  Next Obligation. Proof. apply lookup_correct. Qed.

  (* Finally, the instance for new variables. We give this lower priority so that it is only
   used if Lookup fails. *)

  Global Program Instance quote_new_var V (v: Vars V) x: Quote v x (singlevar x) | 9
    := { quote := Var (inr tt) }.

End Quote.

(* Note: Explicitly using dynamically configured variable index sets instead of plain lists
 not only removes the need for an awkward dummy value to cope with out-of-bounds
 accesses, but also means that we can prove the correctness class fields in
 Lookup/Quote without having to take the potential for out-of-bounds indexing into
 account (which would be a nightmare). *)

(* When quoting something from scratch we will want to start with an empty heap.
 To avoid having to mention this, we define quote' and eval_quote': *)

Definition quote': ∀ x {V'} {v: Vars V'} {d: Quote novars x v}, Expr _ := @quote _ _.

Definition eval_quote': ∀ x {V'} {v: Vars V'} {d: Quote novars x v},
  eval (merge novars v) quote = x
    := @eval_quote _ _ .

Implicit Arguments quote' [[V'] [v] [d]].
Implicit Arguments eval_quote' [[V'] [v] [d]].

(* Time for some tests! *)

Goal ∀ x y (P: Value → Prop), P ((x * y) * (x * 0)).
  intros.
  rewrite <- (eval_quote' _).
    (* turns the goal into
         P (eval some_variable_pack_composed_from_combinators quote)
    *)
  simpl quote.
Admitted.

(* We can also inspect quotations more directly: *)

Section inspect.
  Variables x y: Value.
  Eval compute in quote' ((x * y) * (x * 0)).
    (* = Mult (Mult (Var (inr (inl (inl ())))) (Var (inr (inl (inr ())))))
           (Mult (Var (inr (inl (inl ())))) Zero)
       : Expr (False + (() + () + (False + False))) *)

  (* The second occurrence of (Var (inr (inl (inl ())))) means
   the quoting has successfully noticed that it's the same
   expression. *)

  (* The two units in the generated variable index type reflect the
   fact that the expression contains two variables. *)

  (* I think adding some additional Quote instances might let us
   get rid of the False's, but at the moment I see little reason to. *)

End inspect.

(* If we want to quote an equation between two expressions we should make
 sure that the both sides refer to the same variable pack, and for that we write a
 little utility function. It does the same kind of shuffling that the mult
 Quote instance did. *)

Lemma quote_equality {V} {v: Vars V} {V'} {v': Vars V'} (l r: Value) `{!Quote novars l v} `{!Quote v r v'}:
  let heap := (merge v v') in
  eval heap (map_var monkey quote) = eval heap quote → l = r.
Proof with intuition.
 destruct Quote0 as [lq []].
 destruct Quote1 as [rq []].
 intros heap H.
 subst heap. simpl in H.
 rewrite <- H, eval_map_var.
 apply eval_proper... intro...
Qed.

Goal ∀ x y, x * y = y * x.
 intros.
 apply (quote_equality _ _).
 simpl quote.
 unfold map_var, monkey, sum_rect.
Admitted.

End with_vars.
