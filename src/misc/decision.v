Require Import
  canonical_names util.

Class Decision P := decide: sumbool P (¬P).
Implicit Arguments decide [[Decision]].

Instance: ∀ P, Decision P → Stable P.
Proof. firstorder. Qed.

Ltac solve_trivial_decision :=
  match goal with
  | [ |- Decision (?P) ] => apply _
  | [ |- sumbool ?P (¬?P) ] => change (Decision P); apply _
  end.

Ltac solve_decision :=
  first [solve_trivial_decision | unfold Decision; decide equality; solve_trivial_decision].

(* We cannot state this as Proper (iff ==> iffT) Decision due to the lack of setoid rewriting in Type *)
Program Instance decision_proper (P Q : Prop) (PiffQ : P ↔ Q) (P_dec : Decision P) : Decision Q :=
  match P_dec with
  | left _ => left _
  | right _ => right _
  end.
Solve Obligations using (program_simpl; tauto).

Definition bool_decide (P : Prop) `{dec : !Decision P} : bool := if dec then true else false.

Lemma bool_decide_true `{dec : Decision P} : bool_decide P ≡ true ↔ P.
Proof. unfold bool_decide. split; intro; destruct dec; firstorder. Qed.

Lemma bool_decide_false `{dec : !Decision P} : bool_decide P ≡ false ↔ ¬P.
Proof. unfold bool_decide. split; intro; destruct dec; firstorder. Qed.

(*
  Because [vm_compute] evaluates terms in [Prop] eagerly and does not remove dead code we
  need the decide_rel hack. Suppose we have [(x = y) =def  (f x = f y)], now:
     bool_decide (x = y) → bool_decide (f x = f y) → ...
  As we see, the dead code [f x] and [f y] is actually evaluated, which is of course an utter waste.
  Therefore we introduce decide_rel and bool_decide_rel.
     bool_decide_rel (=) x y → bool_decide_rel (λ a b, f a = f b) x y → ...
  Now the definition of equality remains under a lambda and our problem does not occur anymore!
*)

Definition decide_rel `(R : A → B → Prop) {dec : ∀ x y, Decision (R x y)} (x : A) (y : B) : Decision (R x y)
  := dec x y.

Definition bool_decide_rel `(R : relation A) {dec : ∀ x y, Decision (R x y)} : A → A → bool
  := λ x y, if dec x y then true else false.

Lemma bool_decide_rel_true `(R : relation A) {dec : ∀ x y, Decision (R x y)} :
  ∀ x y, bool_decide_rel R x y ≡ true ↔ R x y.
Proof. unfold bool_decide_rel. split; intro; destruct dec; firstorder. Qed.

Lemma bool_decide_rel_false `(R : relation A)`{dec : ∀ x y, Decision (R x y)} :
  ∀ x y, bool_decide_rel R x y ≡ false ↔ ¬R x y.
Proof. unfold bool_decide_rel. split; intro; destruct dec; firstorder. Qed.

Program Definition decision_from_bool_decide {P b} (prf : b ≡ true ↔ P) :
  Decision P := match b with true => left _ | false => right _ end.
Next Obligation. now apply prf. Qed.
Next Obligation. rewrite <-prf. discriminate. Qed.

Program Instance prod_eq_dec `(A_dec : ∀ x y : A, Decision (x ≡ y))
     `(B_dec : ∀ x y : B, Decision (x ≡ y)) : ∀ x y : A * B, Decision (x ≡ y) := λ x y,
  match A_dec (fst x) (fst y) with
  | left _ => match B_dec (snd x) (snd y) with left _ => left _ | right _ => right _ end
  | right _ => right _
  end.
Solve Obligations using (program_simpl; f_equal; firstorder).

Program Instance and_dec `(P_dec : Decision P) `(Q_dec : Decision Q) : Decision (P ∧ Q) :=
  match P_dec with
  | left _ => match Q_dec with left _ => left _ | right _ => right _ end
  | right _ => right _
  end.
Solve Obligations using (program_simpl; tauto).

Program Instance or_dec `(P_dec : Decision P) `(Q_dec : Decision Q) : Decision (P ∨ Q) :=
  match P_dec with
  | left _ => left _
  | right _ => match Q_dec with left _ => left _ | right _ => right _ end
  end.
Solve Obligations using (program_simpl; firstorder).

Program Instance is_Some_dec `(x : option A) : Decision (is_Some x) :=
  match x with
  | None => right _
  | Some _ => left _
  end.

Program Instance is_None_dec `(x : option A) : Decision (is_None x) :=
  match x with
  | None => left _
  | Some _ => right _
  end.

Program Instance option_eq_dec `(A_dec : ∀ x y : A, Decision (x ≡ y))
     : ∀ x y : option A, Decision (x ≡ y) := λ x y,
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

Program Instance True_dec: Decision True := left _.
Program Instance False_dec: Decision False := right _.
