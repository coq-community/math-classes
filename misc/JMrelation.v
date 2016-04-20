(* JMeq without the [eq] hard-wiring. Meant for use with [Require] only, not [Import]. *)
Require Import Relation_Definitions Setoid.
Require Export Unicode.Utf8 Utf8_core.

Inductive R {A: Type} (r: relation A) (x: A): forall B: Type, relation B → B → Prop := relate y: r x y → R r x A r y.

Lemma reflexive A (x:A) (Ra: relation A) `{!Reflexive Ra}: R Ra x _ Ra x.
Proof. apply relate. reflexivity. Qed.

Lemma symmetric A B (x:A) (Ra: relation A) (Rb: relation B) (y:B) `{!Symmetric Ra}: R Ra x _ Rb y → R Rb y _ Ra x.
Proof. destruct 1. apply relate. symmetry. assumption. Qed.

Lemma transitive A B C (Ra: relation A) (Rb: relation B) (Rc: relation C) (a:A) (b:B) (c:C) `{!Transitive Ra}:
  R Ra a _ Rb b → R Rb b _ Rc c → R Ra a _ Rc c.
Proof. destruct 1. destruct 1. apply relate. transitivity y; assumption. Qed.

Require Import Coq.Logic.Eqdep.

Lemma unJM A (r: relation A) (x y:A) r' (E: R r x A r' y): r x y.
Proof.
 simple inversion E.
 rewrite (eq_rect_eq__eq_dep_eq _ (eq_rect_eq _) _ _ _ _ (eq_sigT_eq_dep _ _ _ _ _ _ H2)).
 firstorder.
Qed. (* Warning: Depends on proof_irrelevance. *)
