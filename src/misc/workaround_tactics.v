Global Ltac posed_rewrite t := pose proof t as TEMP; rewrite TEMP; clear TEMP.
  (* Workaround around Coq bug, probably same as #2185. *)
Global Ltac apply_simplified x := generalize x; simpl; intro HHH; apply HHH; clear HHH.
Tactic Notation "posed_rewrite" "<-" constr(t) := pose proof t as TEMP; rewrite <-TEMP; clear TEMP.
