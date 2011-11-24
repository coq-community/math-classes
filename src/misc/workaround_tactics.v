Global Ltac posed_rewrite t := let TEMP:=fresh in pose proof t as TEMP; simpl TEMP; rewrite TEMP; clear TEMP.
  (* Workaround around Coq bug, probably same as #2185. *)
Global Ltac apply_simplified x := let TEMP:=fresh in generalize x; simpl; intro TEMP; apply TEMP; clear TEMP.
Tactic Notation "posed_rewrite" "<-" constr(t) := let TEMP:= fresh in pose proof t as TEMP; simpl TEMP; rewrite <-TEMP; clear TEMP.
