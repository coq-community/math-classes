Ltac rewrite_with t := let n := fresh in set (n := t); rewrite n; clear n.
Ltac rewrite_rev_with t := let n := fresh in set (n := t); rewrite <- n; clear n.
  (* this is a workaround for coq bug 2185 *)
