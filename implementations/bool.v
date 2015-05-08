Require Import MathClasses.interfaces.abstract_algebra.

Instance bool_eq: Equiv bool := eq.
Instance bool_bottom: Bottom bool := false.
Instance bool_top: Top bool := true.
Instance bool_join: Join bool := orb.
Instance bool_meet: Meet bool := andb.

Instance: BoundedJoinSemiLattice bool.
Proof.
  repeat (split; try apply _); repeat intro.
     apply Bool.orb_assoc.
    apply Bool.orb_false_r.
   apply Bool.orb_comm.
  apply Bool.orb_diag.
Qed.

Instance: MeetSemiLattice bool.
Proof.
  repeat (split; try apply _); repeat intro.
    apply Bool.andb_assoc.
   apply Bool.andb_comm.
  apply Bool.andb_diag.
Qed.

Instance: DistributiveLattice bool.
Proof.
  repeat (split; try apply _); repeat intro.
    apply Bool.absoption_orb.
   apply Bool.absoption_andb.
  apply Bool.orb_andb_distrib_r.
Qed.

(* We don't have a boolean algebra class yet *)