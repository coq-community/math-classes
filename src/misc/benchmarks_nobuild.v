Require Import 
  abstract_algebra interfaces.integers interfaces.additional_operations fast_integers.

Section wolfram_sqrt.
Context `{Integers Z} `{!RingOrder oZ} `{!TotalOrder oZ}
  `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)} `{!ShiftLSpec Z (Z⁺) sl}.

Fixpoint root_loop (x : Z) (n : nat) : Z * Z :=
  match n with
  | O => (x, 0)
  | S n => let (r, s) := root_loop x n in
     if decide_rel (≤) (s + 1) r
     then ((r - (s + 1)) ≪ 2, (s + 2) ≪ 1)
     else (r ≪ 2, s ≪ 1)
  end.
End wolfram_sqrt.

Definition fast_root_loop := root_loop (Z:=fastZ).

Let n : nat := Eval vm_compute in (10 * 10 * 10 * 10)%nat.

Time Eval vm_compute in (snd (fast_root_loop 2 n)).
(* 7.432465s *)

Require Import BigZ.
Open Scope bigZ_scope.

Fixpoint root_loop_alt (x : bigZ) (n : nat) : bigZ * bigZ :=
  match n with
  | O => (x, 0)
  | S n => let (r, s) := root_loop_alt x n in
     match BigZ.compare (s + 1) r with
     | Gt => (BigZ.shiftl r 2, BigZ.shiftl s 1)
     | _ => (BigZ.shiftl (r - (s + 1)) 2, BigZ.shiftl (s + 2) 1)
     end
  end.

Time Eval vm_compute in (snd (root_loop_alt 2 n)).
(* 7.264454s *)

