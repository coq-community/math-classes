Require Import 
  abstract_algebra interfaces.integers interfaces.additional_operations
  implementations.dyadics fast_integers.

Section wolfram_sqrt.
Context `{Integers Z} `{!RingOrder oZ} `{!TotalOrder oZ}
  `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)} 
  `{!NatPowSpec Z (Z⁺) pw}  `{!ShiftLSpec Z (Z⁺) sl}.

Fixpoint root_loop (x : Dyadic Z) (n : nat) : Dyadic Z * Dyadic Z :=
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

Time Eval vm_compute in (
  (fun _ _ _ _ _ _ _ _ _ _ => true)
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))
  (snd (fast_root_loop 2 n))).

Require Import BigZ.
Open Scope bigZ_scope.

Notation bigD := (Dyadic bigZ).

Definition BigD_0 : bigD := (0 $ 0).
Definition BigD_1 : bigD := (1 $ 0).
Definition BigD_2 : bigD := (2 $ 0).

Definition BigD_plus (x y : bigD) : bigD := 
  match BigZ.compare (expo x) (expo y) with
  | Gt => BigZ.shiftl (mant x) (expo x - expo y) + mant y $ BigZ.min (expo x) (expo y)
  | _ => mant x + BigZ.shiftl (mant y) (expo y - expo x) $ BigZ.min (expo x) (expo y)
  end.

Definition BigD_opp (x : bigD) : bigD := -mant x $ expo x.

Definition BigD_mult (x y : bigD) : bigD := mant x * mant y $ expo x + expo y.

Definition BigD_shiftl (x : bigD) (n : bigZ) : bigD := mant x $ expo x + n.

Definition BigD_compare (x y : bigD) : comparison := 
  match BigZ.compare (expo x) (expo y) with
  | Gt => BigZ.compare (BigZ.shiftl (mant x) (expo x - expo y)) (mant y)
  | _ => BigZ.compare (mant x) (BigZ.shiftl (mant y) (expo y - expo x))
  end.

Fixpoint root_loop_alt (x : bigD) (n : nat) : bigD * bigD :=
  match n with
  | O => (x, BigD_0)
  | S n => let (r, s) := root_loop_alt x n in
     match BigD_compare (BigD_plus s BigD_1) r with
     | Gt => (BigD_shiftl r 2, BigD_shiftl s 1)
     | _ => (BigD_shiftl (BigD_plus r (BigD_opp (BigD_plus s BigD_1))) 2, BigD_shiftl (BigD_plus s BigD_2) 1)
     end
  end.

Time Eval vm_compute in (mant (snd (root_loop_alt BigD_2 n))).

Time Eval vm_compute in (
  (fun _ _ _ _ _ _ _ _ _ _ => true)
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))).

Definition BigD_4 : bigD := (4 $ 0).

Fixpoint root_loop_alt_mult (x : bigD) (n : nat) : bigD * bigD :=
  match n with
  | O => (x, BigD_0)
  | S n => let (r, s) := root_loop_alt_mult x n in
     match BigD_compare (BigD_plus s BigD_1) r with
     | Gt => (BigD_mult BigD_4 r, BigD_mult BigD_2 s)
     | _ => (BigD_mult BigD_4 (BigD_plus r (BigD_opp (BigD_plus s BigD_1))), BigD_mult BigD_2 (BigD_plus s BigD_2))
     end
  end.

Time Eval vm_compute in (mant (snd (root_loop_alt_mult BigD_2 n))).

Time Eval vm_compute in (
  (fun _ _ _ _ _ _ _ _ _ _ => true)
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))).
