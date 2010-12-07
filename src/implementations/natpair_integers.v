(* The standard library's implementation of the integers (BinInt) uses nasty binary positive
  crap with various horrible horrible bit fiddling operations on it (especially Pminus).
  The following is a much simpler implementation whose correctness can be shown much
  more easily. In particular, it lets us use initiality of the natural numbers to prove initiality
  of these integers. *)

Set Automatic Introduction.

Require
 theory.naturals.
Require Import
 Morphisms Ring Program
 abstract_algebra theory.categories theory.rings 
 interfaces.naturals interfaces.integers orders.naturals.

Section contents.

Context N `{Naturals N}.

Context (* Extra parameterization for efficiency: *)
 `{∀ x y: N, Decision (x = y)}
 `{∀ x y: N, Decision (x ≤ y)}
 `{!NatDistance N}.

Add Ring N: (stdlib_semiring_theory N).

Inductive Z: Type := C { pos: N; neg: N }.

(* relations/operations/constants: *)

Global Instance z_equiv: Equiv Z := λ x y, pos x + neg y = pos y + neg x.
Global Instance z_plus: RingPlus Z := λ x y: Z, C (pos x + pos y) (neg x + neg y).
Global Instance z_inv: GroupInv Z := λ x: Z, C (neg x) (pos x).
Global Instance z_zero: RingZero Z := C 0 0.
Global Instance z_mult: RingMult Z := λ x y, C (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y).
Global Instance z_ring_one: RingOne Z := C 1 0.
Global Instance z_one: MonoidUnit Z := z_ring_one.

(* z_equiv is nice: *)

Instance: Reflexive z_equiv. Proof. repeat intro. unfold z_equiv. reflexivity. Qed.
Instance: Symmetric z_equiv. Proof. repeat intro. unfold z_equiv. symmetry. assumption. Qed.
Instance: Transitive z_equiv.
Proof.
 unfold z_equiv. intros x y z E E'.
 rewrite commutativity.
 rewrite (commutativity (pos z)).
 apply (left_cancellation (+) (pos y)); trivial.
 do 2 rewrite associativity.
 rewrite <- E, E'. ring.
Qed.

Instance: Equivalence z_equiv.
Instance: Setoid Z.

(* plus is nice: *)

Ltac ring_on_nat := repeat intro; unfold z_plus, equiv, z_equiv; simpl; ring.

Instance: Associative z_plus. Proof. repeat intro. ring_on_nat. Qed.
Instance: Commutative z_plus. Proof. repeat intro. ring_on_nat. Qed.

Instance: Proper (z_equiv ==> z_equiv ==> z_equiv) z_plus.
Proof.
 unfold z_equiv. intros x y E x0 y0 E'. simpl.
 transitivity (pos x + neg y + (pos x0 + neg y0)); [ring|].
 rewrite E, E'. ring.
Qed.

Let z_plus_0_l: LeftIdentity ring_plus (0:Z). Proof. intro. ring_on_nat. Qed.
Let z_plus_0_r: RightIdentity ring_plus (0:Z). Proof. intro. ring_on_nat. Qed.
Let z_plus_opp_l (x: Z): -x + x = 0. Proof. ring_on_nat. Qed.
Let z_plus_opp_r (x: Z): x + -x = 0. Proof. ring_on_nat. Qed.

Global Instance: SemiGroup Z (op:=z_plus).
Global Instance: Monoid Z (op:=z_plus) (unit:=z_zero).

(* inv is nice: *)

Instance: Proper (z_equiv ==> z_equiv) z_inv.
Proof. unfold z_equiv, z_inv. intros x y E. simpl. rewrite commutativity, <- E. ring. Qed.

Global Instance: @Group Z _ (z_plus) (z_zero) _ := { ginv_l := z_plus_opp_l; ginv_r := z_plus_opp_r }.
Global Instance: AbGroup Z (op:=z_plus) (unit:=z_zero).

(* mult is nice: *)

Instance: Associative z_mult. Proof. ring_on_nat. Qed.
Instance: Commutative z_mult. Proof. ring_on_nat. Qed.

Global Instance: Distribute z_mult z_plus. Proof. constructor; ring_on_nat. Qed.

Let z_mult_equiv_compat_r y y': y = y' → ∀ x, z_mult x y = z_mult x y'.
Proof.
 unfold z_mult, equiv, z_equiv. intros E x. simpl.
 transitivity (pos x * (pos y + neg y') + neg x * (pos y' + neg y)); [ring |].
 transitivity (pos x * (pos y' + neg y) + neg x * (pos y + neg y')); [| ring].
 rewrite E. reflexivity.
Qed.

Instance: Proper (z_equiv ==> z_equiv ==> z_equiv) z_mult.
Proof with auto.
 repeat intro. transitivity (z_mult x y0).
 apply z_mult_equiv_compat_r...
 rewrite commutativity.
 rewrite (commutativity y).
 apply z_mult_equiv_compat_r...
Qed.

Let mult_1_l: LeftIdentity ring_mult (1:Z). Proof. intro. ring_on_nat. Qed.
Let mult_1_r: RightIdentity ring_mult (1:Z). Proof. intro. ring_on_nat. Qed.

Instance: SemiGroup _ (op:=z_mult).
Instance: Monoid Z (op:=z_mult) (unit:=z_one).
Instance: CommutativeMonoid Z (op:=z_mult) (unit:=z_one).
Global Instance: Ring Z.

Add Ring Z: (stdlib_ring_theory Z).

(* misc: *)

Definition NtoZ (n: N): Z := C n 0.

Instance: Proper (equiv ==> equiv) NtoZ.
Proof. intros x y E. unfold NtoZ, equiv, z_equiv. simpl. rewrite E. reflexivity. Qed.

Global Instance: SemiRing_Morphism NtoZ.
Proof.
 unfold NtoZ.
 repeat (constructor; try apply _; try reflexivity); unfold equiv, z_equiv; simpl; intros.
  change (a + a' + (0 + 0) = a + a' + 0). ring.
 change (a * a' + (a * 0 + 0 * a') = a * a' + 0 * 0 + 0). ring.
Qed.

Instance: Proper (equiv ==> equiv ==> equiv) C.
Proof.
 intros x x' E y y' E'. unfold equiv, z_equiv. simpl.
 symmetry in E'. apply sg_mor; assumption.
Qed.

Lemma split_into_nats n m: C n m = NtoZ n + - NtoZ m.
Proof. ring_on_nat. Qed.

Global Instance: ∀ x y: Z, Decision (x = y)
  := λ x y, decide (pos x + neg y = pos y + neg x).
    (* An example of specialization: while there will be a generic decider that works for
     all Integers, this specialized one is potentially vastly more efficient. *)

(* Next, we show that Z is initial, and therefore a model of the integers. *)

Global Instance inject: IntegersToRing Z :=
  λ _ _ _ _ _ _ z, naturals_to_semiring N _ (pos z) + - naturals_to_semiring N _ (neg z).

(* Hint Rewrite preserves_0 preserves_1 preserves_mult preserves_plus: preservation.
  doesn't work for some reason, so we use: *)

Ltac preservation :=
   repeat (rewrite preserves_plus || rewrite preserves_mult || rewrite preserves_0 || rewrite preserves_1).

Section for_another_ring.

  Context `{Ring R}.

  Add Ring R: (stdlib_ring_theory R).

  Notation n_to_sr := (naturals_to_semiring N R).

  Instance: Proper (equiv ==> equiv) (integers_to_ring Z R).
  Proof.
   unfold equiv, z_equiv, integers_to_ring, inject. intros x y E.
   apply equal_by_zero_sum.
   transitivity (n_to_sr (pos x) + n_to_sr (neg y) + - (n_to_sr (neg x) + n_to_sr (pos y))); [ring|].
   do 2 rewrite <- preserves_plus.
   rewrite E. rewrite (commutativity (pos y)). ring.
  Qed.

  Ltac derive_preservation := unfold integers_to_ring, inject; simpl; preservation; ring.

  Let inject_preserves_plus x y: integers_to_ring Z R (x + y) = integers_to_ring Z R x + integers_to_ring Z R y.
  Proof. derive_preservation. Qed.

  Let preserves_mult x y: integers_to_ring Z R (x * y) = integers_to_ring Z R x * integers_to_ring Z R y.
  Proof. derive_preservation. Qed.

  Let preserves_1: integers_to_ring Z R 1 = 1.
  Proof. derive_preservation. Qed.

  Let preserves_0: integers_to_ring Z R 0 = 0.
  Proof. derive_preservation. Qed.

  Let preserves_inv x: integers_to_ring Z R (- x) = - integers_to_ring Z R x.
  Proof. derive_preservation. Qed.

  Instance: Setoid_Morphism (integers_to_ring Z R).
  Instance: SemiGroup_Morphism (integers_to_ring Z R) := { preserves_sg_op := inject_preserves_plus }.
  Instance: @SemiGroup_Morphism _ _ _ _ ring_mult ring_mult (integers_to_ring Z R) := { preserves_sg_op := preserves_mult }.
  Instance: @Monoid_Morphism _ _ _ _ (0:Z) (0:R) ring_plus ring_plus (integers_to_ring Z R) := { preserves_mon_unit := preserves_0 }.
  Instance: @Monoid_Morphism _ _ _ _ (1:Z) (1:R) ring_mult ring_mult (integers_to_ring Z R) := { preserves_mon_unit := preserves_1 }.
  Instance: @Group_Morphism _ _ _ _ ring_plus ring_plus (0:Z) (0:R) group_inv group_inv (integers_to_ring Z R) := { preserves_inv := preserves_inv }.
  Global Instance inject_mor: Ring_Morphism (integers_to_ring Z R).

  Section for_another_morphism.

    Context (inject': Z → R) `{!Ring_Morphism inject'}.

    Definition inject'_N: N → R := inject' ∘ (λ n, C n 0).

    Instance: Proper (equiv ==> equiv) inject'_N.
    Proof. intros x y E. unfold inject'_N. rewrite E. reflexivity. Qed.

    Instance: SemiRing_Morphism inject'_N.

    Lemma agree_on_nat: inject'_N = n_to_sr.
    Proof.
     intros x y E. rewrite E.
     apply (naturals.to_semiring_unique inject'_N).
    Qed.

    Lemma same_morphism: integers_to_ring Z R = inject'.
    Proof with intuition.
     intros [pos0 neg0] z' E. rewrite <- E. clear E z'.
     rewrite split_into_nats.
     preservation.
     rewrite preserves_inv, abstract_algebra.preserves_inv.
     rewrite (agree_on_nat pos0 pos0), (agree_on_nat neg0 neg0)...
     unfold integers_to_ring, inject. simpl. rewrite theory.rings.preserves_0.
     ring.
    Qed.

  End for_another_morphism.

End for_another_ring.

(* Initiality stated categorically: *)

Instance: Initial (ring.object Z).
Proof.
  apply integer_initial. intros. apply same_morphism. auto.
Qed.

Global Instance: Integers Z.

Lemma NtoZ_uniq x: naturals_to_semiring N Z x = NtoZ x.
Proof. symmetry. apply (theory.naturals.to_semiring_unique NtoZ x). Qed. 

Global Program Instance simpleZ_abs: IntAbs Z N := λ d: Z, nat_distance (pos d) (neg d).

Next Obligation.
Proof.
 rewrite NtoZ_uniq. destruct d.
 unfold equiv, z_equiv. simpl. 
 destruct nat_distance. simpl.
 destruct o as [A|A]; [right | left]; rewrite <- A; ring.
Qed.

Global Program Instance simpleZ_le_dec (x y: Z): Decision (x ≤ y) :=
  match decide (pos x + neg y ≤ pos y + neg x) with
  | left E => left _
  | right E => right _
  end.

Next Obligation.
  destruct (natural_precedes_with E) as [z Ez].
  apply (semiring.sr_precedes_from N z).
  rewrite NtoZ_uniq. unfold equiv, z_equiv. simpl. ring_simplify.
  rewrite <-Ez. ring.
Qed.

Next Obligation.
 intro F. apply E. destruct (semiring.sr_precedes_with N F) as [z Ez].
 apply (natural_precedes_from z).
 rewrite NtoZ_uniq in Ez. unfold equiv, z_equiv in Ez. simpl in Ez. ring_simplify in Ez.
 rewrite <-Ez. ring.
Qed. 

Global Instance: TotalOrder (sr_precedes (R:=Z)).
 intros x y.
 cut ((exists z, x + NtoZ z = y) ∨ (exists z, y + NtoZ z = x)).
  intros [[z E] | [z E]]; [left | right];
   apply (semiring.sr_precedes_from N z); rewrite NtoZ_uniq; assumption.
 unfold equiv, z_equiv.
 simpl.
 destruct (total_order (pos x + neg y) (pos y + neg x)) as [E | E];
   destruct (natural_precedes_with E) as [z Ez];
   [left | right]; exists z; ring_simplify; rewrite <- Ez; ring.
Qed.

End contents.
