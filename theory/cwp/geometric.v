Set Implicit Arguments.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.

Require Import order.
Require Import Q.

Fixpoint geometric_series (a r : Q) (n : nat) :=
  match n with
  | O => a
  | S n' => geometric_series a r n' + a * Qpow r n
  end.

Definition geometric_series' (a r : Q) (n : nat) : Q :=
  sum_Q_list (map (fun n => a * Qpow r n) (seq O (S n))).

Lemma geometric_series_geometric_series' (a r : Q) (n : nat) :
  geometric_series a r n == geometric_series' a r n.
Proof.
  unfold geometric_series'.
  induction n.
  - simpl; field.
  - simpl in *.
    rewrite IHn. ring_simplify.
    set (f := fun n => a * Qpow r n).
    assert (a == f O).
    { unfold f. simpl. field. }
    rewrite H.
    rewrite <- Qplus_assoc.
    rewrite sum_Q_list_l.
    rewrite Qplus_comm.
    simpl.
    assert (H0: f O * r * Qpow r n == f (1 + n)%nat).
    { unfold f. simpl. field. }
    rewrite H0.
    rewrite <- Qplus_assoc.
    rewrite sum_Q_list_r.
    unfold f. simpl. field.
Qed.

(* In general we require (|r| < 1) to ensure convergence, but here we
   assume the stronger condition (0 <= r < 1) for simplicity and
   because r will always be nonnegative for our purposes. *)
Axiom geometric_series_converges :
  forall a r,
    0 <= r -> r < 1 ->
    converges (geometric_series a r) (a / (1 - r)).

(* Definition converges_from_below (g : nat -> Q) (lim : Q) := *)
(*   forall eps, 0 < eps -> *)
(*          exists n0, forall n, *)
(*              (n0 <= n)%nat -> lim - g n < eps. *)

(* Axiom geometric_series_converges : *)
(*   forall a r, converges (geometric_series a r) (a / (1 - r)). *)

(* Axiom geometric_series_converges : *)
(*   forall a r eps, *)
(*     0 <= a <= 1 -> 0 <= r -> r < 1 -> 0 < eps -> *)
(*     exists n0, forall n, *)
(*         (n0 <= n)%nat -> (a / (1 - r)) - geometric_series a r n < eps. *)

(* Definition prefix_series {A : Type} (n : nat) (f : nat -> A) (i : nat) := *)
(*   f (i-n)%nat. *)

(* Definition postfix_series {A : Type} (n : nat) (f : nat -> A) (i : nat) := *)
(*   f (i-n)%nat. *)

Lemma geometric_series_succ (a r : Q) (n : nat) :
  a + r * geometric_series a r n == geometric_series a r (S n).
Proof.
  rewrite 2!geometric_series_geometric_series'.
  unfold geometric_series'. simpl.
  set (f := fun i => a * Qpow r i).
  assert (H0: a * 1 == f O).
  { reflexivity. }
  rewrite H0.
  rewrite sum_Q_list_l.
  assert (H1: a * (r * 1) == f (S O)).
  { reflexivity. }
  rewrite H1.
  rewrite sum_Q_list_l. rewrite sum_Q_list_l.
  rewrite sum_Q_list_distr. unfold f.
  rewrite sum_Q_list_Qpow; simpl; field.
Qed.

Lemma geometric_series_supremum (a r : Q) :
  0 <= a ->
  0 <= r -> r < 1 ->
  supremum (a / (1 - r)) (geometric_series a r).
Proof.
  intros; apply converges_from_below_supremum.
  - intro i. simpl.
    assert (0 <= Qpow r i).
    { apply Qpow_nonnegative; auto. }
    assert (0 <= r * Qpow r i). nra. nra.
  - apply geometric_series_converges; auto.
Qed.

Lemma geometric_series_monotone (a r : Q) :
  (0 <= a) -> (0 <= r) ->
  monotone (geometric_series a r).
Proof.
  intros Hle_a Hle_r n m Hleq. simpl in *.
  induction m. simpl.
  - inversion Hleq; subst; simpl; lra.
  - unfold Nat.le in *.
    destruct (Nat.eqb_spec n (S m)); subst. lra.
    assert (Hle: (n <= m)%nat). lia.
    apply IHm in Hle. simpl.
    generalize (@Qpow_nonnegative r m Hle_r).
    intro Hle_pow.
    assert (0 <= r * Qpow r m); nra.
Qed.

Lemma geometric_supremum (ch : nat -> Q) (a r : Q) :
  0 <= a ->
  0 <= r -> r < 1 ->
  ch ==f geometric_series a r ->
  supremum (a / (1 - r)) ch.
Proof.
  intros Hle_a Hle_r0 Hle_r1 Heq.
  apply converges_from_below_supremum.
  - intro i. unfold f_Qeq in Heq. rewrite 2!Heq.
    apply geometric_series_monotone; auto; simpl; unfold Nat.le; lia.
  - eapply Proper_converges; eauto. reflexivity.
    apply geometric_series_converges; auto.
Qed.

Instance Proper_geometric_series
  : Proper (Qeq ==> Qeq ==> eq ==> Qeq) geometric_series.
Proof.
  intros a b Heq1 c d Heq2 n m Heq3.
  subst. induction m; simpl; auto.
  rewrite IHm, Heq1, Heq2; reflexivity.
Qed.

Lemma geometric_series_const (a : Q) (n : nat) :
  geometric_series a 0 n == a.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn; lra.
Qed.
