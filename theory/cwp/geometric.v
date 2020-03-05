(** Geometric series definitions and lemmas. *)

Set Implicit Arguments.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.

Require Import order.
Require Import Q.

Fixpoint geometric_series (a r : Q) (n : nat) :=
  match n with
  | O => a
  | S n' => geometric_series a r n' + a * Qpow r n
  end.

(** This is the one being used currently. *)
Fixpoint geometric_series'' (a r : Q) (n : nat) :=
  match n with
  | O => 0
  | S n' => geometric_series'' a r n' + a * Qpow r n'
  end.

(** This slightly different series is used instead for wlp. *)
Definition wlpf_series (a r : Q) (n : nat) :=
  geometric_series'' a r n + Qpow r n.

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
    rewrite H, <- Qplus_assoc, sum_Q_list_l, Qplus_comm; simpl.
    assert (H0: f O * r * Qpow r n == f (1 + n)%nat).
    { unfold f. simpl. field. }
    rewrite H0, <- Qplus_assoc, sum_Q_list_r.
    unfold f; simpl; field.
Qed.

Lemma geometric_series_geometric_series'' (a r : Q) (n : nat) :
  geometric_series a r n == geometric_series'' a r (S n).
Proof.
  induction n; simpl.
  - lra.
  - rewrite IHn; reflexivity.
Qed.

Lemma geometric_series_cons_geometric_series'' (a r : Q) (n : nat) :
  cons_chain 0 (geometric_series a r) n == geometric_series'' a r n.
Proof.
  destruct n.
  - reflexivity.
  - apply geometric_series_geometric_series''.
Qed.

Definition pow_series (a : Q) (i : nat) := Qpow a i.

(* In general we require (|r| < 1) to ensure convergence, but here we
   assume the stronger condition (0 <= r < 1) for simplicity and
   because r will always be nonnegative for our purposes. *)
Axiom geometric_series_converges :
  forall a r,
    0 <= r -> r < 1 ->
    converges (geometric_series a r) (a / (1 - r)).

Axiom geometric_series''_converges :
  forall a r,
    0 <= r -> r < 1 ->
    converges (geometric_series'' a r) (a / (1 - r)).

Axiom pow_series_converges :
  forall a,
    0 <= a -> a < 1 ->
    converges (pow_series a) 0.


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

Lemma sum_converges f g limf limg :
  converges f limf /\ converges g limg ->
  converges (fun i => f i + g i) (limf + limg).
Proof.
  unfold converges.
  intros [Hf Hg] eps Heps.
  assert (Heps2: 0 < eps/(2#1)).
  { apply Qlt_shift_div_l; lra. }
  specialize (Hf (eps/(2#1)) Heps2).
  specialize (Hg (eps/(2#1)) Heps2).
  destruct Hf as [n Hf].
  destruct Hg as [m Hg].
  exists (max n m). intros i Hle.
  assert (Hn: (n <= i)%nat).
  { eapply Nat.max_lub_l; eauto. }
  assert (Hm: (m <= i)%nat).
  { eapply Nat.max_lub_r; eauto. }
  specialize (Hf i Hn).
  specialize (Hg i Hm).
  apply Qle_lt_trans with (Qabs (limf - f i) + Qabs (limg - g i)).
  - assert (H: limf + limg - (f i + g i) == limf - f i + (limg - g i)).
    { lra. }
    rewrite H.
    apply Qabs_triangle. (* triangle inequality *)
  - apply Qlt_Qplus_Qdiv2; auto.
Qed.

Lemma wlpf_series_converges :
  forall a r,
    0 <= r -> r < 1 ->
    converges (wlpf_series a r) (a / (1 - r)).
Proof.
  intros a r Hle Hlt.
  set (f := (geometric_series'' a r)).
  set (g := fun i => Qpow r i).
  cut (converges (fun i => f i + g i) (a / (1 - r) + 0)).
  - intro Hc; eapply Proper_converges; eauto. reflexivity. lra.
  - apply sum_converges. split.
    + apply geometric_series''_converges; auto.
    + apply pow_series_converges; auto.
Qed.

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

Lemma geometric_series''_succ (a r : Q) (n : nat) :
  a + r * geometric_series'' a r n == geometric_series'' a r (S n).
Proof.
  rewrite <- geometric_series_geometric_series''.
  induction n; simpl.
  - lra.
  - rewrite <- IHn; lra.
Qed.

Lemma geometric_series_monotone (a r : Q) :
  0 <= a -> 0 <= r ->
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

Lemma geometric_series''_monotone (a r : Q) :
  0 <= a -> 0 <= r ->
  monotone (geometric_series'' a r).
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

Lemma wlpf_series_succ_le (a r : Q) (i : nat) :
  0 <= a -> 0 <= r -> r < 1 ->
  a + r <= 1 ->
  wlpf_series a r (S i) <= wlpf_series a r i.
Proof.
  intros H0 H1 H2 H3.
  unfold wlpf_series.
  simpl.
  cut (a * Qpow r i + r * Qpow r i <= Qpow r i).
  { lra. }
  assert (H': a * Qpow r i + r * Qpow r i == (a + r) * Qpow r i).
  { lra. }
  rewrite H'; clear H'.
  apply Qpow_nonnegative with (n:=i) in H1.
  nra.
Qed.

Lemma wlpf_series_monotone_decreasing (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
  a + r <= 1 ->
  monotone_decreasing (wlpf_series a r).
Proof.
  intros H0 H1 H2 H3 n m Hle.
  unfold leq in *; simpl in *; unfold Nat.le in Hle.
  induction m.
  - destruct n; try lra; lia.
  - destruct (Nat.eqb_spec n (S m)); subst.
    + lra.
    + assert (Hle' : (n <= m)%nat).
      { lia. }
      specialize (IHm Hle').
      eapply Qle_trans; eauto.
      apply wlpf_series_succ_le; auto.
Qed.

Lemma geometric_series_supremum (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
  supremum (a / (1 - r)) (geometric_series a r).
Proof.
  intros; apply converges_from_below_supremum.
  - intro i. 
    apply geometric_series_monotone; auto.
    unfold leq; simpl; unfold Nat.le; lia.
  - apply geometric_series_converges; auto.
Qed.

Lemma wlpf_series_infimum (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
  a + r <= 1 ->
  infimum (a / (1 - r)) (wlpf_series a r).
Proof.
  intros; apply converges_from_above_infimum.
  - intro i. simpl.
    apply wlpf_series_monotone_decreasing; auto.
    unfold leq; simpl; unfold Nat.le; lia.
  - apply wlpf_series_converges; auto.
Qed.

Lemma geometric_supremum (ch : nat -> Q) (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
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

Lemma wlpf_infimum (ch : nat -> Q) (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
  a + r <= 1 ->
  ch ==f wlpf_series a r ->
  infimum (a / (1 - r)) ch.
Proof.
  intros Hle_a Hle_r0 Hle_r1 Hsum Heq.
  apply converges_from_above_infimum.
  - intro i. unfold f_Qeq in Heq. rewrite 2!Heq.
    apply wlpf_series_succ_le; auto.
  - eapply Proper_converges. intro; apply Heq. reflexivity.
    apply wlpf_series_converges; auto.
Qed.

Lemma geometric''_supremum (ch : nat -> Q) (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
  ch ==f geometric_series'' a r ->
  supremum (a / (1 - r)) ch.
Proof.
  intros Hle_a Hle_r0 Hle_r1 Heq.
  apply converges_from_below_supremum.
  - intro i. unfold f_Qeq in Heq. rewrite 2!Heq.
    apply geometric_series''_monotone; auto; simpl; unfold Nat.le; lia.
  - eapply Proper_converges; eauto. reflexivity.
    apply geometric_series''_converges; auto.
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
