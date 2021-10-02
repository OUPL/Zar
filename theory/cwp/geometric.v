(** Geometric series definitions and lemmas. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.

Require Import order.
Require Import Q.

Fixpoint geometric_series (a r : Q) (n : nat) :=
  match n with
  | O => 0
  | S n' => geometric_series a r n' + a * Qpow r n'
  end.

Definition geometric_sequence (a r : Q) (n : nat) :=
  a * Qpow r n.

Definition geometric_series' (a r : Q) := partial_sum (geometric_sequence a r).

Lemma geometric_series_geometric_series' (a r : Q) (i : nat) :
  geometric_series a r i == geometric_series' a r i.
Proof.  
  induction i; simpl.
  - reflexivity.
  - unfold geometric_series'; rewrite IHi, partial_sum_S; reflexivity.
Qed.

(** This slightly different series is used instead for wlp. It
  includes an additional term that is large initially but converges to
  zero as n increases. *)
Definition wlpf_series (a r : Q) (n : nat) :=
  geometric_series a r n + Qpow r n.

Definition pow_sequence (a : Q) (i : nat) := Qpow a i.

(* In general we require (|r| < 1) to ensure convergence, but here we
   assume the stronger condition (0 <= r < 1) for simplicity and
   because r will always be nonnegative for our purposes. *)
Axiom geometric_series_converges :
  forall a r,
    0 <= r -> r < 1 ->
    converges (geometric_series a r) (a / (1 - r)).

(* Axiom pow_series_converges : *)
(*   forall a, *)
(*     0 <= a -> a < 1 -> *)
(*     converges (pow_series a) 0. *)

From Coq Require Import
     Reals
     Raxioms
     Rpower.

Definition real_pow_sequence (a : R) (n : nat) : R := pow a n.

Lemma has_lb_real_pow_sequence (a : R) :
  (0 <= a)%R -> (a < 1)%R ->
  has_lb (real_pow_sequence a).
Proof.
  intros H0 H1.
  unfold has_lb.
  unfold bound. exists 0%R.
  unfold is_upper_bound. simpl.
  intros x H2.
  unfold EUn in H2.
  unfold opp_seq in H2.
  destruct H2 as [i H2]; subst.
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  unfold real_pow_sequence.
  apply pow_le; auto.
Qed.

Lemma archimedean (r : R) :
  exists n, (r < INR n)%R.
Proof.
  destruct (Rlt_le_dec 0 r).
  - assert (Hlt: (0 < / r)%R).
    { apply Rinv_0_lt_compat; auto. }
    generalize (archimed_cor1 (/ r) Hlt).
    intros [n [H Hnz]].
    exists n.
    rewrite <- Rinv_involutive.
    2: { apply not_0_INR; lia. }
    rewrite <- (Rinv_involutive r); try lra.
    apply Rinv_lt_contravar; auto.
    apply Rmult_lt_0_compat; auto.
    apply Rinv_0_lt_compat.
    replace 0%R with (INR 0) by reflexivity.
    apply lt_INR; auto.
  - exists (S O).
    eapply Rle_lt_trans; eauto.
    replace 0%R with (INR 0) by reflexivity.
    apply lt_INR; lia.
Qed.

Lemma ln_neg (a : R) :
  (0 < a)%R ->
  (a < 1)%R ->
  (ln a < 0)%R.
Proof.
  intro Hlt.
  replace 0%R with (ln 1).
  2: apply ln_1.
  apply ln_increasing; auto.
Qed.

Lemma real_pow_series_converges :
  forall a : R,
    (0 < a)%R -> (a < 1)%R ->
    forall eps : R, (0 < eps)%R -> exists n0, forall n, (n0 <= n)%nat -> (pow a n < eps)%R.
Proof.
  intros a H0 H1 eps Heps.
  generalize (archimedean (/ ln a * ln eps)); intros [n0 H2].
  exists n0; intros n Hle.
  apply ln_lt_inv; auto.
  { apply pow_lt; auto. }
  rewrite ln_pow; auto.
  apply Rmult_lt_reg_l with (r := Ropp (Rinv (ln a))%R).
  { rewrite Ropp_inv_permute.
    2: apply ln_neq_0; auto; lra.
    apply Rinv_0_lt_compat.
    apply Ropp_0_gt_lt_contravar.
    apply Rlt_gt.
    apply ln_neg; auto. }
  rewrite 2!Ropp_mult_distr_l_reverse.
  apply Ropp_lt_contravar.
  replace (INR n * ln a)%R with (ln a * INR n)%R.
  2: { apply Rmult_comm. }
  rewrite <- Rmult_assoc.
  replace (/ ln a * ln a)%R with 1%R.
  2: { field; apply ln_neq_0; lra. }
  rewrite Rmult_1_l.
  apply Rlt_le_trans with (INR n0); auto.
  apply le_INR; auto.
Qed.

Definition converges (g : nat -> Q) (lim : Q) :=
  forall eps,
    0 < eps ->
    exists n0, forall n,
        (n0 <= n)%nat -> Qabs (lim - g n) < eps.

Require Import Coq.micromega.Lqa.

Lemma Q2R_pow (a : Q) (n : nat) :
  (Q2R a ^ n)%R = Q2R (Qpow a n).
Proof.
  revert a; induction n; intro a; simpl.
  - rewrite RMicromega.Q2R_1; reflexivity.
  - rewrite IHn.
    rewrite Qreals.Q2R_mult; reflexivity.
Qed.

Lemma pow_series_converges :
  forall a,
    0 <= a -> a < 1 ->
    converges (pow_sequence a) 0.
Proof.
  intros a H0 H1 eps Heps.
  unfold pow_sequence.
  destruct (Qeq_bool 0 a) eqn:Ha.
  apply Qeq_bool_eq in Ha.
  - exists (S O); intros n Hle.
    rewrite <- Ha.
    rewrite Qabs_Qminus.
    rewrite Qabs_Qminus_Qle.
    + rewrite Qminus_0_r.
      destruct n. inversion Hle.
      simpl. rewrite Qmult_0_l; auto.
    + apply Qpow_nonnegative; lra.
  - apply Qeq_bool_neq in Ha.
    assert (H0': (0 < Q2R a)%R).
    { rewrite <- RMicromega.Q2R_0.
      apply Qreals.Qlt_Rlt; lra. }
    assert (H1': (Q2R a < 1)%R).
    { rewrite <- RMicromega.Q2R_1.
      apply Qreals.Qlt_Rlt; lra. }
    assert (Heps': (0 < Q2R eps)%R).
    { rewrite <- RMicromega.Q2R_0.
      apply Qreals.Qlt_Rlt; lra. }
    generalize (real_pow_series_converges H0' H1' Heps').
    intros [n0 H].
    exists n0; intros n Hle.
    specialize (H n Hle).
    rewrite Qabs_Qminus.
    rewrite Qabs_Qminus_Qle, Qminus_0_r.
    + apply Qreals.Rlt_Qlt.
      rewrite <- Q2R_pow; auto.
    + apply Qpow_nonnegative; auto.
Qed.

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
  set (f := (geometric_series a r)).
  set (g := fun i => Qpow r i).
  cut (converges (fun i => f i + g i) (a / (1 - r) + 0)).
  - intro Hc; eapply Proper_converges; eauto. reflexivity. lra.
  - apply sum_converges. split.
    + apply geometric_series_converges; auto.
    + apply pow_series_converges; auto.
Qed.

Lemma geometric_series_succ (a r : Q) (n : nat) :
  a + r * geometric_series a r n == geometric_series a r (S n).
Proof.
  induction n; simpl.
  - lra.
  - rewrite Qmult_plus_distr_r, Qplus_assoc, IHn; simpl; lra.
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
  unfold flip, leq in *; simpl in *; unfold Nat.le in Hle.
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

Lemma geometric_series'_supremum (a r : Q) :
  0 <= a -> 0 <= r -> r < 1 ->
  supremum (a / (1 - r)) (geometric_series' a r).
Proof.
  intros H0 H1 H2.
  eapply supremum_f_Qeq.
  - apply geometric_series_geometric_series'.
  - apply geometric_series_supremum; auto.
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
  subst. induction m; simpl; auto; try reflexivity.
  rewrite IHm, Heq1, Heq2; reflexivity.
Qed.
