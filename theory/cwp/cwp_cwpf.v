(** The relational and functional specifications of CWP coincide when
    all loops are iid. *)

Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Local Open Scope program_scope.
Import ListNotations.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ListMonad.

Require Import compile.
Require Import cpGCL.
Require Import cwp.
Require Import cwpf_infer.
Require Import geometric.
Require Import infer.
Require Import order.
Require Import Q.
Require Import tree.

Open Scope cpGCL_scope.
Open Scope Q_scope.

Lemma wpf_linear c f g st :
  wpf c (fun st => f st + g st) st == wpf c f st + wpf c g st.
Proof.
  revert f g st.
  induction c; intros f g st; simpl.
  - reflexivity.
  - unfold const; lra.
  - reflexivity.
  - unfold compose. rewrite <- IHc1.
    apply Proper_wpf; auto.
    intros ?; apply IHc2.
  - destruct (e st); auto.
  - rewrite IHc1, IHc2. lra.
  - destruct (e st); try reflexivity.
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) st) 1).
    + rewrite q, Qminus_cancel, 3!Qdiv_0_den; lra.
    + assert (H0: forall a b c, ~ c == 0 -> a / c + b / c == (a + b) / c).
      { intros. field; auto. }
      rewrite H0.
      * rewrite <- IHc. apply Qeq_Qdiv.
        ++ apply Proper_wpf; auto.
           intro x; destruct (e x); lra.
        ++ reflexivity.
      * lra.
  - destruct (e st); lra.
Qed.

Lemma wpf_linear' c (e : exp) f g st :
  wpf c (fun x => if e x then f x else g x) st ==
  wpf c (fun x => if e x then f x else 0) st +
  wpf c (fun x => if e x then 0 else g x) st.
Proof.
  rewrite <- wpf_linear; apply Proper_wpf; auto.
  intro x; destruct (e x); lra.
Qed.

(** wpf preserves constant zero. *)
Lemma wpf_strict c f x :
  f ==f const 0 ->
  wpf c f x == 0.
Proof.
  revert f x.
  induction c; simpl; unfold const in *; intros f x Heq; auto; try reflexivity.
  - unfold compose; auto.
  - destruct (e x); auto.
  - rewrite IHc1, IHc2; auto; lra.
  - destruct (e x); auto.
    rewrite IHc.
    + apply Qdiv_0_num.
    + intro y; destruct (e y); auto; reflexivity.
  - destruct (e x); auto; reflexivity.
Qed.

(** [wpf c f] is bounded by 1 whenever f is. I think this is true more
  generally for any upper bound. *)
Lemma wpf_bounded c f :
  wf_cpGCL c ->
  (forall x, f x <= 1) ->
  forall x, wpf c f x <= 1.
Proof.
  revert f.
  induction c; intros f Hwf Hle x; simpl; inversion Hwf; subst; auto.
  - unfold const; lra.
  - apply IHc1; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 f H3 Hle x); specialize (IHc2 f H4 Hle x); nra.
  - set (ea := wpf c (fun st => if e st then 0 else f st) x).
    set (eb := wpf c (fun st => if e st then 1 else 0) x).
    assert (eb <= 1).
    { apply IHc; auto.
      intro y; destruct (e y); lra. }
    destruct (e x); auto.
    destruct (Qeq_dec eb 1).
    { rewrite q, Qminus_cancel, Qdiv_0_den; lra. }
    apply ratio_Qle_sum. lra.
    rewrite Qmult_1_r.
    assert (ea <= 1).
    { apply IHc; auto.
      intro y; destruct (e y); auto; lra. }
    assert (H': eb == wpf c (fun x => if e x then const 1 x else 0) x).
    { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
    rewrite H'; clear H'.
    unfold ea.
    rewrite Qplus_comm.
    rewrite <- wpf_linear'.
    apply IHc; auto.
    intro y; destruct (e y); auto.
    unfold const; lra.
  - destruct (e x); auto; lra.
Qed.

(** Similar to [wpf_linear] but decomposes into wpf and wlpf. *)
Lemma wlpf_linear c f g st :
  wlpf c (fun st => f st + g st) st == wpf c f st + wlpf c g st.
Proof.
  revert f g st.
  induction c; intros f g st; simpl.
  - reflexivity.
  - unfold const; lra.
  - reflexivity.
  - unfold compose. rewrite <- IHc1.
    apply Proper_wlpf; auto.
    intros ?; apply IHc2.
  - destruct (e st); auto.
  - rewrite IHc1, IHc2. lra.
  - destruct (e st); try reflexivity.
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) st) 1).
    + rewrite Qeq_eq_bool; auto.
      rewrite q, Qminus_cancel, Qdiv_0_den; lra.
    + rewrite Qeq_bool_false; auto.
      assert (H0: forall a b c, ~ c == 0 -> a / c + b / c == (a + b) / c).
      { intros. field; auto. }
      rewrite H0.
      * rewrite <- IHc. apply Qeq_Qdiv.
        ++ apply Proper_wlpf; auto.
           intro x; destruct (e x); lra.
        ++ reflexivity.
      * lra.
  - destruct (e st); lra.
Qed.

Lemma wlpf_linear' c (e : exp) f g st :
  wlpf c (fun st' => if e st' then f st' else g st') st ==
  wpf c (fun st' => if e st' then f st' else 0) st +
  wlpf c (fun st' => if e st' then 0 else g st') st.
Proof.
  rewrite <- wlpf_linear; apply Proper_wlpf; auto.
  intro x; destruct (e x); lra.
Qed.

(** Similar to [wpf_bounded]. *)
Lemma wlpf_bounded c f :
  wf_cpGCL c ->
  (forall x, f x <= 1) ->
  forall x, wlpf c f x <= 1.
Proof.
  revert f.
  induction c; intros f Hwf Hle x; simpl; inversion Hwf; subst; auto.
  - unfold const; lra.
  - apply IHc1; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 f H3 Hle x); specialize (IHc2 f H4 Hle x); nra.
  - set (ea := wlpf c (fun st => if e st then 0 else f st) x).
    set (eb := wpf c (fun st => if e st then 1 else 0) x).
    destruct (e x); auto.
    assert (eb <= 1).
    { apply wpf_bounded; auto.
      intro y; destruct (e y); lra. }
    destruct (Qeq_dec eb 1).
    { rewrite q. simpl. lra. }
    rewrite Qeq_bool_false; auto.
    apply ratio_Qle_sum. lra.
    rewrite Qmult_1_r.
    assert (ea <= 1).
    { apply IHc; auto.
      intro y; destruct (e y); auto; lra. }
    assert (H': eb == wpf c (fun x => if e x then const 1 x else 0) x).
    { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
    rewrite H'; clear H'.
    unfold ea.
    rewrite Qplus_comm.
    rewrite <- wlpf_linear'.
    apply IHc; auto.
    intro y; destruct (e y); auto.
    unfold const; lra.
  - destruct (e x); auto; lra.
Qed.

(** [wpf c [e]] and [wpf c [~e]] sum to at most 1. *)
Lemma wpf_disjoint_le_1 c (e : exp) st :
  wf_cpGCL c ->
  wpf c (fun x => if e x then 1 else 0) st +
  wpf c (fun x => if e x then 0 else 1) st <= 1.
Proof.
  intros Hwf.
  set (a := wpf c (fun st : St => if e st then 1 else 0) st).
  set (b := wpf c (fun st : St => if e st then 0 else 1) st).
  assert (a == wpf c (fun x => if e x then const 1 x else 0) st).
  { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
  rewrite H. unfold b.
  rewrite <- wpf_linear'.
  apply wpf_bounded; auto.
  intro y; destruct (e y); auto; unfold const; lra.
Qed.

(** [wpf c [e]] and [wlpf c [~e]] sum to at most 1. *)
Lemma wlpf_disjoint_le_1 c (e : exp) st :
  wf_cpGCL c ->
  wpf c (fun x => if e x then 1 else 0) st +
  wlpf c (fun x => if e x then 0 else 1) st <= 1.
Proof.
  intros Hwf.
  set (a := wpf c (fun st : St => if e st then 1 else 0) st).
  set (b := wlpf c (fun st : St => if e st then 0 else 1) st).
  assert (a == wpf c (fun x => if e x then const 1 x else 0) st).
  { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
  rewrite H. unfold b.
  rewrite <- wlpf_linear'.
  apply wlpf_bounded; auto.
  intro y; destruct (e y); auto; unfold const; lra.
Qed.

(** Given that f is a valid expectation (bounded below by 0), so is
  [wpf c f].*)
Lemma wpf_expectation c f :
  wf_cpGCL c ->
  expectation f ->
  expectation (wpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hexp; simpl; inversion Hwf; subst; auto.
  - unfold const; intros ?; lra.
  - intros ?; apply Hexp.
  - apply IHc1; auto.
  - intro x; destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - intro x.
    specialize (IHc1 f H3 Hexp x); specialize (IHc2 f H4 Hexp x).
    nra.
  - intro x. simpl.
    destruct (e x); auto.
    assert (wpf c (fun st => if e st then 1 else 0) x <= 1).
    { apply wpf_bounded; auto.
      intro st; destruct (e st); auto; lra. }
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) x) 1).
    + rewrite q, Qminus_cancel, Qdiv_0_den; lra.
    + apply Qle_shift_div_l. lra. rewrite Qmult_0_l. apply IHc; auto.
      intro st; destruct (e st); auto; lra.
  - intro x; destruct (e x); auto; lra.
Qed.

(** Similar to [wpf_expectation]. *)
Lemma wlpf_expectation c f :
  wf_cpGCL c ->
  expectation f ->
  expectation (wlpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hexp; simpl; inversion Hwf; subst; auto.
  - unfold const; intros ?; lra.
  - intros ?; apply Hexp.
  - apply IHc1; auto.
  - intro x; destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - intro x.
    specialize (IHc1 f H3 Hexp x); specialize (IHc2 f H4 Hexp x).
    nra.
  - intro x. simpl.
    destruct (e x); auto.
    assert (wpf c (fun st => if e st then 1 else 0) x <= 1).
    { apply wpf_bounded; auto.
      intro st; destruct (e st); auto; lra. }
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) x) 1).
    + apply Qeq_bool_iff in q. rewrite q; lra.
    + rewrite Qeq_bool_false; auto; apply Qle_shift_div_l.
      lra. rewrite Qmult_0_l. apply IHc; auto.
      intro st; destruct (e st); auto; lra.
  - intro x; destruct (e x); auto; lra.
Qed.

(** Putting [wlpf_bounded] and [wlpf_expectation] together. *)
Lemma wlpf_bounded_expectation c f :
  wf_cpGCL c ->
  bounded_expectation f 1 ->
  bounded_expectation (wlpf c f) 1.
Proof.
  intros Hwf Hf x; split.
  - apply wlpf_expectation; auto.
    intro y; apply Hf.
  - apply wlpf_bounded; auto.
    intro y; apply Hf.
Qed.

(** Given that a loop is iid, its sequence of unrollings yields a
  geometric series progression for any f. *)
Lemma wpf_chain_geometric_series f e c st i :
  e st = true ->
  iid_wpf e c ->
  wpf (unroll e c i) f st ==
  geometric_series (wpf c (fun x => if e x then 0 else f x) st)
                   (wpf c (indicator e) st) i.
Proof.
  intros He Hiid; induction i.
  - simpl; rewrite He; reflexivity.
  - unfold iid_wpf in Hiid.
    rewrite Hiid; auto.
    rewrite IHi.
    rewrite Qplus_comm.
    apply geometric_series_succ.
Qed.

(** Similar to [wpf_chain_geometric_series], but wrt a geometric
  series modified with an additional term which makes the series
  actually decreasing. *)
Lemma wlpf_chain_series f e c st i :
  e st = true ->
  iid_wlpf e c ->
  wlpf (unroll e c i) f st ==
  wlpf_series (wlpf c (fun x => if e x then 0 else f x) st)
              (wpf c (indicator e) st) i.
Proof.
  unfold wlpf_series; intros He Hiid; induction i.
  - simpl; rewrite He; reflexivity.
  - unfold iid_wlpf in Hiid.
    rewrite Hiid, IHi, Qplus_comm; auto; simpl.
    rewrite Qmult_plus_distr_r, Qplus_assoc, geometric_series_succ.
    reflexivity.
Qed.

Lemma wf_unroll c e i :
  wf_cpGCL c ->
  wf_cpGCL (unroll e c i).
Proof. induction i; repeat constructor; auto. Qed.

(** wpf is monotone. That is, [∀ f g, f <= g -> wpf c f <= wpf c g] for
  any command c. *)
Lemma wpf_monotone c :
  wf_cpGCL c ->
  monotone (wpf c).
Proof.
  induction c; unfold monotone, leq; simpl;
    intros Hwf f g Hleq x; auto; inversion Hwf; subst.
  - lra.
  - apply IHc1; auto; apply IHc2; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 H3 f g Hleq x).
    specialize (IHc2 H4 f g Hleq x).
    unfold leq in *; simpl in *; nra.
  - destruct (e x); auto.
    specialize (IHc H0).
    cut (wpf c (fun st' : St => if e st' then 0 else f st') x <=
         wpf c (fun st' : St => if e st' then 0 else g st') x).
    { intros.
      destruct (Qeq_dec (wpf c (fun x => if e x then 1 else 0) x) 1).
      { rewrite q, Qminus_cancel, 2!Qdiv_0_den; lra. }
      assert (wpf c (fun x => if e x then 1 else 0) x <= 1).
      { apply wpf_bounded; auto.
        intro y; destruct (e y); lra. }
      apply Qle_Qdiv; auto.
      lra. }
    apply IHc; simpl.
    intro y; destruct (e y); auto; lra.
  - destruct (e x); auto; lra.
Qed.

(** Similar to [wlpf_monotone]. *)
Lemma wlpf_monotone c :
  wf_cpGCL c ->
  monotone (wlpf c).
Proof.
  induction c; unfold monotone, leq; simpl;
    intros Hwf f g Hleq x; auto; inversion Hwf; subst.
  - lra.
  - apply IHc1; auto; apply IHc2; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 H3 f g Hleq x).
    specialize (IHc2 H4 f g Hleq x).
    unfold leq in *; simpl in *; nra.
  - destruct (e x); auto.
    destruct (Qeq_dec (wpf c (fun st' : St => if e st' then 1 else 0) x) 1).
    { rewrite q; simpl; lra. }
    rewrite Qeq_bool_false; auto.
    specialize (IHc H0).
    cut (wlpf c (fun st' : St => if e st' then 0 else f st') x <=
         wlpf c (fun st' : St => if e st' then 0 else g st') x).
    { intros.
      destruct (Qeq_dec (wpf c (fun x => if e x then 1 else 0) x) 1).
      { rewrite q, Qminus_cancel, 2!Qdiv_0_den; lra. }
      assert (wpf c (fun x => if e x then 1 else 0) x <= 1).
      { apply wpf_bounded; auto.
        intro y; destruct (e y); lra. }
      apply Qle_Qdiv; auto.
      lra. }
    apply IHc; simpl.
    intro y; destruct (e y); auto; lra.
  - destruct (e x); auto; lra.
Qed.

(** A corollary of [wlpf_disjoint_le_1] that isn't being used at the
  moment. *)
(* Lemma wpf_indicator_1_0 c (e : exp) st : *)
(*   wf_cpGCL c -> *)
(*   wpf c (fun x => if e x then 1 else 0) st == 1 -> *)
(*   wpf c (fun x => if e x then 0 else 1) st == 0. *)
(* Proof. *)
(*   unfold indicator. *)
(*   set (a := wpf c (fun st : St => if e st then 1 else 0) st). *)
(*   set (b := wpf c (fun st : St => if e st then 0 else 1) st). *)
(*   intros Hwf Heq. *)
(*   cut (a + b <= 1). *)
(*   { intros. *)
(*     assert (0 <= a). *)
(*     { apply wpf_expectation; auto. *)
(*       intro y; destruct (e y); lra. } *)
(*     assert (0 <= b). *)
(*     { apply wpf_expectation; auto. *)
(*       intro y; destruct (e y); auto; lra. } *)
(*     lra. } *)
(*   apply wpf_disjoint_le_1; auto. *)
(* Qed. *)

(** It was unclear how to prove this directly so we make use of tree
  compilation. We perform all reasoning on the trees the commands
  compile to, and then reflect the result back to wpf via
  [wpf_infer_f]. *)
Lemma wpf_indicator_1_f_0 c (e : exp) f st :
  wf_cpGCL c ->
  wpf c (fun x => if e x then 1 else 0) st == 1 ->
  wpf c (fun x => if e x then 0 else f x) st == 0.
Proof.
  intros Hwf Heq.
  rewrite wpf_infer_f with (n:=O); auto.
  rewrite wpf_infer_f with (n:=O) in Heq; auto.
  unfold compose, evalCompile, evalState in *.
  destruct (runState (compile c) O) eqn:Hc. simpl in *.
  assert (Hnotbound: not_bound_in (S n) (t st)).
  { apply bound_in_not_bound_in; intro HC.
    eapply compile_bound_labels in HC; eauto; lia. }
  assert (Hnotin: not_in (S n) (t st)).
  { apply not_in_not_bound_and_not_free. split; auto.
    apply free_in_not_free_in; intro HC.
    eapply compile_free_in_0 in HC; eauto; lia. }
  assert (Hwft: wf_tree' (t st)).
  { eapply compile_wf_tree'; eauto. }
  rewrite <- infer_fail_tree_bind_infer_f with (m := S n) in Heq; auto.
  + apply (infer_f_fail f) in Heq.
    * rewrite <- infer_f_bind_fail_f_neg; eauto.
    * apply wf_tree_bind.
      ++ intros ? y; destruct (e y); constructor.
      ++ apply wf_tree'_wf_tree; auto.
      ++ intros y; destruct (e y); constructor.
    * apply bound_in_not_bound_in; intro HC.
      apply bound_in_bind in HC. destruct HC.
      ++ apply bound_in_not_bound_in in Hnotbound; congruence.
      ++ destruct H as [y Hbound].
         destruct (e y); inversion Hbound.
  + apply wf_tree'_wf_tree; auto.
Qed.

(** Similar to [wpf_indicator_1_f_0]. *)
Lemma wlpf_indicator_1_f_0 c (e : exp) f st :
  wf_cpGCL c ->
  wpf c (fun x => if e x then 1 else 0) st == 1 ->
  wlpf c (fun x => if e x then 0 else f x) st == 0.
Proof.
  intros Hwf Heq.
  rewrite wlpf_infer_f_lib with (n:=O); auto.
  rewrite wpf_infer_f with (n:=O) in Heq; auto.
  unfold compose, evalCompile, evalState in *.
  destruct (runState (compile c) O) eqn:Hc. simpl in *.
  assert (Hnotbound: not_bound_in (S n) (t st)).
  { apply bound_in_not_bound_in; intro HC.
    eapply compile_bound_labels in HC; eauto; lia. }
  assert (Hnotin: not_in (S n) (t st)).
  { apply not_in_not_bound_and_not_free. split; auto.
    apply free_in_not_free_in; intro HC.
    eapply compile_free_in_0 in HC; eauto; lia. }
  assert (Hwft: wf_tree' (t st)).
  { eapply compile_wf_tree'; eauto. }
  rewrite <- infer_fail_tree_bind_infer_f with (m := S n) in Heq; auto.
  + apply (infer_f_lib_fail f) in Heq.
    * rewrite <- infer_f_lib_bind_fail_f_neg; eauto.
    * apply wf_tree_bind.
      ++ intros ? y; destruct (e y); constructor.
      ++ apply wf_tree'_wf_tree; auto.
      ++ intros y; destruct (e y); constructor.
    * apply bound_in_not_bound_in; intro HC.
      apply bound_in_bind in HC. destruct HC.
      ++ apply bound_in_not_bound_in in Hnotbound; congruence.
      ++ destruct H as [y Hbound].
         destruct (e y); inversion Hbound.
  + apply wf_tree'_wf_tree; auto.
Qed.

(** The statement of the conclusion here is slightly unnatural but
  convenient for us. This lemma essentially says that whenever a loop
  body is divergent (either the guard condition is always true or the
  body diverges in some other way), every finite unrolling will yield
  zero expectation regardless of the input expectation f. *)
Lemma wpf_unroll_const_0 c e x i f :
  e x = true ->
  wf_cpGCL c ->
  iid_wpf e c ->
  expectation f ->
  wpf c (indicator e) x == 1 ->
  wpf (unroll e c i) f x == (const 0) i.
Proof.
  revert c e x f; unfold indicator.
  induction i; intros c e x f He Hwf Hiid Hexp Heq; unfold compose, const.
  - simpl; rewrite He; reflexivity.
  - unfold iid_wpf in Hiid.
    rewrite Hiid, IHi; auto.
    unfold const; rewrite Qmult_0_r, Qplus_0_l.
    apply wpf_indicator_1_f_0; auto.
Qed.

(** Similar to [wpf_unroll_const_0] but wlpf yields the constant 1
  expectation because that's how it treats the abort command. *)
Lemma wlpf_unroll_const_1 c e x i f :
  e x = true ->
  wf_cpGCL c ->
  iid_wlpf e c ->
  wpf c (indicator e) x == 1 ->
  wlpf (unroll e c i) f x == (const 1) i.
Proof.
  revert c e x f; unfold indicator.
  induction i; intros c e x f He Hwf Hiid Heq; unfold compose, const.
  - simpl; rewrite He; reflexivity.
  - unfold iid_wlpf in Hiid.
    rewrite Hiid, IHi; auto.
    unfold const; rewrite Qmult_1_r.
    rewrite Heq, wlpf_indicator_1_f_0; auto; reflexivity.
Qed.

(** wpf mapped over the sequence of finite unrollings is an ascending
  chain. *)
Lemma wpf_unroll_chain c e f x :
  wf_cpGCL c ->
  expectation f ->
  chain (fun i => wpf (unroll e c i) f x).
Proof.
  intros Hwf Hexp i; simpl; revert x.
  induction i; intro x; simpl.
  - unfold const, compose.
    destruct (e x).
    + apply wpf_expectation; auto.
      intro y. destruct (e y); auto; lra.
    + lra.
  - destruct (e x); try lra.
    apply wpf_monotone; auto.
Qed.

(** wlpf mapped over the sequence of finite unrollings is a descending
  chain. *)
Lemma wlpf_unroll_dec_chain c e f x :
  wf_cpGCL c ->
  bounded_expectation f 1 ->
  dec_chain (fun i => wlpf (unroll e c i) f x).
Proof.
  intros Hwf Hexp i; simpl; revert x.
  induction i; intro x; simpl.
  - unfold const, compose.
    destruct (e x).
    + apply wlpf_bounded; auto; intro y; destruct (e y); try lra; apply Hexp.
    + lra.
  - destruct (e x); try lra.
    unfold compose in *.
    apply wlpf_monotone; auto.
Qed.

(** wp and wpf coincide when every loop in the program is iid. *)
Lemma wp_wpf (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  expectation f ->
  wp c f (wpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hiid Hexp; simpl;
    inversion Hwf; inversion Hiid; subst;
      try solve [econstructor; auto; reflexivity].
  - unfold compose.
    econstructor; auto.
    apply IHc1; auto.
    apply wpf_expectation; auto.
    reflexivity.
  - set (ch := flip wpf f ∘ unroll e c).
    apply wp_while with (ch := ch).
    + reflexivity.
    + intro n.
      eexists. split.
      * apply IHc; auto.
        unfold ch.
        unfold compose, flip.
        apply wpf_expectation; auto.
        apply wf_unroll; auto.
      * intro x. unfold ch. unfold compose. unfold flip.
        simpl. reflexivity.
    + apply supremum_pointwise; intro x.
      destruct (e x) eqn:He.
      * assert (Hle: wpf c (indicator e) x <= 1).
        { apply wpf_bounded; auto.
          intro y; unfold indicator; destruct (e y); lra. }
        destruct (Qeq_dec (wpf c (indicator e) x) 1).
        ++ unfold indicator in *.
           eapply Proper_supremum_Q.
           rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity.
           intro i. unfold app_chain, flip.
           unfold ch. unfold compose, flip.
           destruct H5; apply wpf_unroll_const_0; auto.
           apply const_supremum.
           intro i; unfold const. apply Qeq_equ; reflexivity.
        ++ apply geometric_supremum.
           ** apply wpf_expectation; auto.
              intro y; destruct (e y); auto; lra.
           ** apply wpf_expectation; auto.
              intro y; destruct (e y); auto; lra.
           ** unfold indicator in *; lra.
           ** intro i; destruct H5; apply wpf_chain_geometric_series; auto.
      * unfold app_chain. unfold flip. unfold ch. unfold compose, flip.
        apply const_supremum'.
        ++ apply wpf_unroll_chain; auto.
        ++ exists (S 0).
           intros n Hle.
           apply Qeq_equ.
           destruct n. lia.
           simpl. rewrite He. reflexivity.
Qed.

(** wlp and wlpf coincide when every loop in the program is iid. *)
Lemma wlp_wlpf (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  bounded_expectation f 1 ->
  wlp c f (wlpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hiid Hexp; simpl;
    inversion Hwf; inversion Hiid; subst; try solve [constructor; reflexivity].
  - unfold compose.
    econstructor; auto.
    apply IHc1; auto.
    apply wlpf_bounded_expectation; auto.
    reflexivity.
  - econstructor; eauto; reflexivity.
  - econstructor; eauto. reflexivity.
  - set (ch := flip wlpf f ∘ unroll e c).
    apply wlp_while with (ch := ch).
    + reflexivity.
    + intro n.
      eexists. split.
      * apply IHc; auto.
        unfold ch.
        unfold compose, flip.
        apply wlpf_bounded_expectation; auto.
        apply wf_unroll; auto.
      * intro x. unfold ch. unfold compose. unfold flip.
        simpl. reflexivity.
    + apply infimum_pointwise; intro x.
      destruct (e x) eqn:He.
      * assert (Hle: wpf c (indicator e) x <= 1).
        { apply wpf_bounded; auto.
          intro y; unfold indicator; destruct (e y); lra. }
        destruct (Qeq_dec (wpf c (indicator e) x) 1).
        ++ unfold indicator in *.
           eapply Proper_infimum_Q.
           rewrite Qeq_eq_bool. reflexivity. auto.
           intro i. unfold app_chain, ch, flip, compose.
           destruct H5; apply wlpf_unroll_const_1; auto.
           apply const_infimum.
           intro; apply Qeq_equ; reflexivity.
        ++ eapply Proper_infimum_Q. rewrite Qeq_bool_false; auto.
           reflexivity. reflexivity.
           apply wlpf_infimum.
           ** apply wlpf_expectation; auto.
              intro y; destruct (Hexp y); destruct (e y); auto; lra.
           ** apply wpf_expectation; auto.
              intro y; destruct (Hexp y); destruct (e y); auto; lra.
           ** unfold indicator in *; lra.
           ** set (a := wlpf c (fun st' : St => if e st' then 0 else f st') x).
              set (b := wpf c (fun st' : St => if e st' then 1 else 0) x).
              assert (H: b == wpf c (fun y => if e y then const 1 y else 0) x).
              { eapply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
              rewrite H; clear H.
              rewrite Qplus_comm; unfold a.
              rewrite <- wlpf_linear'.
              apply wlpf_bounded; auto.
              intro y; destruct (Hexp y); destruct (e y);
                auto; unfold const; lra.
           ** intro i; destruct H5; apply wlpf_chain_series; auto.
      * apply const_infimum'.
        ++ apply wlpf_unroll_dec_chain; auto.
        ++ exists (S O).
           intros n Hle.
           destruct n.
           ** lia.
           ** unfold app_chain, ch, flip, compose; simpl.
              rewrite He; reflexivity.
Qed.

(** cwp and cwpf coincide when every loop in the program is iid. *)
Theorem cwp_cwpf (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  expectation f ->
  cwp c f (cwpf c f).
Proof.
  intros Hwf Hiid Hexp; unfold cwp.
  exists (wpf c f). exists (wlpf c (const 1)); split.
  - split.
    + apply wp_wpf; auto.
    + apply wlp_wlpf; auto.
      intro; unfold const; lra.
  - reflexivity.
Qed.
