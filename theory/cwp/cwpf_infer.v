(** Compilation+inference agrees with functional CWP (always). *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Data.Monads.StateMonad.
Local Open Scope program_scope.

Require Import compile.
Require Import cpGCL.
Require Import cwp.
Require Import infer.
Require Import order.
Require Import Q.
Require Import tree.

(** wpf and unnormalized inference after compilation coincide when c
  is well-formed. *)
Theorem wpf_infer_f c f n :
  wf_cpGCL c ->
  wpf c f ==f infer_f f ∘ evalCompile c n.
Proof.
  revert n f.
  induction c; intros m f Hwf st;
    unfold evalCompile, evalState, compose; simpl; inversion Hwf; subst.
  - reflexivity.
  - rewrite Qdiv_0_num; reflexivity.
  - reflexivity.
  - unfold compose.
    unfold compose, f_Qeq, evalCompile, evalState in *.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    specialize (IHc1 m (wpf c2 f) H1 st).
    rewrite IHc1. simpl.
    rewrite Hc1. simpl.
    unfold kcomp. simpl.
    rewrite <- infer_f_bind. unfold compose. simpl.
    + apply infer_f_proper; intro x.
      specialize (IHc2 n f H2 x).
      rewrite IHc2, Hc2; reflexivity.
    + intros l x Hbound. apply not_in_not_bound_and_not_free. split.
      * apply free_in_not_free_in; intro HC.
        eapply compile_free_in_0 in Hc2; eauto. subst.
        eapply compile_bound_labels in Hc1; eauto; lia.
      * apply bound_in_not_bound_in; intro HC.
        eapply compile_bound_labels in Hc2; eauto.
        eapply compile_bound_labels in Hc1; eauto.
        lia.
  - unfold compose, evalCompile, evalState, f_Qeq in *.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    simpl; destruct (e st).
    + rewrite IHc1, Hc1; auto; reflexivity.
    + rewrite IHc2, Hc2; auto; reflexivity.
  - unfold compose, evalCompile, evalState, f_Qeq in *.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    rewrite IHc1, Hc1, IHc2, Hc2; auto; reflexivity.
  - destruct (runState (compile c) (S m)) eqn:Hc.
    pose proof IHc as IHc'.
    specialize (IHc (S m) f H0 st).
    unfold compose, evalCompile, evalState, f_Qeq in *.
    rewrite Hc in IHc. simpl in *.
    set (g := fun st' => if e st' then 0 else f st').
    set (h := fun st' => if e st' then 1 else 0).
    set (k := fun st' => if e st' then Fail St (S m) else Leaf st').
    destruct (e st).
    + cut (wpf c g st == infer_f f (tree_bind (t st) k)).
      cut (wpf c h st == infer_fail (S m) (tree_bind (t st) k)).
      { intros H1 H2; rewrite H1, H2; reflexivity. }
      * unfold h. unfold k.
        rewrite infer_fail_tree_bind_infer_f.
        specialize (IHc' (S m) (fun st => if e st then 1 else 0) H0 st).
        rewrite Hc in IHc'. simpl in IHc'.
        apply IHc'.
        apply label_in_not_in; intro HC. apply label_in_bound_or_free in HC.
        destruct HC as [HC|HC].
        ++ eapply compile_bound_labels in Hc; eauto; lia.
        ++ eapply compile_free_in_0 in Hc; eauto; lia.
        ++ eapply compile_wf_tree; eauto.
      * specialize (IHc' (S m) g H0 st).
        rewrite IHc'. rewrite Hc. simpl.
        unfold g. unfold k.
        rewrite infer_f_bind_fail.
        ++ reflexivity.
        ++ apply bound_in_not_bound_in; intro HC.
           eapply compile_bound_labels in Hc; eauto; lia.
    + reflexivity.
  - destruct (e st); reflexivity.
Qed.

(** wlpf and unnormalized liberal inference after compilation coincide
  when c is well-formed. *)
Theorem wlpf_infer_f_lib c f n :
  wf_cpGCL c ->
  wlpf c f ==f infer_f_lib f ∘ evalCompile c n.
Proof.
  revert n f.
  induction c; intros m f Hwf st;
    unfold evalCompile, evalState, compose; simpl; inversion Hwf; subst.
  - reflexivity.
  - rewrite Nat.eqb_refl; reflexivity.
  - reflexivity.
  - unfold compose.
    unfold compose, f_Qeq, evalCompile, evalState in *.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    specialize (IHc1 m (wlpf c2 f) H1 st).
    rewrite IHc1. simpl.
    rewrite Hc1. simpl.
    unfold kcomp. simpl.
    rewrite <- infer_f_lib_bind. unfold compose. simpl.
    + apply infer_f_lib_proper; intro x.
      specialize (IHc2 n f H2 x).
      rewrite IHc2, Hc2; reflexivity.
    + intros l x Hbound. apply not_in_not_bound_and_not_free. split.
      * apply free_in_not_free_in; intro HC.
        eapply compile_free_in_0 in Hc2; eauto. subst.
        eapply compile_bound_labels in Hc1; eauto; lia.
      * apply bound_in_not_bound_in; intro HC.
        eapply compile_bound_labels in Hc2; eauto.
        eapply compile_bound_labels in Hc1; eauto.
        lia.
  - unfold compose, evalCompile, evalState, f_Qeq in *.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    simpl; destruct (e st).
    + rewrite IHc1, Hc1; auto; reflexivity.
    + rewrite IHc2, Hc2; auto; reflexivity.
  - unfold compose, evalCompile, evalState, f_Qeq in *.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    rewrite IHc1, Hc1, IHc2, Hc2; auto; reflexivity.
  - destruct (runState (compile c) (S m)) eqn:Hc.
    pose proof IHc as IHc'.
    specialize (IHc (S m) f H0 st).
    unfold compose, evalCompile, evalState, f_Qeq in *.
    rewrite Hc in IHc. simpl in *.
    set (g := fun st' => if e st' then 0 else f st').
    set (h := fun st' => if e st' then 1 else 0).
    set (k := fun st' => if e st' then Fail St (S m) else Leaf st').
    destruct (e st).
    + cut (wlpf c g st == infer_f_lib f (tree_bind (t st) k)).
      cut (wpf c h st == infer_fail (S m) (tree_bind (t st) k)).
      { intros H1 H2. rewrite H1; simpl.
        destruct (Qeq_dec (infer_fail (S m) (tree_bind (t st) k)) 1).
        { rewrite Qeq_eq_bool; auto; reflexivity. }
        rewrite Qeq_bool_false; auto.
        rewrite H1, H2. reflexivity. }
      * unfold h. unfold k.
        rewrite infer_fail_tree_bind_infer_f.
        specialize (IHc' (S m) (fun st => if e st then 1 else 0) H0 st).
        rewrite Hc in IHc'. simpl in IHc'.
        generalize (@wpf_infer_f c (indicator e) (S m) H0 st).
        unfold compose, evalCompile, evalState; rewrite Hc; auto.
        apply label_in_not_in; intro HC. apply label_in_bound_or_free in HC.
        destruct HC as [HC|HC].
        ++ eapply compile_bound_labels in Hc; eauto; lia.
        ++ eapply compile_free_in_0 in Hc; eauto; lia.
        ++ eapply compile_wf_tree; eauto.
      * specialize (IHc' (S m) g H0 st).
        rewrite IHc'. rewrite Hc. simpl.
        unfold g. unfold k.
        rewrite infer_f_lib_bind_fail.
        ++ reflexivity.
        ++ apply bound_in_not_bound_in; intro HC.
           eapply compile_bound_labels in Hc; eauto; lia.
    + reflexivity.
  - destruct (e st); reflexivity.
Qed.

(** cwpf and normalized inference after compilation coincide when c is
    well-formed. *)
Theorem cwpf_infer c f n :
  wf_cpGCL c ->
  cwpf c f ==f infer f ∘ evalCompile c n.
Proof.
  intros Hwf x.
  unfold cwpf, infer, compose; simpl.
  apply Qeq_Qdiv.
  - apply wpf_infer_f; auto.
  - apply wlpf_infer_f_lib; auto.
Qed.
