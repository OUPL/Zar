Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Data.Monads.StateMonad.
Local Open Scope program_scope.

Require Import compile.
Require Import cpGCL.
Require Import cwp.
Require Import infer.
Require Import order.
Require Import tree.

Theorem wp_infer (c : cpGCL) (f : St -> Q) (n : nat) :
  wf_cpGCL c ->
  expectation f ->
  wp c f (infer_f f ∘ evalCompile c n).
Proof.
  revert f n. induction c; intros f m Hwf Hexp; try solve [constructor; intros ?; reflexivity].
  (* sequence *)
  - unfold compose. unfold evalCompile, evalState in *. simpl.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hwf; subst.
    econstructor. apply IHc2 with (n:=n); auto.
    apply IHc1 with (n:=m); auto. intro x.
    apply infer_f_expectation_0_le; auto. apply compile_wf; auto.
    intro x. unfold compose. simpl.
    rewrite Hc1. rewrite Hc2.
    unfold kcomp. simpl. rewrite <- infer_f_bind. reflexivity.
    intros n1 x0 Hbound. eapply compile_bound_in_not_in.
    apply Hc1. apply Hc2. omega. apply Hbound.
  (* ite *)
  - unfold compose; simpl.
    set (fi := infer_f f).
    inversion Hwf; subst.
    unfold evalCompile, evalState in *. simpl.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2. simpl.
    econstructor. apply IHc1 with (n:=m); auto.
    apply IHc2 with (n:=n); auto.
    intro x. destruct (e x).
    rewrite Hc1; reflexivity.
    rewrite Hc2; reflexivity.
  (* choice *)
  - unfold compose, evalCompile, evalState in *; simpl.
    inversion Hwf; subst.
    specialize (IHc1 f m H3 Hexp).
    destruct (runState (compile c1) m) eqn:Hc1.
    specialize (IHc2 f n H4 Hexp).
    destruct (runState (compile c2) n) eqn:Hc2. simpl in *.
    econstructor.
    apply IHc1.
    apply IHc2.
    reflexivity.
  (* while *)
  -
    (* Need to provide a chain of approximations that satisfies the
       conditions of the while wp constructor, and such that infer
       after compile yields of the supremum of that chain (probably
       via an argument based on convergence of geometric series). *)
    simpl. unfold compose. simpl.
    unfold evalCompile, evalState.
    simpl. destruct (runState (compile c) (S m)) eqn:Hc. simpl.
    rename t into k.
    set (k' := fun st => tree_bind (k st) (fun st' => if e st' then Fail _ (S m) else Leaf st')).
    set (ch := fun i => fun st => infer_f f (tree_chain (k' st ) (S m) i)).
    set (ch' := cons_chain (const 0) ch).
    apply wp_while with ch'.
    + reflexivity.
    + admit. (* TODO: prove chain is ω-invariant *)
    + unfold ch'. apply cons_chain_supremum.
      * unfold ch.
        intros i st; unfold const; simpl.
        apply infer_f_expectation_0_le; auto.
        apply tree_chain_wf. unfold k'.
        apply compile_wf with (n:=m) (st:=st) in Hwf.
        unfold evalCompile, evalState in Hwf. simpl in Hwf.
        unfold k'. (* unfold k. *)
        apply wf_tree_bind; auto.
        ++ intros. apply bound_in_not_bound_in; intro HC.
           destruct (e x); inversion HC.
        ++ rewrite Hc in Hwf. simpl in Hwf.
           inversion Hwf; subst; eapply wf_tree_bind'; eauto.
        ++ intros; destruct (e x); constructor.
      * unfold ch.
        unfold k'.
        apply infer_f_supremum_expectation; auto.
        { intro st.
          apply wf_tree'_bind.
          - intros ? ? ? ? HC; destruct (e x); inversion HC.
          - intros n0 m0 x Hbound Hfree.
            destruct (e x); inversion Hfree; subst.
            eapply compile_bound_labels in Hc; eauto; lia.
          - inversion Hwf; subst.
            apply compile_wf_tree' with (c:=c) (m:=S m) (n:=n); auto.
          - intros; destruct (e x); constructor. }
        { intros st l Hbound.
          apply bound_in_bind in Hbound. destruct Hbound as [Hbound|[x HC]].
          - eapply compile_bound_labels in Hc; eauto; lia.
          - destruct (e x); inversion HC. }
        { intros st n0 m0 Hbound Hfree.
          apply bound_in_bind in Hbound. destruct Hbound as [Hbound | [x HC]].
          - apply free_in_bind in Hfree. destruct Hfree as [Hfree | [x Hfree]].
            * pose proof Hc as Hc'.
              eapply compile_bound_labels in Hc; eauto.
              eapply compile_free_in_0 in Hc'; eauto; subst.
              lia.
            * destruct (e x); inversion Hfree; subst.
              eapply compile_bound_labels in Hc; eauto; lia.
          - destruct (e x); inversion HC. }
  (* observe *)
  - unfold compose, evalCompile, evalState; simpl.
    constructor. intro x. destruct (e x); reflexivity.
Admitted.

Theorem wlp_infer (c : cpGCL) (f : St -> Q) (n : nat) :
  wf_cpGCL c ->
  expectation f ->
  wlp c f (infer_f_lib f ∘ evalCompile c n).
Admitted.

Theorem cwp_infer (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  expectation f ->
  cwp c f (infer f ∘ evalCompile' c).
Proof.
  intros Hwf Hexp.
  eexists; eexists; split.
  - split.
    + apply wp_infer with (n:=O); auto.
    + apply wlp_infer with (n:=O); auto.
      compute; congruence.
  - reflexivity.
Qed.

Lemma wp_iid_infer_f c f n :
  wf_cpGCL c ->
  wp_iid c f ==f infer_f f ∘ evalCompile c n.
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
    specialize (IHc1 m (wp_iid c2 f) H1 st).
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
    cut (wp_iid c g st == infer_f f (tree_bind (t st) k)).
    cut (wp_iid c h st == infer_fail (S m) (tree_bind (t st) k)).
    { intros H1 H2; rewrite H1, H2; reflexivity. }
    + unfold h. unfold k.
      rewrite infer_fail_tree_bind_infer_f.
      specialize (IHc' (S m) (fun st => if e st then 1 else 0) H0 st).
      rewrite Hc in IHc'. simpl in IHc'.
      apply IHc'.
      apply label_in_not_in; intro HC. apply label_in_bound_or_free in HC.
      destruct HC as [HC|HC].
      * eapply compile_bound_labels in Hc; eauto; lia.
      * eapply compile_free_in_0 in Hc; eauto; lia.
      * eapply compile_wf_tree'; eauto.
    + specialize (IHc' (S m) g H0 st).
      rewrite IHc'. rewrite Hc. simpl.
      unfold g. unfold k.
      rewrite infer_f_tree_bind.
      * reflexivity.
      * apply bound_in_not_bound_in; intro HC.
        eapply compile_bound_labels in Hc; eauto; lia.
  - destruct (e st); reflexivity.
Qed.
