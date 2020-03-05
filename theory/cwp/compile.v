(** Compiling commands to trees and some associated lemmas. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import Coq.micromega.Lia.

Require Import cpGCL.
Require Import tree.

Definition freshLabel : state nat nat :=
  bind get (fun l => bind (put (S l)) (fun _ => ret (S l))).

Fixpoint compile (c : cpGCL) : state nat (St -> tree St) :=
  match c with
  | CSkip => ret (@Leaf _)
  | CAbort => bind freshLabel (fun l => ret (fun _ => Fix l (Fail _ l)))
  | CSeq c1 c2 =>
    bind (compile c1) (fun k1 => bind (compile c2) (fun k2 => ret (kcomp k1 k2)))
  | CAssign x e => ret (fun st => Leaf (upd x (e st) st))
  | CIte e c1 c2 =>
    bind (compile c1)
         (fun k1 => bind (compile c2)
                      (fun k2 => ret (fun st => if e st
                                          then k1 st
                                          else k2 st)))
  | CChoice p c1 c2 =>
    bind (compile c1)
         (fun k1 => bind (compile c2)
                      (fun k2 => ret (fun st => Choice p (k1 st) (k2 st))))
  | CWhile e body =>
    (** Generate the bound label before compiling the body so
        the tree is well-formed wrt the ordering the bound labels. *)
    bind freshLabel
         (fun l => bind (compile body)
                     (fun k => ret (fun st => Fix l (bind (k st)
                                                    (fun st' => if e st'
                                                             then Fail _ l
                                                             else Leaf st')))))
  | CObserve e =>
    ret (fun st => if e st then Leaf st else Fail _ O)
  end.

Definition runCompile (c : cpGCL) (n : nat) : (St -> tree St) * nat :=
  runState (compile c) n.

Definition evalCompile (c : cpGCL) (n : nat) : St -> tree St :=
  evalState (compile c) n.

Definition evalCompile' (c : cpGCL) : St -> tree St :=
  evalCompile c O.

Lemma compile_bound_n_m (c : cpGCL) (n m : nat) (k : St -> tree St) :
  runState (compile c) n = (k, m) ->
  (n <= m)%nat.
Proof.
  revert n m k.
  induction c; intros m m' k Hc;
    try solve [inversion Hc; subst; lia]; inversion Hc; subst.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion H0; subst; clear H0.
    etransitivity.
    eapply IHc1; eauto.
    eapply IHc2; eauto.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion H0; subst; clear H0.
    etransitivity.
    eapply IHc1; eauto.
    eapply IHc2; eauto.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion H0; subst; clear H0.
    etransitivity.
    eapply IHc1; eauto.
    eapply IHc2; eauto.
  - destruct (runState (compile c) (S m)) eqn:Hc1.
    inversion H0; subst; clear H0.
    apply IHc in Hc1; lia.
Qed.

Lemma compile_bound_labels (c : cpGCL) (n m : nat) (k : St -> tree St) :
  runState (compile c) n = (k, m) ->
  forall l st, bound_in l (k st) -> n < l <= m.
Proof.
  revert n m k.
  induction c; intros m m' k Hc l st Hbound; simpl in Hc; inversion Hc; subst.
  - inversion Hbound.
  - unfold compose, const in Hbound.
    inversion Hbound; subst. lia. inversion H3.
  - inversion Hbound.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    apply bound_in_bind in Hbound. destruct Hbound.
    + eapply IHc1 in Hc1; eauto.
      apply compile_bound_n_m in Hc2; lia.
    + destruct H. eapply IHc2 in Hc2; eauto.
      apply compile_bound_n_m in Hc1; lia.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    destruct (e st).
    + eapply IHc1 in Hc1; eauto.
      apply compile_bound_n_m in Hc2; lia.
    + eapply IHc2 in Hc2; eauto.
      apply compile_bound_n_m in Hc1; lia.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    inversion Hbound; subst.
    + eapply IHc1 in Hc1; eauto.
      apply compile_bound_n_m in Hc2; lia.
    + eapply IHc2 in Hc2; eauto.
      apply compile_bound_n_m in Hc1; lia.
  - destruct (runState (compile c) (S m)) eqn:Hc1.
    inversion Hc; subst; clear Hc.
    unfold compose in Hbound.
    inversion Hbound; subst.
    + apply compile_bound_n_m in Hc1; lia.
    + apply bound_in_bind' in H4.
      * eapply IHc in Hc1; eauto; lia.
      * intro x; destruct (e x); constructor.
  - inversion Hc; subst; clear Hc.
    destruct (e st); inversion Hbound.
Qed.

Lemma compile_bound_in_0_lt (c : cpGCL) (n n' m : nat) (k : St -> tree St) (x : St) :
  runState (compile c) n = (k, n') ->
  bound_in m (k x) ->
  (0 < m)%nat.
Proof.
  revert n n' m k x.
  induction c; intros n' n'' m k x Hc Hbound; simpl in Hc; inversion Hc; subst.
  - inversion Hbound.
  - inversion Hbound; subst. lia. inversion H3.
  - inversion Hbound.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc H0.
    apply bound_in_bind in Hbound. destruct Hbound.
    + eapply IHc1; eauto.
    + destruct H; eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc H0.
    destruct (e x).
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc H0.
    inversion Hbound; subst.
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c) (S n')) eqn:Hc1.
    inversion Hc; subst; clear Hc H0.
    inversion Hbound; subst. lia.
    apply bound_in_bind' in H3.
    + eapply IHc; eauto.
    + intro y; destruct (e y); constructor; auto.
  - destruct (e x); inversion Hbound.
Qed.

Lemma compile_free_in_0 (c : cpGCL) (n n' m : nat) (k : St -> tree St) (x : St) :
  runState (compile c) n = (k, n') ->
  free_in m (k x) ->
  m = O.
Proof.
  revert n n' m k x.
  induction c; intros n' n'' m k x Hc Hfree; simpl in Hc.
  - inversion Hc; subst. inversion Hfree.
  - inversion Hc; subst. unfold compose, const in Hfree.
    inversion Hfree; subst.
    inversion H3; subst. congruence.
  - inversion Hc; subst. inversion Hfree.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    apply free_in_bind in Hfree.
    destruct Hfree.
    + eapply IHc1; eauto.
    + destruct H; eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    destruct (e x).
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    inversion Hfree; subst.
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c) (S n')) eqn:Hc1.
    inversion Hc; subst; clear Hc.
    inversion Hfree; subst.
    apply free_in_bind' in H3.
    + eapply IHc; eauto.
    + intro y; destruct (e y); constructor; auto.
  - inversion Hc; subst.
    destruct (e x); inversion Hfree; reflexivity.
Qed.

Lemma compile_not_in (c : cpGCL) (n n' m : nat) (k : St -> tree St) :
  runState (compile c) n = (k, n') ->
  (S m <= n)%nat ->
  forall x, not_in (S m) (k x).
Proof.
  intros Hc Hle x.
  apply not_in_not_bound_or_free. intro H.
  destruct H.
  + eapply compile_free_in_0 in H; eauto. lia.
  + eapply compile_bound_labels in H; eauto. lia.
Qed.

Lemma compile_bound_in_not_in (c1 c2 : cpGCL) (n n' m m' : nat) (k1 : St -> tree St) (k2 : St -> tree St) :
  runState (compile c1) n = (k1, n') ->
  runState (compile c2) m = (k2, m') ->
  (n' <= m)%nat ->
  forall n0 x y, bound_in n0 (k1 x) ->
            not_in n0 (k2 y).
Proof.
  revert k1 k2 c2 n n' m m'.
  induction c1; intros k1 k2 c2 n' n'' m m' H0 H1 Hle n0 x y Hbound.
  - inversion H0; subst. inversion Hbound.
  - inversion H0; subst.
    unfold compose, const in Hbound.
    inversion Hbound; subst; clear H0.
    + eapply compile_not_in; eauto.
    + inversion H5.
  - inversion H0; subst. inversion Hbound.
  - inversion H0.
    destruct (runState (compile c1_1) n') eqn:Hc1_1.
    destruct (runState (compile c1_2) n) eqn:Hc1_2.
    inversion H2; subst; clear H2.
    unfold kcomp in Hbound. simpl in Hbound.
    generalize (@compile_bound_labels (c1_1;;c1_2) n' n'' (kcomp t t0) H0 n0 x Hbound).
    intros [Hlt Hle'].
    assert (n0 <= m)%nat. lia.
    destruct n0.
    + eapply compile_bound_in_0_lt in H0; eauto. lia.
    + eapply compile_not_in; eauto.
  - inversion H0; subst.
    destruct (runState (compile c1_1) n') eqn:Hc1_1.
    destruct (runState (compile c1_2) n) eqn:Hc1_2.
    inversion H2; subst; clear H2.
    destruct (e x).
    + eapply IHc1_1; eauto.
      apply compile_bound_n_m in Hc1_2; lia.
    + eapply IHc1_2; eauto.
  - inversion H0; subst.
    destruct (runState (compile c1_1) n') eqn:Hc1_1.
    destruct (runState (compile c1_2) n) eqn:Hc1_2.
    inversion H2; subst; clear H2.
    inversion Hbound; subst.
    + eapply IHc1_1; eauto.
      apply compile_bound_n_m in Hc1_2; lia.
    + eapply IHc1_2; eauto.
  - inversion H0; subst.
    destruct (runState (compile c1) (S n')) eqn:Hc1_1.
    inversion H2; subst; clear H2.
    unfold compose in Hbound.
    inversion Hbound; subst.
    + eapply compile_not_in; eauto.
      apply compile_bound_n_m in Hc1_1; lia.
    + apply bound_in_bind' in H5.
      eapply IHc1; eauto.
      intro z. destruct (e z); constructor; auto.
  - inversion H0; subst.
    destruct (e x); inversion Hbound.
Qed.

Lemma compile_wf' (c : cpGCL) (n : nat) :
  wf_cpGCL c ->
  (forall st, wf_tree' (evalCompile c n st)).
Proof.
  revert n.
  induction c; intros m Hwf st;
    unfold evalCompile, evalState; simpl;
      try solve [repeat constructor].
  - unfold compose, const. constructor. constructor.
    intros x Hbound; inversion Hbound.
    intros x Hfree; inversion Hfree; subst; auto.    
  - inversion Hwf; subst. apply (IHc1 m) with (st:=st) in H1.
    unfold evalCompile, evalState in H1.
    destruct (runState (compile c1) m) eqn:Hc1.
    unfold evalCompile, evalState in IHc2.
    specialize (IHc2 n H2).
    destruct (runState (compile c2) n) eqn:Hc2.
    unfold kcomp. simpl in *.
    apply wf_tree'_bind; auto.
    + intros n1 m0 x Hbound_n1 Hbound_m0.
      eapply compile_bound_labels in Hc2; eauto.
      eapply compile_bound_labels in Hc1; eauto.
      lia.
    + intros n1 m0 x Hbound_n1 free_m0.
      eapply compile_free_in_0 in Hc2; eauto; subst; lia.
  - inversion Hwf; subst.
    specialize (IHc1 m H1).
    unfold evalCompile, evalState in IHc1.
    destruct (runState (compile c1) m).
    specialize (IHc2 n H3).
    unfold evalCompile, evalState in IHc2.
    destruct (runState (compile c2) n).
    simpl in *.
    destruct (e st); auto.
  - inversion Hwf; subst.
    specialize (IHc1 m H3).
    unfold evalCompile, evalState in IHc1.
    destruct (runState (compile c1) m).
    specialize (IHc2 n H4).
    unfold evalCompile, evalState in IHc2.
    destruct (runState (compile c2) n).
    simpl in *.
    constructor; auto.
  - unfold evalCompile, evalState in IHc.
    inversion Hwf; subst.
    specialize (IHc (S m) H0).
    destruct (runState (compile c) (S m)) eqn:Hc.
    simpl in *.
    constructor.
    + apply wf_tree'_bind; auto.
      * intros; destruct (e x); inversion H1.
      * intros. destruct (e x); inversion H1; subst.
        (* This is true because we generate the labels in the correct
           order in the compiler. *)
        eapply compile_bound_labels in Hc; eauto; lia.
      * intro x; destruct (e x); constructor.
    + intros l Hbound.
      apply bound_in_bind in Hbound. destruct Hbound as [Hbound|Hbound].
      eapply compile_bound_labels in Hc; eauto; lia.
      destruct Hbound as [x Hbound]; destruct (e x); inversion Hbound.
    + intros l Hfree.
      apply free_in_bind in Hfree.
      destruct Hfree as [Hfree|Hfree].
      * eapply compile_free_in_0 in Hc; eauto; lia.
      * destruct Hfree as [x Hfree].
        destruct (e x); inversion Hfree; subst; lia.
  - destruct (e st); constructor.
Qed.

Lemma compile_wf (c : cpGCL) (n : nat) :
  wf_cpGCL c ->
  (forall st, wf_tree (evalCompile c n st)).
Proof. intros; apply wf_tree'_wf_tree, compile_wf'; auto. Qed.

(* Lemma afsddd e c m : *)
(*   exists l, forall st, exists t, evalCompile (CWhile e c) m st = Fix l t. *)
(* Proof. *)
(*   unfold evalCompile. simpl. unfold evalState. simpl. *)
(*   destruct (runState (compile c) (S m)). simpl. *)
(*   eexists. intro. eexists. reflexivity. *)
(* Qed. *)

Lemma compile_wf_tree' c m n k st :
  wf_cpGCL c ->
  runState (compile c) m = (k, n) ->
  wf_tree' (k st).
Proof.
  intros Hwf Hc; generalize (compile_wf' m Hwf st).
  unfold evalCompile, evalState; rewrite Hc; auto.
Qed.
