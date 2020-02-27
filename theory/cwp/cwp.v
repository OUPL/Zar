Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Local Open Scope program_scope.
Import ListNotations.

Require Import cpGCL.
Require Import geometric.
Require Import order.
Require Import Q.

Open Scope cpGCL_scope.
Open Scope Q_scope.


(** Relational specification of weakest pre-expectation semantics *)
Inductive wp : cpGCL -> (St -> Q) -> (St -> Q) -> Prop :=
| wp_skip : forall f g, f ==f g -> wp CSkip f g
| wp_abort : forall f g, g ==f const 0 -> wp CAbort f g
| wp_assign : forall x e f f',
    f' ==f (fun st => f (upd x (e st) st)) ->
    wp (CAssign x e) f f'
| wp_seq : forall c1 c2 f f' g g',
    wp c2 f g ->
    wp c1 g g' ->
    f' ==f g' ->
    wp (CSeq c1 c2) f f'
| wp_ite : forall e c1 c2 f f' g h,
    wp c1 f g ->
    wp c2 f h ->
    f' ==f (fun st => if e st : bool then g st else h st) ->
    wp (CIte e c1 c2) f f'
| wp_choice : forall p c1 c2 f f' g h,
    wp c1 f g ->
    wp c2 f h ->
    f' ==f (fun st => p * g st + (1-p) * h st) ->
    wp (CChoice p c1 c2) f f'
| wp_while : forall e body f f' ch,
    ch O = const 0 ->
    (forall n, exists g, wp body (ch n) g /\
               ch (S n) = fun st => if e st : bool then g st else f st) ->
    supremum f' ch ->
    wp (CWhile e body) f f'
| wp_observe : forall e f f',
    f' ==f (fun st => if e st : bool then f st else 0) ->
    wp (CObserve e) f f'.


(** Relational specification of weakest liberal pre-expectation
    semantics *)
Inductive wlp : cpGCL -> (St -> Q) -> (St -> Q) -> Prop :=
| wlp_skip : forall f, wlp CSkip f f
| wlp_abort : forall f, wlp CAbort f (const 1)
| wlp_assign : forall x e f,
    wlp (CAssign x e) f (fun st => f (upd x (e st) st))
| wlp_seq : forall c1 c2 f f' f'',
    wlp c2 f f' ->
    wlp c1 f' f'' ->
    wlp (CSeq c1 c2) f f''
| wlp_ite : forall e c1 c2 f g h,
    wlp c1 f g ->
    wlp c2 f h ->
    wlp (CIte e c1 c2) f (fun st => if e st then g st else h st)
| wlp_choice : forall p c1 c2 f f' g h,
    wlp c1 f g ->
    wlp c2 f h ->
    f' ==f (fun st => p * g st + (1-p) * h st) ->
    wlp (CChoice p c1 c2) f f'
| wlp_while : forall e body f f' ch,
    ch O = const 1 ->
    (forall n, exists g, wlp body (ch n) g /\
               ch (S n) ==f fun st => if e st : bool then g st else f st) ->
    infimum f' ch ->
    wlp (CWhile e body) f f'
| wlp_observe : forall e f,
    wlp (CObserve e) f (fun st => if e st then f st else 0).

(** cwp_ is decomposed into wp and wlp *)
Definition cwp_ (c : cpGCL) (f f' g g' : St -> Q) :=
  wp c f f' /\ wlp c g g'.

(** cwp is the ratio of the pair given by cwp_ *)
Definition cwp (c : cpGCL) (f f'' : St -> Q) :=
  exists f' g', cwp_ c f f' (const 1) g' /\ f'' ==f fun st => f' st / g' st.


(** Functional specification of weakest pre-expectation semantics
    (only valid for iid programs). *)
Fixpoint wp_iid (c : cpGCL) (f : St -> Q) : (St -> Q) :=
  match c with
  | CSkip => f
  | CAbort => const 0
  | CAssign x e => fun st => f (upd x (e st) st)
  | CSeq c1 c2 => (wp_iid c1 ∘ wp_iid c2) f
  | CIte e c1 c2 => fun st => if e st then wp_iid c1 f st else wp_iid c2 f st
  | CChoice p c1 c2 => fun st => p * wp_iid c1 f st + (1-p) * wp_iid c2 f st
  | CWhile e body =>
    fun st =>
      wp_iid body (fun st' => if e st' then 0 else f st') st /
             (1 - wp_iid body (fun st' => if e st' then 1 else 0) st)
  | CObserve e => fun st => if e st then f st else 0
  end.

(** Functional specification of weakest liberal pre-expectation
    semantics (only valid for iid programs). *)
Fixpoint wlp_iid (c : cpGCL) (f : St -> Q) : (St -> Q) :=
  match c with
  | CSkip => f
  | CAbort => const 1
  | CAssign x e => fun st => f (upd x (e st) st)
  | CSeq c1 c2 => (wlp_iid c1 ∘ wlp_iid c2) f
  | CIte e c1 c2 => fun st => if e st then wlp_iid c1 f st else wlp_iid c2 f st
  | CChoice p c1 c2 => fun st => p * wlp_iid c1 f st + (1-p) * wlp_iid c2 f st
  | CWhile e body =>
    fun st =>
      wlp_iid body (fun st' => if e st' then 0 else f st') st /
             (1 - wp_iid body (fun st' => if e st' then 1 else 0) st)
  | CObserve e => fun st => if e st then f st else 0
  end.

(** Functional specification of conditional weakest pre-expectation
    semantics (only valid for iid programs). *)
Definition cwp_iid (c : cpGCL) (f : St -> Q) : St -> Q :=
  fun st => wp_iid c f st / wlp_iid c (const 1) st.

(* Lemma wp_proper (c : cpGCL) (f g g': St -> Q) : *)
(*   wp c f g -> *)
(*   g ==f g' -> *)
(*   wp c f g'. *)
(* Proof. *)
(*   induction c; intros H0 H1; inversion H0; subst; clear H0. *)
(*   - constructor; auto; eapply f_Qeq_trans; eauto. *)
(*   - constructor; auto; eapply f_Qeq_trans; eauto; apply f_Qeq_symm; auto. *)
(*   - constructor; intro x; rewrite <- H1, H5; reflexivity. *)
(*   - eapply wp_seq; eauto; eapply f_Qeq_trans; eauto; apply f_Qeq_symm; auto. *)
(*   - econstructor; eauto; intro x; rewrite <- H1, H8; reflexivity. *)
(*   - econstructor; eauto; intro x; rewrite <- H1, H8; reflexivity. *)
(*   - econstructor; eauto; eapply equ_supremum; eauto; apply f_Qeq_equ; auto. *)
(*   - constructor; intro x; rewrite <- H1, H2; reflexivity. *)
(* Qed. *)

(* Theorem wp_infer (c : cpGCL) (f : St -> Q) (n : nat) : *)
(*   wf_cpGCL c -> *)
(*   expectation f -> *)
(*   wp c f (infer_f f ∘ evalCompile c n). *)
(* Proof. *)
(*   revert f n. induction c; intros f m Hwf Hexp; try solve [constructor; intros ?; reflexivity]. *)
(*   (* sequence *) *)
(*   - unfold compose. unfold evalCompile, evalState in *. simpl. *)
(*     destruct (runState (compile c1) m) eqn:Hc1. *)
(*     destruct (runState (compile c2) n) eqn:Hc2. *)
(*     inversion Hwf; subst. *)

(*     econstructor. apply IHc2 with (n:=n); auto. *)
(*     apply IHc1 with (n:=m); auto. intro x. *)
(*     apply infer_f_expectation_0_le; auto. apply compile_wf; auto. *)
(*     intro x. unfold compose. simpl. *)
(*     rewrite Hc1. rewrite Hc2. *)
(*     unfold kcomp. simpl. rewrite <- infer_f_bind. reflexivity. *)
(*     intros n1 x0 Hbound. eapply compile_bound_in_not_in. *)
(*     apply Hc1. apply Hc2. omega. apply Hbound. *)

(*   (* ite *) *)
(*   - unfold compose; simpl. *)
(*     set (fi := infer_f f). *)
(*     inversion Hwf; subst. *)
(*     unfold evalCompile, evalState in *. simpl. *)
(*     destruct (runState (compile c1) m) eqn:Hc1. *)
(*     destruct (runState (compile c2) n) eqn:Hc2. simpl. *)
(*     econstructor. apply IHc1 with (n:=m); auto. *)
(*     apply IHc2 with (n:=n); auto. *)
(*     intro x. destruct (e x). *)
(*     rewrite Hc1; reflexivity. *)
(*     rewrite Hc2; reflexivity. *)

(*   (* choice *) *)
(*   - unfold compose, evalCompile, evalState in *; simpl. *)
(*     inversion Hwf; subst. *)
(*     specialize (IHc1 f m H3 Hexp). *)
(*     destruct (runState (compile c1) m) eqn:Hc1. *)
(*     specialize (IHc2 f n H4 Hexp). *)
(*     destruct (runState (compile c2) n) eqn:Hc2. simpl in *. *)
(*     econstructor. *)
(*     apply IHc1. *)
(*     apply IHc2. *)
(*     reflexivity. *)

(*   (* while *) *)
(*   - *)
(*     (* Need to provide a chain of approximations that satisfies the *)
(*        conditions of the while wp constructor, and such that infer *)
(*        after compile yields of the supremum of that chain (probably *)
(*        via an argument based on convergence of geometric series). *) *)

(*     (* set (ch := *) *)
    
(*     simpl. unfold compose. simpl. *)
(*     (* econstructor. *) *)

(*     admit. *)

(*   (* observe *) *)
(*   - unfold compose, evalCompile, evalState; simpl. *)
(*     constructor. intro x. destruct (e x); reflexivity. *)
(* Admitted. *)


(** Using CWP on example programs *)

Ltac rewrite_equiv :=
  match goal with
  | [ H : forall _ : St, _ == _ |- _ ] => rewrite H; simpl
  | [ H : _ ==f _ |- _ ] => unfold f_Qeq in H; rewrite H; simpl
  end.

Ltac wp_inversion :=
  match goal with
  | [ H : wp ?c ?f ?f' |- _ ] => inversion H; subst; clear H
  end;
  repeat rewrite_equiv.

Ltac wlp_inversion :=
  match goal with
  | [ H : wlp ?c ?f ?f' |- _ ] => inversion H; subst; clear H
  end;
  repeat rewrite_equiv.

(* Lemma goldfish_piranha_cwp (f : St -> Q) : *)
(*   cwp goldfish_piranha (fun st => if st O then 1 else 0) f -> f ==f const (2#3). *)
(* Proof. *)
(*   intros (f' & g' & [Hwp Hwlp] & Hf) x. *)
(*   repeat wp_inversion; repeat wlp_inversion; reflexivity. *)
(* Qed. *)

(* Lemma fair_coin_cwp (f : St -> Q) : *)
(*   cwp fair_coin (fun st => if st O then 1 else 0) f -> f ==f const (1#2). *)
(* Proof. *)
(*   unfold fair_coin. *)
(*   unfold cwp. *)
(*   intros (f' & g' & [Hwp Hwlp] & Hf). *)
(*   set (fx := fun st : St => if st O : bool then 1 else 0). *)
(*   repeat wp_inversion. *)
(*   repeat wlp_inversion. *)
(*   intro x. rewrite Hf. unfold const. *)
(*   assert (forall i, ch0 i ==f const 1). *)
(*   { clear Hf H5 H6 H8 H1 H3 H7 H10 H13 f f' f'1 ch x g g'0 g0 g'1. *)
(*     intro i. induction i. *)
(*     - intro x; rewrite H2; reflexivity. *)
(*     - specialize (H9 i). *)
(*       destruct H9 as (g & Hwlp & H). *)
(*       repeat wlp_inversion. *)
(*       unfold const in *. *)
(*       intro st. *)
(*       assert (H9' := H9). *)
(*       specialize (H9 (upd O true st)). *)
(*       specialize (H9' (upd O false st)). *)
(*       specialize (H10 st). *)
(*       rewrite 2!IHi in H9. *)
(*       rewrite 2!IHi in H9'. *)
(*       rewrite H9 in H10. *)
(*       rewrite H9' in H10. *)
(*       rewrite H. *)
(*       destruct (eqb (st O) (st (S O))); try reflexivity. *)
(*       rewrite H10. field. } *)
(*   assert (infimum (const 1) ch0). *)
(*   { apply const_infimum; intro i; apply f_Qeq_equ; auto. } *)
(*   assert (Hf'1: f'1 ==f const 1). *)
(*   { apply f_Qeq_equ; eapply infimum_unique; eauto. } *)
(*   rewrite Hf'1. *)
(*   assert (supremum (fun st => if eqb (st O) (st (S O)) then 1#2 else fx st) ch). *)
(*   { *)
(*     split. *)
(*     - intros i st. unfold const; simpl. *)
(*       clear Hf. clear H6. clear H2. clear H5. clear H9. *)
(*       clear x. clear H0. clear Hf'1. clear H. clear H13. clear H8 g. *)
(*       clear ch0. revert st. *)
(*       induction i; intro st. *)
(*       + rewrite H1. unfold const, fx. *)
(*         destruct (st O); destruct (st (S O)); simpl; compute; congruence. *)
(*       + specialize (H3 i). *)
(*         destruct H3 as (g & Hwp & H). *)
(*         repeat wp_inversion. *)
(*         unfold const in H. *)
(*         rewrite H. *)
(*         assert (Hi0 := IHi (upd 1 true (upd 0 true st))). *)
(*         assert (Hi1 := IHi (upd 1 false (upd 0 true st))). *)
(*         assert (Hi2 := IHi (upd 1 true (upd 0 false st))). *)
(*         assert (Hi3 := IHi (upd 1 false (upd 0 false st))). *)
(*         unfold fx in *. simpl in *. *)
(*         destruct (st O) eqn:Hx; destruct (st (S O)) eqn:Hy; simpl in *; try lra; *)
(*         repeat rewrite_equiv; unfold const; lra. *)
(*     - intros ub Hub st. *)
(*       unfold upper_bound in Hub. *)
(*       simpl in *. *)
(*       unfold fx. *)
(*       assert (forall i, ch (S (S i)) ==f fun st => if eqb (st O) (st (S O)) *)
(*                                            then geometric_series (2#9) (5#9) i *)
(*                                            else fx st). *)
(*       { clear Hf. clear H6. clear H2. clear H5. clear H9. *)
(*         clear x. clear H0. clear Hf'1. clear H. *)
(*         clear H13 ch0. revert st. *)
(*         clear Hub ub. clear H8 g. *)
(*         induction i; intro x. *)
(*         - simpl. *)
(*           assert (Hch1 := H3 O). *)
(*           specialize (H3 (S O)). *)
(*           destruct H3 as (g & Hwp & H3). *)
(*           rewrite H3. *)
(*           simpl. *)
(*           repeat wp_inversion. *)
(*           destruct Hch1 as (? & Hwp & Hch1). *)
(*           repeat wp_inversion. *)
(*           unfold const in *. *)
(*           unfold fx. *)
(*           destruct (x O); destruct (x (S O)); simpl; try reflexivity; *)
(*             repeat rewrite_equiv; rewrite Hch1; simpl; *)
(*               repeat rewrite_equiv; rewrite H1; reflexivity. *)
(*         - set (geom := geometric_series (2#9) (5#9) (S i)). *)
(*           simpl. *)
(*           destruct (H3 (S (S i))) as (g & Hwp & Hch). *)
(*           repeat wp_inversion. *)
(*           rewrite Hch. unfold const. *)
(*           clear Hch. *)
(*           unfold fx in *. *)
(*           destruct (x O); destruct (x (S O)); simpl; *)
(*             try rewrite 4!IHi; simpl; try reflexivity; *)
(*               unfold geom; rewrite <- geometric_series_fact; *)
(*                 rewrite H8; repeat rewrite_equiv; field. } *)
(*       assert (Hle0: 0 <= 2#9 <= 1). lra. *)
(*       assert (Hle1: 0 <= 5#9). lra. *)
(*       assert (Hlt: 5#9 < 1). lra. *)
(*       destruct (st O) eqn:Hx; destruct (st (S O)) eqn:Hy; simpl. *)
(*       + assert (forall eps, 0 < eps -> exists n0, (1#2) - ch n0 st < eps). *)
(*         { intros eps Heps. *)
(*           generalize (@geometric_series_converges _ _ _ Hle0 Hle1 Hlt Heps). *)
(*           intros [n0 Hgeom]. *)
(*           exists (S (S n0)). *)
(*           rewrite H4. *)
(*           rewrite Hx. rewrite Hy. simpl. *)
(*           specialize (Hgeom n0 (Nat.le_refl _)). *)
(*           assert (H': (2#9) / (1 - (5#9)) == 1#2). *)
(*           { reflexivity. } *)
(*           rewrite <- H'. apply Hgeom. } *)
(*         destruct (Qlt_le_dec (ub st) (1#2)); auto. *)
(*         * assert (H': 0 < (1#2) - ub st). *)
(*           { lra. } *)
(*           specialize (H11 ((1#2) - ub st) H'). *)
(*           destruct H11 as [n0 H11]. *)
(*           assert (ub st < ch n0 st). *)
(*           { lra. } *)
(*           specialize (Hub n0 st); lra. *)
(*       + specialize (Hub (S O) st). *)
(*         specialize (H3 O). clear H6 H8 g. *)
(*         destruct H3 as (g & Hwp & H3). *)
(*         rewrite H3 in Hub. *)
(*         rewrite Hx in Hub. *)
(*         rewrite Hy in Hub. *)
(*         apply Hub. *)
(*       + specialize (Hub O st). rewrite H1 in Hub. apply Hub. *)
(*       + assert (forall eps, 0 < eps -> exists n0, (1#2) - ch n0 st < eps). *)
(*         { intros eps Heps. *)
(*           generalize (@geometric_series_converges _ _ _ Hle0 Hle1 Hlt Heps). *)
(*           intros [n0 Hgeom]. *)
(*           exists (S (S n0)). *)
(*           rewrite H4. *)
(*           rewrite Hx. rewrite Hy. simpl. *)
(*           specialize (Hgeom n0 (Nat.le_refl _)). *)
(*           assert (H': (2#9) / (1 - (5#9)) == 1#2). *)
(*           { reflexivity. } *)
(*           rewrite <- H'. apply Hgeom. } *)
(*         destruct (Qlt_le_dec (ub st) (1#2)); auto. *)
(*         * assert (H': 0 < (1#2) - ub st). *)
(*           { lra. } *)
(*           specialize (H11 ((1#2) - ub st) H'). *)
(*           destruct H11 as [n0 H11]. *)
(*           assert (ub st < ch n0 st). *)
(*           { lra. } *)
(*           specialize (Hub n0 st). *)
(*           lra. } *)
(*   rewrite H5. repeat rewrite_equiv. unfold const. *)
(*   assert (Hg0 : g0 ==f fun st => if eqb (st O) (st (S O)) then 1#2 else fx st). *)
(*   { apply f_Qeq_equ; eapply supremum_unique; eauto. } *)
(*   rewrite Hg0; reflexivity. *)
(* Qed. *)

Lemma wp_iid_bounded c f :
  wf_cpGCL c ->
  (forall x, f x <= 1) ->
  forall x, wp_iid c f x <= 1.
Proof.
  revert f.
  induction c; intros f Hwf Hbounded x; simpl; inversion Hwf; subst; auto.
  - unfold const; lra.
  - apply IHc1; auto.
  - destruct (e x); auto.
  - specialize (IHc1 f H3 Hbounded x).
    specialize (IHc2 f H4 Hbounded x).
    nra.
  - admit.
    (* destruct (Qeq_dec (wp_iid c (fun st => if e st then 1 else 0) x) 1). *)
    (* + rewrite q, Qminus_cancel, Qdiv_0_den; lra. *)
    (* + assert (wp_iid c (fun st => if e st then 1 else 0) x <= 1). *)
    (*   { apply IHc; auto; intro st; destruct (e st); auto; lra. } *)
    (*   apply Qle_shift_div_r. lra.       *)
    (*   cut (wp_iid c (fun st => if e st then 1 else 0) x < 1). *)
    (*   { intros; lra. } *)
    (*   nra. *)
Admitted.

Lemma wp_iid_expectation c f :
  wf_cpGCL c ->
  expectation f ->
  expectation (wp_iid c f).
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
    assert (wp_iid c (fun st => if e st then 1 else 0) x <= 1).
    { apply wp_iid_bounded; auto.
      intro st; destruct (e st); auto; lra. }
    destruct (Qeq_dec (wp_iid c (fun st => if e st then 1 else 0) x) 1).
    + rewrite q, Qminus_cancel, Qdiv_0_den; lra.
    + apply Qle_shift_div_l. lra. rewrite Qmult_0_l. apply IHc; auto.
      intro st; destruct (e st); auto; lra.
  - intro x; destruct (e x); auto; lra.
Qed.

Fixpoint loop_chain (e : exp) (c : cpGCL) (i : nat) : cpGCL :=
  match i with
  | O => CSeq c (CIte e CAbort CSkip)
  | S i' => CSeq c (CIte e (loop_chain e c i') CSkip)
  end.

(* Lemma dfjkgdf (e : exp) x c f : *)
(*   c <> CAbort -> *)
(*   (if e x then wp_iid c (fun _ : St => 0) x else f x) == *)
(*   wp_iid c (fun st' : St => if e st' then 0 else f st') x. *)
(* Proof. *)
(*   induction c; simpl; intro Hneq; try congruence; clear Hneq. *)
(*   - (* Do we need the iid condition here ..? *) *)
(*     admit. *)
(*   - unfold compose. *)
(* Admitted. *)

(* Lemma djuifgdfg (e : exp) x c f : *)
(*   (if e x then wp_iid c f x else f x) == *)
(*   wp_iid c (fun st' : St => if e st' then 0 else f st') x. *)
(* Proof. *)
(*   induction c; simpl. *)
(*   - reflexivity. *)

(* Lemma jkdfgdfg e c n f x : *)
(*   wp_iid (loop_chain e c n) f x == *)
(*   wp_iid c (fun st => if e st then 0 else f st) x * *)
(*   sum_Q_list (map (fun i => Qpow (wp_iid c (fun st => if e st then 1 else 0) x) i) (seq 0 n)). *)
(* Admitted. *)

Lemma wp_iid_chain_geometric_series f e c x i :
  (* c <> CAbort -> *)
  wp_iid (loop_chain e c i) f x ==
  geometric_series (wp_iid c (fun st' : St => if e st' then 0 else f st') x)
                   (wp_iid c (fun st' : St => if e st' then 1 else 0) x) i.
Proof.
  induction i.
  - reflexivity.
  - simpl.
    unfold compose. rewrite <- IHi.
Admitted.

Theorem wp_wp_iid (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  expectation f ->
  wp c f (wp_iid c f).
Proof.
  revert f. induction c; intros f Hwf Hexp; simpl; inversion Hwf; subst.
  - constructor. apply f_Qeq_refl.
  - constructor; apply f_Qeq_refl.
  - constructor; apply f_Qeq_refl.
  - unfold compose.
    econstructor; auto.
    + apply IHc1; auto.
      apply wp_iid_expectation; auto.
    + apply f_Qeq_refl.
  - econstructor; auto; apply f_Qeq_refl.
  - econstructor; auto; apply f_Qeq_refl.
  - apply wp_while with (ch := flip wp_iid f ∘ loop_chain e c).
    + 
(*       reflexivity. *)
(*     + intros i. *)
(*       admit. (* need iid condition *) *)
(*     + apply supremum_pointwise; intro x.  *)
(*       apply geometric_supremum. *)
(*       * apply wp_iid_expectation; auto. *)
(*         intro st; destruct (e st); auto; lra. *)
(*       * apply wp_iid_expectation; auto. *)
(*         intro st; destruct (e st); auto; lra. *)
(*       * admit. (* needs to be a separate case probably *) *)
(*       * intro i; apply wp_iid_chain_geometric_series. *)
(*   - constructor; apply f_Qeq_refl. *)
(* Admitted. *)
Admitted.
