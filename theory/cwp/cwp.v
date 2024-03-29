(** Relational and functional specifications of conditional weakest
    pre-expectation semantics. *)

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
Open Scope order_scope.

(** Note on the relational versions of wp and wlp: we make them
  explicitly "proper" wrt extensional equivalence of arguments. This
  is necessary (or at least useful) because equivalence of standard
  library rational numbers doesn't coincide with Coq's definitional
  equality in general, so rational equivalence lifted pointwise to
  functions must be handled explicitly (can't use functional
  extensionality axiom). *)

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
    ch O ==f (fun st => if e st : bool then const 0 st else f st) ->
    (forall n, exists g, wp body (ch n) g /\
               ch (S n) ==f fun st => if e st : bool then g st else f st) ->
    supremum f' ch ->
    wp (CWhile e body) f f'
| wp_observe : forall e f f',
    f' ==f (fun st => if e st : bool then f st else 0) ->
    wp (CObserve e) f f'.

(** Relational specification of weakest liberal pre-expectation
    semantics. *)
Inductive wlp : cpGCL -> (St -> Q) -> (St -> Q) -> Prop :=
| wlp_skip : forall f g, f ==f g -> wlp CSkip f g
| wlp_abort : forall f g, g ==f const 1 -> wlp CAbort f g
| wlp_assign : forall x e f f',
    f' ==f (fun st => f (upd x (e st) st)) ->
    wlp (CAssign x e) f f'
| wlp_seq : forall c1 c2 f f' g g',
    wlp c2 f g ->
    wlp c1 g g' ->
    f' ==f g' ->
    wlp (CSeq c1 c2) f f'
| wlp_ite : forall e c1 c2 f f' g h,
    wlp c1 f g ->
    wlp c2 f h ->
    f' ==f (fun st => if e st : bool then g st else h st) ->
    wlp (CIte e c1 c2) f f'
| wlp_choice : forall p c1 c2 f f' g h,
    wlp c1 f g ->
    wlp c2 f h ->
    f' ==f (fun st => p * g st + (1-p) * h st) ->
    wlp (CChoice p c1 c2) f f'
| wlp_while : forall e body f f' ch,
    ch O ==f (fun st => if e st : bool then const 1 st else f st) ->
    (forall n, exists g, wlp body (ch n) g /\
               ch (S n) ==f fun st => if e st : bool then g st else f st) ->
    infimum f' ch ->
    wlp (CWhile e body) f f'
| wlp_observe : forall e f f',
    f' ==f (fun st => if e st : bool then f st else 0) ->
    wlp (CObserve e) f f'.

(** cwp_ is decomposed into wp and wlp *)
Definition cwp_ (c : cpGCL) (f f' g g' : St -> Q) :=
  wp c f f' /\ wlp c g g'.

(** cwp is the ratio of the pair given by cwp_ *)
Definition cwp (c : cpGCL) (f f'' : St -> Q) :=
  exists f' g', cwp_ c f f' (const 1) g' /\ f'' ==f fun st => f' st / g' st.


(** As observed by Olmedo et al. in Lemma 7.4 (page 39), wp and wlp
  for loops can be computed directly as a ratio whenever the loops are
  iid. This leads to the following functional specifications of wp and
  wlp. *)

(** Functional specification of weakest pre-expectation semantics
    (only valid for iid programs). *)
Fixpoint wpf (c : cpGCL) (f : St -> Q) : St -> Q :=
  match c with
  | CSkip => f
  | CAbort => const 0
  | CAssign x e => fun st => f (upd x (e st) st)
  | CSeq c1 c2 => (wpf c1 ∘ wpf c2) f
  | CIte e c1 c2 => fun st => if e st then wpf c1 f st else wpf c2 f st
  | CChoice p c1 c2 => fun st => p * wpf c1 f st + (1-p) * wpf c2 f st
  | CWhile e body =>
    fun st =>
      if e st then
        wpf body (fun st' => if e st' then 0 else f st') st /
            (1 - wpf body (fun st' => if e st' then 1 else 0) st)
      else f st
  | CObserve e => fun st => if e st then f st else 0
  end.

(** Functional specification of weakest liberal pre-expectation
    semantics (only valid for iid programs). *)
Fixpoint wlpf (c : cpGCL) (f : St -> Q) : St -> Q :=
  match c with
  | CSkip => f
  | CAbort => const 1
  | CAssign x e => fun st => f (upd x (e st) st)
  | CSeq c1 c2 => (wlpf c1 ∘ wlpf c2) f
  | CIte e c1 c2 => fun st => if e st then wlpf c1 f st else wlpf c2 f st
  | CChoice p c1 c2 => fun st => p * wlpf c1 f st + (1-p) * wlpf c2 f st
  | CWhile e body =>
    fun st =>
      if e st then
        let a := wlpf body (fun st' => if e st' then 0 else f st') st in
        let r := wpf body (fun st' => if e st' then 1 else 0) st in
        if Qeq_bool r 1 then 1 else a / (1 - r)
      else f st
  | CObserve e => fun st => if e st then f st else 0
  end.

Definition cwpf_ (c : cpGCL) (f : St  -> Q) : St -> Q*Q :=
  fun st => (wpf c f st, wlpf c (const 1) st).

(** Functional specification of conditional weakest pre-expectation
    semantics (only valid for iid programs). *)
Definition cwpf (c : cpGCL) (f : St  -> Q) : St -> Q :=
  fun st => let (a, b) := cwpf_ c f st in a / b.

Definition indicator (e : exp) (st : St) : Q :=
  if e st then 1 else 0.

Definition neg_indicator (e : exp) (st : St) : Q :=
  if e st then 0 else 1.

(** [unroll e c i] is the ith finite unrolling of the loop with guard
  condition [e] and body [c]. *)
Fixpoint unroll (e : exp) (c : cpGCL) (i : nat) : cpGCL :=
  match i with
  | O => CIte e CAbort CSkip
  | S i' => CIte e (CSeq c (unroll e c i')) CSkip
  end.

(** iid condition for functional wp *)
Definition iid_wpf (e : exp) (c : cpGCL) :=
  forall f st n,
    e st = true ->
    wpf (unroll e c (S n)) f st ==
    wpf c (indicator e) st * wpf (unroll e c n) f st +
    wpf c (fun x => if e x then 0 else f x) st.

(** iid condition for functional wlp *)
Definition iid_wlpf (e : exp) (c : cpGCL) :=
  forall f st n,
    e st = true ->
    wlpf (unroll e c (S n)) f st ==
    wpf c (indicator e) st * wlpf (unroll e c n) f st +
    wlpf c (fun x => if e x then 0 else f x) st.

(** The loop with guard expression e and body c is iid wrt both wpf
    and wlpf. *)
Definition iid (e : exp) (c : cpGCL) :=
  iid_wpf e c /\ iid_wlpf e c.

(** Predicate asserting that all loops in a program are iid. *)
Inductive iid_cpGCL : cpGCL -> Prop :=
| iid_skip : iid_cpGCL CSkip
| iid_abort : iid_cpGCL CAbort
| iid_assign : forall x e, iid_cpGCL (CAssign x e)
| iid_seq : forall c1 c2,
    iid_cpGCL c1 -> iid_cpGCL c2 ->
    iid_cpGCL (CSeq c1 c2)
| iid_ite : forall e c1 c2,
    iid_cpGCL c1 -> iid_cpGCL c2 ->
    iid_cpGCL (CIte e c1 c2)
| iid_choice : forall p c1 c2,
    iid_cpGCL c1 -> iid_cpGCL c2 ->
    iid_cpGCL (CChoice p c1 c2)
| iid_while : forall e c,
    iid_cpGCL c ->
    iid e c ->
    iid_cpGCL (CWhile e c)
| iid_observe : forall e,
    iid_cpGCL (CObserve e).


(** A couple tactics that are useful for reasoning about example
    programs with wp and wlp. *)

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


(** wp is proper wrt extensional equivalence of its function
    arguments. *)
Instance Proper_wp : Proper (eq ==> f_Qeq ==> f_Qeq ==> iff) wp.
Proof.
  unfold f_Qeq; intros ? c ? f g Heq f' g' Heq'; subst; split; intro Hwp.
  - revert f g Heq f' g' Heq' Hwp.
    induction c; intros f g Heq f' g' Heq' Hwp; inversion Hwp; subst.
    + constructor; intro x; rewrite <- Heq, H; apply Heq'.
    + constructor; intro x; rewrite <- H, Heq'; reflexivity.
    + constructor; intro x. rewrite <- Heq, <- H3, Heq'; reflexivity.
    + econstructor; eauto.
      eapply IHc2; eauto; reflexivity. intro x; rewrite <- Heq'; apply H5.
    + assert (Hwp0: wp c1 g g0).
      { eapply IHc1; eauto; reflexivity. }
      assert (Hwp1: wp c2 g h).
      { eapply IHc2; eauto; reflexivity. }
      econstructor; eauto.
      intro x; rewrite <- Heq'; auto.
    + econstructor.
      * eapply IHc1. auto. apply (f_Qeq_refl g0). auto.
      * eapply IHc2. auto. apply (f_Qeq_refl h). auto.
      * intro x; rewrite <- Heq', H6; reflexivity.
    + econstructor; eauto.
      * intro x. rewrite H1. destruct (e x); auto; lra.
      * intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
        exists g0. split; auto.
        intro x. rewrite Hg0'.
        destruct (e x); auto; reflexivity.
      * eapply equ_supremum; eauto.
        apply f_Qeq_equ; auto.
    + constructor; intro x; rewrite <- Heq', H0.
      destruct (e x); auto; reflexivity.
  - revert f g Heq f' g' Heq' Hwp.
    induction c; intros f g Heq f' g' Heq' Hwp; inversion Hwp; subst.
    + constructor; intro x; rewrite Heq, Heq'; auto.
    + constructor; intro x; rewrite <- H, Heq'; reflexivity.
    + constructor; intro x. rewrite Heq, Heq'; auto.
    + econstructor; eauto.
      eapply IHc2; eauto; reflexivity. intro x; rewrite Heq'; apply H5.
    + assert (Hwp0: wp c1 f g0).
      { eapply IHc1; eauto; reflexivity. }
      assert (Hwp1: wp c2 f h).
      { eapply IHc2; eauto; reflexivity. }
      econstructor; eauto.
      intro x; rewrite Heq'; auto.
    + econstructor.
      * eapply IHc1. auto. apply (f_Qeq_refl g0). auto.
      * eapply IHc2. auto. apply (f_Qeq_refl h). auto.
      * intro x; rewrite Heq', H6; reflexivity.
    + econstructor; eauto.
      * intro x; rewrite H1; destruct (e x); try rewrite Heq; reflexivity.
      * intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
        exists g0. split; auto.
        intro x. rewrite Hg0'.
        destruct (e x); auto. reflexivity. rewrite Heq; reflexivity.
      * eapply equ_supremum; eauto.
        apply f_Qeq_equ; intro x; symmetry; apply Heq'.
    + constructor; intro x; rewrite  Heq', H0.
      destruct (e x); symmetry; auto; reflexivity.
Qed.

(** wlp is proper wrt extensional equivalence of its function
    arguments. *)
Instance Proper_wlp : Proper (eq ==> f_Qeq ==> f_Qeq ==> iff) wlp.
Proof.
  unfold f_Qeq; intros ? c ? f g Heq f' g' Heq'; subst; split; intro Hwlp.
  - revert f g Heq f' g' Heq' Hwlp.
    induction c; intros f g Heq f' g' Heq' Hwlp; inversion Hwlp; subst.
    + constructor; intro x; rewrite <- Heq, H; apply Heq'.
    + constructor; intro x; rewrite <- H, Heq'; reflexivity.
    + constructor; intro x. rewrite <- Heq, <- H3, Heq'; reflexivity.
    + econstructor; eauto.
      eapply IHc2; eauto; reflexivity. intro x; rewrite <- Heq'; apply H5.
    + assert (Hwp0: wlp c1 g g0).
      { eapply IHc1; eauto; reflexivity. }
      assert (Hwp1: wlp c2 g h).
      { eapply IHc2; eauto; reflexivity. }
      econstructor; eauto.
      intro x; rewrite <- Heq'; auto.
    + econstructor.
      * eapply IHc1. auto. apply (f_Qeq_refl g0). auto.
      * eapply IHc2. auto. apply (f_Qeq_refl h). auto.
      * intro x; rewrite <- Heq', H6; reflexivity.
    + econstructor; eauto.
      * intro x; rewrite H1; destruct (e x); auto; reflexivity.
      * intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
        exists g0. split; auto.
        intro x. rewrite Hg0'.
        destruct (e x); auto; reflexivity.
      * eapply equ_infimum; eauto.
        apply f_Qeq_equ; auto.
    + constructor; intro x; rewrite <- Heq', H0.
      destruct (e x); auto; reflexivity.
  - revert f g Heq f' g' Heq' Hwlp.
    induction c; intros f g Heq f' g' Heq' Hwp; inversion Hwp; subst.
    + constructor; intro x; rewrite Heq, Heq'; auto.
    + constructor; intro x; rewrite <- H, Heq'; reflexivity.
    + constructor; intro x. rewrite Heq, Heq'; auto.
    + econstructor; eauto.
      eapply IHc2; eauto; reflexivity. intro x; rewrite Heq'; apply H5.
    + assert (Hwp0: wlp c1 f g0).
      { eapply IHc1; eauto; reflexivity. }
      assert (Hwp1: wlp c2 f h).
      { eapply IHc2; eauto; reflexivity. }
      econstructor; eauto.
      intro x; rewrite Heq'; auto.
    + econstructor.
      * eapply IHc1. auto. apply (f_Qeq_refl g0). auto.
      * eapply IHc2. auto. apply (f_Qeq_refl h). auto.
      * intro x; rewrite Heq', H6; reflexivity.
    + econstructor; eauto.
      * intro x; rewrite H1; destruct (e x); try rewrite Heq; reflexivity.
      * intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
        exists g0. split; auto.
        intro x. rewrite Hg0'.
        destruct (e x); auto. reflexivity. rewrite Heq; reflexivity.
      * eapply equ_infimum; eauto.
        apply f_Qeq_equ; intro x; symmetry; apply Heq'.
    + constructor; intro x; rewrite  Heq', H0.
      destruct (e x); symmetry; auto; reflexivity.
Qed.

(** cwp is proper wrt extensional equivalence of its function
    arguments. *)
Instance Proper_cwp : Proper (eq ==> f_Qeq ==> f_Qeq ==> iff) cwp.
Proof.
  unfold f_Qeq; intros ? c ? f g Heq f' g' Heq'; subst.
  unfold cwp, cwp_.
  split; intros (f'' & g'' & [Hwp Hwlp] & Hrat).
  - exists f'', g''; split.
    + split.
      * eapply Proper_wp; unfold f_Qeq.
        reflexivity. symmetry. eauto. reflexivity. auto.
      * apply Hwlp.
    + intro x; rewrite <- Heq'; auto.
  - exists f'', g''; split.
    + split.
      * eapply Proper_wp; unfold f_Qeq.
        reflexivity. eauto. reflexivity. auto.
      * apply Hwlp.
    + intro x; rewrite Heq'; auto.
Qed.

(** wpf is proper wrt extensional equivalence of its function
    arguments. *)
Instance Proper_wpf : Proper (eq ==> f_Qeq ==> f_Qeq) wpf.
Proof.
  intros c1 c2 Heq; subst.
  induction c2; intros f g Hqeq st; simpl.
  - apply Hqeq.
  - reflexivity.
  - apply Hqeq.
  - unfold compose, respectful, f_Qeq in *.
    rewrite IHc2_1. reflexivity. apply IHc2_2; auto.
  - destruct (e st).
    + apply IHc2_1; auto.
    + apply IHc2_2; auto.
  - unfold respectful, f_Qeq in *.
    rewrite IHc2_1, IHc2_2; auto; reflexivity.
  - unfold respectful, f_Qeq in *.
    destruct (e st); auto.
    rewrite IHc2. reflexivity.
    intros; simpl; destruct (e x); auto; reflexivity.
  - destruct (e st); auto; reflexivity.
Qed.

(** wlpf is proper wrt extensional equivalence of its function
    arguments. *)
Instance Proper_wlpf : Proper (eq ==> f_Qeq ==> f_Qeq) wlpf.
Proof.
  intros c1 c2 Heq; subst.
  induction c2; intros f g Hqeq st; simpl.
  - apply Hqeq.
  - reflexivity.
  - apply Hqeq.
  - unfold compose, respectful, f_Qeq in *.
    rewrite IHc2_1. reflexivity. apply IHc2_2; auto.
  - destruct (e st).
    + apply IHc2_1; auto.
    + apply IHc2_2; auto.
  - unfold respectful, f_Qeq in *.
    rewrite IHc2_1, IHc2_2; auto; reflexivity.
  - unfold respectful, f_Qeq in *.
    destruct (e st); auto.
    set (a := wlpf c2 (fun st' : St => if e st' then 0 else f st') st).
    set (r := wpf c2 (fun st' : St => if e st' then 1 else 0) st).
    destruct (Qeq_dec r 1).
    + rewrite Qeq_eq_bool; lra.
    + rewrite Qeq_bool_false; auto.
      rewrite IHc2. reflexivity.
    intros; simpl; destruct (e x). reflexivity.
    rewrite Hqeq; reflexivity.
  - destruct (e st); auto; reflexivity.
Qed.

(** wp preserves const 0. *)
Lemma wp_strict c :
  wp c (const 0) (const 0).
Proof.
  induction c; try (constructor; reflexivity).
  - econstructor; eauto; reflexivity.
  - econstructor; eauto; intro x; destruct (e x); reflexivity.
  - econstructor; eauto; unfold const; intro; lra.
  - apply wp_while with (ch := const (const 0)).
    + intro x; destruct (e x); reflexivity.
    + intro i; exists (const 0).
      unfold const; split; auto.
      intro x; destruct (e x); reflexivity.
    + apply const_supremum; reflexivity.
  - constructor; intro x; destruct (e x); reflexivity.
Qed.

(** wlp preserves const 1. *)
Lemma wlp_strict c :
  no_obs c ->
  wlp c (const 1) (const 1).
Proof.
  induction c; intros Hno_obs;
    try (constructor; reflexivity); inversion Hno_obs; subst.
  - econstructor; eauto; reflexivity.
  - econstructor; eauto; intro x; destruct (e x); reflexivity.
  - econstructor; eauto; unfold const; intro; lra.
  - apply wlp_while with (ch := const (const 1)).
    + intro x; destruct (e x); reflexivity.
    + intro i; exists (const 1).
      unfold const; split; auto.
      intro x; destruct (e x); reflexivity.
    + apply const_infimum; reflexivity.
Qed.

(** wp is deterministic up to extensional equivalence. *)
Lemma wp_deterministic c f g g' :
  wp c f g ->
  wp c f g' ->
  g ==f g'.
Proof.
  revert f g g'.
  induction c; simpl; intros f g g' Hwlp1 Hwlp2;
    inversion Hwlp1; inversion Hwlp2; subst.
  - intros; rewrite <- H; auto.
  - intros; rewrite H, H0; reflexivity.
  - intros; rewrite H3, H8; reflexivity.
  - assert (g0 ==f g1).
    { eapply IHc2; eauto. }
    intros; rewrite H5, H12. eapply IHc1; eauto.
    eapply Proper_wp. reflexivity.
    intro y. apply H. reflexivity.
    auto.
  - intros; rewrite H6, H14.
    destruct (e x).
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - intros; rewrite H6, H14.
    assert (Hg: g0 ==f g1).
    { eapply IHc1; eauto. }
    assert (Hh: h ==f h0).
    { eapply IHc2; eauto. }
    rewrite Hg, Hh; reflexivity.
  - apply f_Qeq_equ.
    eapply supremum_unique; eauto.
    assert (equ ch ch0).
    { apply chain_equ.
      intro i. apply f_Qeq_equ.
      induction i; intro x.
      - rewrite H1, H8; reflexivity.
      - destruct (H2 i) as [h [Hwlp1' Hch1]].
        destruct (H9 i) as [h' [Hwlp2' Hch2]].
        rewrite Hch1, Hch2.
        destruct (e x); try reflexivity.
        eapply IHc; eauto.
        eapply Proper_wp. reflexivity.
        intro y. apply IHi. reflexivity.
        auto. }
    eapply Proper_supremum. reflexivity. eauto. auto.
  - intros x; rewrite H0, H4; destruct (e x); reflexivity.
Qed.

(** wlp is deterministic up to extensional equivalence. *)
Lemma wlp_deterministic c f g g' :
  wlp c f g ->
  wlp c f g' ->
  g ==f g'.
Proof.
  revert f g g'.
  induction c; simpl; intros f g g' Hwlp1 Hwlp2;
    inversion Hwlp1; inversion Hwlp2; subst.
  - intros; rewrite <- H; auto.
  - intros; rewrite H, H0; reflexivity.
  - intros; rewrite H3, H8; reflexivity.
  - assert (g0 ==f g1).
    { eapply IHc2; eauto. }
    intros; rewrite H5, H12. eapply IHc1; eauto.
    eapply Proper_wlp. reflexivity.
    intro y. apply H. reflexivity.
    auto.
  - intros; rewrite H6, H14.
    destruct (e x).
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - intros; rewrite H6, H14.
    assert (Hg: g0 ==f g1).
    { eapply IHc1; eauto. }
    assert (Hh: h ==f h0).
    { eapply IHc2; eauto. }
    rewrite Hg, Hh; reflexivity.
  - apply f_Qeq_equ.
    eapply infimum_unique; eauto.
    assert (equ ch ch0).
    { apply chain_equ.
      intro i. apply f_Qeq_equ.
      induction i; intro x.
      - rewrite H1, H8; reflexivity.
      - destruct (H2 i) as [h [Hwlp1' Hch1]].
        destruct (H9 i) as [h' [Hwlp2' Hch2]].
        rewrite Hch1, Hch2.
        destruct (e x); try reflexivity.
        eapply IHc; eauto.
        eapply Proper_wlp. reflexivity.
        intro y. apply IHi. reflexivity.
        auto. }
    eapply Proper_infimum. reflexivity. eauto. auto.
  - intros x; rewrite H0, H4; destruct (e x); reflexivity.
Qed.

(** cwp is deterministic up to extensional equivalence. *)
Lemma cwp_deterministic c f g g' :
  cwp c f g ->
  cwp c f g' ->
  g ==f g'.
Proof.
  unfold cwp.
  intros (n & m & [Hwp Hwlp] & Hg) (n' & m' & [Hwp' Hwlp'] & Hg') x.
  rewrite Hg, Hg'.
  rewrite wp_deterministic; eauto.
  cut (m x == m' x).
  { intros; rewrite H; reflexivity. }
  eapply wlp_deterministic; eauto.
Qed.

(* Lemma wp_expectation (c : cpGCL) (f f' : St -> Q) : *)
(*   wf_cpGCL c -> *)
(*   expectation f -> *)
(*   wp c f f' -> *)
(*   expectation f'. *)
(* Proof. *)
(* Admitted. *)

(* (** The relational version of wp is monotone (the corresponding proof *)
(*     for wpf is in cwp_cwpf.v. *) *)
(* Lemma wp_monotone (c : cpGCL) : *)
(*   wf_cpGCL c -> *)
(*   forall f f' g g' : St -> Q, *)
(*     expectation f -> expectation g -> *)
(*     wp c f f' -> wp c g g' -> *)
(*     leq f g -> leq f' g'. *)
(* Proof. *)
(*   induction c; simpl; intros Hwf f f' g g' Hf Hg Hwpf Hwpg Hleq; *)
(*     inversion Hwpf; inversion Hwpg; subst; intro x. *)
(*   - rewrite <- H, <- H0; auto. *)
(*   - rewrite H, H0; lra. *)
(*   - rewrite H3, H8; apply Hleq. *)
(*   - inversion Hwf; subst; rewrite H5, H12. *)
(*     eapply IHc1 with (f:=g0) (g:=g1); eauto. *)
(*     + eapply wp_expectation with (f:=f); eauto. *)
(*     + eapply wp_expectation with (f:=g); eauto. *)
(*   - inversion Hwf; subst; rewrite H6, H14; destruct (e x). *)
(*     + eapply IHc1 with (f:=f); eauto. *)
(*     + eapply IHc2 with (f:=f); eauto. *)
(*   - inversion Hwf; subst; rewrite H6, H14. *)
(*     cut (g0 x <= g1 x). *)
(*     { intro Hle; cut (h x <= h0 x). *)
(*       { nra. } *)
(*       eapply IHc2 with (f:=f); eauto. } *)
(*     eapply IHc1 with (f:=f); eauto. *)
(*   - admit. *)
(*   - rewrite H0, H4; destruct (e x); auto; lra. *)
(* Admitted. *)

Lemma unroll_le (e : exp) (c : cpGCL) (i : nat) :
  unroll e c i ⊑ unroll e c (S i).
Proof.
  induction i.
  - repeat constructor.
  - constructor; constructor; apply IHi.
Qed.

(* (** wp is ω-continuous. *) *)
(* Lemma wp_continuous (c : cpGCL) : *)
(*   wf_cpGCL c -> *)
(*   forall ch ch' : nat -> St -> Q, forall sup sup' : St -> Q, *)
(*       chain ch -> *)
(*       (forall i, expectation (ch i)) -> *)
(*       supremum sup ch -> *)
(*       wp c sup sup' -> *)
(*       (forall i, wp c (ch i) (ch' i)) -> *)
(*       supremum sup' ch'. *)
(* Proof. *)
(*   induction c; intros Hwf ch ch' sup sup' Hchain Hexp Hsup Hwpsup Hwpchain. *)
(*   - inversion Hwpsup; subst. *)
(*     rewrite f_Qeq_equ in H. rewrite <- H. *)
(*     assert (H0: equ ch ch'). *)
(*     { split; intro i; specialize (Hwpchain i); inversion Hwpchain; subst; *)
(*         apply f_Qeq_equ in H0; apply H0. } *)
(*     rewrite <- H0; auto. *)
(*   - inversion Hwpsup; subst. *)
(*     rewrite f_Qeq_equ in H. rewrite H. *)
(*     assert (H0: equ ch' (const (const 0))). *)
(*     { split; intro i; specialize (Hwpchain i); inversion Hwpchain; subst; *)
(*         apply f_Qeq_equ in H0; apply H0. } *)
(*     rewrite H0. *)
(*     apply const_supremum; intro i; apply f_Qeq_equ; intro j; reflexivity. *)
(*   - inversion Hwpsup; subst. *)
(*     apply f_Qeq_equ in H3; rewrite H3; clear H3. *)
(*     split. *)
(*     + intros i x. specialize (Hwpchain i). *)
(*       inversion Hwpchain; subst. *)
(*       rewrite H3. apply Hsup. *)
(*     + intros ub Hub. *)
(*     admit. *)
(*   - inversion Hwpsup; subst. *)
(*     apply f_Qeq_equ in H5. *)
(*     rewrite H5. *)
(*     inversion Hwf; subst. *)
(*     assert (Htemp: forall i, exists f, wp c1 f (ch' i) /\ wp c2 (ch i) f). *)
(*     { intro i. specialize (Hwpchain i). inversion Hwpchain; subst. *)
(*       exists g0; auto; split; eapply Proper_wp; eauto; reflexivity. } *)
(*     (* Need choice function to turn Htemp into Hch'' *) *)
(*     assert (Hch'': exists ch'', (forall i, wp c1 (ch'' i) (ch' i) /\ wp c2 (ch i) (ch'' i))). *)
(*     { admit. } *)
(*     destruct Hch'' as [ch'' Hch'']. *)
(*     eapply IHc2 with (ch' := ch'') in H1; eauto. *)
(*     2: { apply Hch''. } *)
(*     eapply IHc1 with (ch := ch'') (ch' := ch') in H2; eauto. *)
(*     + intro i; eapply wp_monotone; eauto; apply Hch''. *)
(*     + intro i; eapply wp_expectation; eauto; apply Hch''. *)
(*     + apply Hch''. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - inversion Hwpsup; subst. *)
(*     apply f_Qeq_equ in H0; rewrite H0; clear H0. *)
(*     admit. *)
(* Admitted. *)
