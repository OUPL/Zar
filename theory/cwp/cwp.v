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
    ch O = const 0 ->
    (forall n, exists g, wp body (ch n) g /\
               ch (S n) ==f fun st => if e st : bool then g st else f st) ->
    supremum f' ch ->
    wp (CWhile e body) f f'
| wp_observe : forall e f f',
    f' ==f (fun st => if e st : bool then f st else 0) ->
    wp (CObserve e) f f'.

(** Relational specification of weakest liberal pre-expectation
    semantics *)
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
    ch O = const 1 ->
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
  | O => CAbort
  | S i' => CIte e (CSeq c (unroll e c i')) CSkip
  end.

(** iid condition for functional wp*)
Definition iid_wpf (e : exp) (c : cpGCL) :=
  forall f st n,
    wpf (unroll e c (S n)) f st =
    wpf c (indicator e) st * wpf (unroll e c n) f st +
    wpf c (fun x => if e x then 0 else f x) st.

(** iid condition for functional wlp*)
Definition iid_wlpf (e : exp) (c : cpGCL) :=
  forall f st n,
    wlpf (unroll e c (S n)) f st =
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
  programs using wp and wlp. *)

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
      intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
      exists g0. split; auto.
      intro x. rewrite Hg0'.
      destruct (e x); auto; reflexivity.
      eapply equ_supremum; eauto.
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
      intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
      exists g0. split; auto.
      intro x. rewrite Hg0'.
      destruct (e x); auto. reflexivity. rewrite Heq; reflexivity.
      eapply equ_supremum; eauto.
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
      intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
      exists g0. split; auto.
      intro x. rewrite Hg0'.
      destruct (e x); auto; reflexivity.
      eapply equ_infimum; eauto.
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
      intro n. specialize (H2 n). destruct H2 as [g0 [Hg0 Hg0']].
      exists g0. split; auto.
      intro x. rewrite Hg0'.
      destruct (e x); auto. reflexivity. rewrite Heq; reflexivity.
      eapply equ_infimum; eauto.
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
