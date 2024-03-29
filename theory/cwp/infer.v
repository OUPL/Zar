(** Inference on trees. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Structures.Monad.
Require Import List.
Import ListNotations.
Local Open Scope program_scope.

Require Import cpGCL.
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.

(** Inference on trees. *)

(** Compute the probability of reaching a fail node with label n. *)
Fixpoint infer_fail {A : Type} (n : nat) (t : tree A) : Q :=
  match t with
  | Leaf _ => 0
  | Fail _ m => if m =? n then 1 else 0
  | Choice p t1 t2 => p * infer_fail n t1 + (1-p) * infer_fail n t2
  | Fix m t =>
    let a := infer_fail n t in
    let b := infer_fail m t in
    a / (1 - b)
  end.

(** Compute the expected value of f. *)
Fixpoint infer_f {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf x => f x
  | Fail _ _ => 0
  | Choice p t1 t2 => p * infer_f f t1 + (1-p) * infer_f f t2
  | Fix m t =>
    let a := infer_f f t in
    let b := infer_fail m t in
    a / (1 - b)
  end.

(** The same as infer_f except in the case of divergent loops (choose
    the value 1 instead of 0). *)
Fixpoint infer_f_lib {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf x => f x
  | Fail _ _ => 0
  | Choice p t1 t2 => p * infer_f_lib f t1 + (1-p) * infer_f_lib f t2
  | Fix m t =>
    let a := infer_f_lib f t in
    let b := infer_fail m t in
    if Qeq_bool b 1 then 1 else a / (1 - b)
  end.

(** Compute the expected value of f normalized wrt observation
    failure. *)
Definition infer {A : Type} (f : A -> Q) (t : tree A) : Q :=
  let a := infer_f f t in
  let b := infer_f_lib (const 1) t in
  a / b.


(** Proofs about inference. *)

Lemma infer_fail_fix {A : Type} (t : tree A) (n m : nat) :
  infer_fail m (Fix n t) = infer_fail m t / (1 - infer_fail n t).
Proof. reflexivity. Qed.

Lemma infer_f_fix {A : Type} (f : A -> Q) (t : tree A) (n : nat) :
  infer_f f (Fix n t) = infer_f f t / (1 - infer_fail n t).
Proof. reflexivity. Qed.

Lemma infer_fail_sum_le_1 {A : Type} (t : tree A) (l : list nat) :
  wf_tree t ->
  NoDup l ->
  (forall x, In x l -> not_bound_in x t) ->
  sum_Q_list (map (fun n => infer_fail n t) l) <= 1.
Proof.
  revert l. induction t; intros l Hwf Hnodup Hnotbound; simpl.
  - induction l; simpl.
    + lra.
    + inversion Hnodup; subst.
      apply IHl in H2. lra.
      intros; apply Hnotbound; right; auto.
  - induction l; simpl.
    + lra.
    + inversion Hnodup; subst.
      apply IHl in H2.
      destruct (Nat.eqb_spec n a); subst; try lra.
      rewrite not_in_sum_Q_list; auto; apply Qle_refl.
      intros; apply Hnotbound; right; auto.      
  - rewrite sum_Q_list_map_plus, 2!sum_Q_list_map_mult_scalar.
    inversion Hwf; subst.
    assert (Ht1: forall x, In x l -> not_bound_in x t1).
    { intros x Hin; specialize (Hnotbound x Hin).
      inversion Hnotbound; subst; auto. }
    assert (Ht2: forall x, In x l -> not_bound_in x t2).
    { intros x Hin; specialize (Hnotbound x Hin).
      inversion Hnotbound; subst; auto. }
    specialize (IHt1 l H3 Hnodup Ht1).
    specialize (IHt2 l H4 Hnodup Ht2).
    nra.
  - inversion Hwf; subst.
    assert (~ In n l).
    { intro HC. apply Hnotbound in HC. inversion HC; subst. congruence. }
    assert (H0: sum_Q_list (map (fun n => infer_fail n t) [n]) <= 1).
    { apply IHt; auto.
      - constructor; auto; constructor.
      - intros x Hin. inversion Hin; subst; auto.
        inversion H0. }
    simpl in H0. rewrite Qplus_0_r in H0.
    apply Qle_lteq in H0. destruct H0.
    + rewrite sum_Q_list_map_div_scalar; try lra.
      apply Qle_shift_div_r; try lra.
      rewrite Qmult_1_l.
      assert (Hnodup': NoDup (n :: l)).
      { constructor; auto. }
      apply IHt in Hnodup'; auto.
      * simpl in Hnodup'. lra.
      * intros x Hin. inversion Hin; subst; auto.
        apply Hnotbound in H3. inversion H3; subst; auto.
    + induction l. simpl. lra.
      simpl. rewrite H0.
      rewrite Qminus_cancel, Qdiv_0_den, Qplus_0_l.
      apply IHl. inversion Hnodup; auto.
      * intros x Hin. apply Hnotbound. right; auto.
      * intro HC. apply H. right; auto.
Qed.

Lemma infer_fail_le_1 {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  infer_fail n t <= 1.
Proof.
  intros Hwf Hnotbound.
  assert (Hnodup: NoDup [n]).
  { constructor; auto; constructor. }
  assert (H: forall x, In x [n] -> not_bound_in x t).
  { intros x [Hin | ?]; subst; auto; inversion H. }
  generalize (infer_fail_sum_le_1 Hwf Hnodup H); simpl; lra.
Qed.

Lemma infer_fail_0_le {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  0 <= infer_fail n t.
Proof.
  induction t; intros Hwf Hnotbound; simpl;
    inversion Hwf; inversion Hnotbound; subst.
  - lra.
  - destruct (Nat.eqb_spec n0 n); subst; lra.
  - specialize (IHt1 H3 H8); specialize (IHt2 H4 H10); nra.
  - specialize (IHt H1 H7).
    destruct (Qeq_dec (infer_fail n0 t) 1).
    + rewrite q, Qminus_cancel, Qdiv_0_den; lra.
    + apply Qle_shift_div_l.
      * generalize (infer_fail_le_1 H1 H2); intro Hle; lra.
      * lra.
Qed.

Lemma infer_f_expectation_0_le {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  expectation f ->
  0 <= infer_f f t.
Proof.
  revert f. induction t; intros f Hwf Hexp.
  - simpl; apply Hexp.
  - apply Qle_refl.
  - simpl.
    inversion Hwf; subst.
    specialize (IHt1 f H3 Hexp).
    specialize (IHt2 f H4 Hexp).
    nra.
  - simpl.
    inversion Hwf; subst.
    specialize (IHt f H1 Hexp).
    assert (infer_fail n t <= 1).
    { apply infer_fail_le_1; auto. }
    subst.
    assert (0 <= 1 - infer_fail n t).
    { lra. }
    apply Qle_lt_or_eq in H0.
    destruct H0.
    + apply Qle_shift_div_l; auto; lra.
    + rewrite <- H0. apply Qle_lteq.
      right. simpl.
      rewrite Qdiv_0_den; reflexivity.
Qed.

Lemma infer_f_lib_expectation_0_le {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  expectation f ->
  0 <= infer_f_lib f t.
Proof.
  induction t; simpl; intros Hwf Hexp.
  - apply Hexp.
  - lra.
  - inversion Hwf; subst.
    specialize (IHt1 H3 Hexp); specialize (IHt2 H4 Hexp); nra.
  - inversion Hwf; subst.
    destruct (Qeq_bool (infer_fail n t) 1) eqn:Hq1; try lra.
    apply Qeq_bool_neq in Hq1.
    assert (infer_fail n t <= 1).
    { apply infer_fail_le_1; auto. }
    apply Qle_shift_div_l; try lra.
    rewrite Qmult_0_l; apply IHt; auto.
Qed.

Lemma not_in_infer_fail {A : Type} (l : nat) (t : tree A) :
  not_in l t ->
  infer_fail l t == 0.
Proof.
  induction t; intro Hnotin; simpl.
  - reflexivity.
  - destruct (Nat.eqb_spec n l); subst.
    + inversion Hnotin; subst; congruence.
    + reflexivity.
  - inversion Hnotin; subst; rewrite IHt1, IHt2; auto; field.
  - inversion Hnotin; subst; rewrite IHt; auto; apply Qdiv_0_num.
Qed.

Lemma not_in_infer_fail_tree_bind {A B : Type} (t : tree A) m (k : A -> tree B) :
  (forall x, not_in m (k x)) ->
  (forall n x, bound_in n t -> not_in n (k x)) ->
  infer_fail m (tree_bind t k) == infer_fail m t.
Proof.
  revert m k.
  induction t; intros m k Hnotin Hnotin'; unfold tree_bind in *; simpl.
  - apply not_in_infer_fail; auto.
  - reflexivity.
  - rewrite IHt1; auto. rewrite IHt2; auto. reflexivity.
    + intros n x Hbound; apply Hnotin'; solve [constructor; auto].
    + intros n x Hbound; apply Hnotin'; solve [constructor; auto].
  - rewrite IHt; auto. rewrite IHt; auto. reflexivity.
    + intro x; apply Hnotin'; constructor.
    + intros l x Hbound. apply Hnotin'.
      destruct (Nat.eqb_spec l n); subst; constructor; auto.
    + intros l x Hbound. apply Hnotin'.
      destruct (Nat.eqb_spec l n); subst; constructor; auto.
Qed.

Lemma infer_fail_bind {A B : Type} (lbl : nat) (t : tree A) (k : A -> tree B) :
  not_in lbl t ->
  (forall n x, bound_in n t -> not_in n (k x)) ->
  infer_f (infer_fail lbl ∘ k) t == infer_fail lbl (tree_bind t k).
Proof.
  revert lbl k.
  induction t; simpl; intros lbl k Hnotin Hbound; inversion Hnotin; subst.
  - reflexivity.
  - apply Nat.eqb_neq in H1.
    rewrite Nat.eqb_sym, H1; reflexivity.
  - rewrite IHt1, IHt2; auto; try reflexivity;
      intros n x Hboundin; apply Hbound; solve [constructor; auto].
  - rewrite IHt; auto.
    + assert (H: infer_fail n (tree_bind t k) == infer_fail n t).
      { apply not_in_infer_fail_tree_bind.
        - intro x; apply Hbound; constructor.
        - intros m x Hboundin; apply Hbound.
          destruct (Nat.eqb_spec m n); subst; constructor; auto. }
      rewrite H; reflexivity.
    + intros m x Hboundin; apply Hbound.
      destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Lemma infer_f_bind {A B : Type} (f : B -> Q) (t : tree A) (k : A -> tree B) :
  (forall n x, bound_in n t -> not_in n (k x)) ->
  infer_f (infer_f f ∘ k) t == infer_f f (tree_bind t k).
Proof.
  revert f k. induction t; intros f k Hnotin; try reflexivity.
  - simpl; rewrite IHt1, IHt2; try reflexivity;
      intros n st Hbound; apply Hnotin;
        try solve [apply bound_in_choice2; auto]; constructor; auto.
  - simpl. apply Qeq_Qdiv.
    + apply IHt; intros n0 st Hbound; apply Hnotin.
      destruct (Nat.eqb_spec n0 n); subst; constructor; auto.
    + apply Qeq_Qminus; try reflexivity.
      clear IHt. revert Hnotin. revert k n. induction t; intros k m Hnotin.
      * simpl. rewrite not_in_infer_fail. reflexivity. apply Hnotin. constructor.
      * simpl. reflexivity.
      * simpl. rewrite IHt1, IHt2. reflexivity.
        intros m' x Hbound. apply Hnotin. inversion Hbound; subst.
        constructor. constructor; auto. apply bound_in_choice2; auto.
        intros m' x Hbound. apply Hnotin. inversion Hbound; subst.
        constructor. constructor; auto. constructor; auto.
      * simpl. rewrite IHt. rewrite IHt. reflexivity.
        intros m' x Hbound. apply Hnotin.
        inversion Hbound; subst.
        destruct (Nat.eqb_spec n m); subst. constructor. constructor; auto.
        destruct (Nat.eqb_spec m' m); subst. constructor. constructor; auto.
        intros m' x Hbound. apply Hnotin.
        inversion Hbound; subst.
        constructor.
        constructor; auto.
        destruct (Nat.eqb_spec m' n); subst. constructor. constructor; auto.
Qed.

Lemma infer_f_lib_bind_lem1 {A B : Type} n (t : tree A) (k : A -> tree B) :
  (forall m x, bound_in m (Fix n t) -> not_in m (k x)) ->
  infer_fail n (tree_bind t k) == infer_fail n t.
Proof.
  intros Hnotin.
  rewrite not_in_infer_fail_tree_bind; auto.
  - reflexivity.
  - intro x; apply Hnotin; constructor.
  - intros m x Hbound; apply Hnotin.
    destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Lemma infer_f_lib_bind {A B : Type} (f : B -> Q) (t : tree A) (k : A -> tree B) :
  (forall n x, bound_in n t -> not_in n (k x)) ->
  infer_f_lib (infer_f_lib f ∘ k) t == infer_f_lib f (tree_bind t k).
Proof.
  revert f k. induction t; intros f k Hnotin; simpl; try reflexivity.
  - rewrite IHt1, IHt2; try reflexivity;
      intros n st Hbound; apply Hnotin;
        try solve [apply bound_in_choice2; auto]; constructor; auto.
  - destruct (Qeq_dec (infer_fail n t) 1).
    { rewrite q; simpl.
      destruct (Qeq_dec (infer_fail n (tree_bind t k)) 1).
      { rewrite q0; simpl; reflexivity. }
      rewrite infer_f_lib_bind_lem1 in n0; auto; congruence. }
    destruct (Qeq_dec (infer_fail n (tree_bind t k)) 1).
    { rewrite q. simpl.
      rewrite Qeq_bool_false; auto.
      rewrite IHt.
      - rewrite infer_f_lib_bind_lem1 in q; auto; congruence.
      - intros m x Hbound; apply Hnotin.
        destruct (Nat.eqb_spec m n); subst; constructor; auto. }
    rewrite 2!Qeq_bool_false; auto.
    rewrite IHt; auto.
    + unfold tree_bind. erewrite <- not_in_infer_fail_tree_bind.
      * reflexivity.
      * intro x; apply Hnotin; constructor.
      * intros m x Hbound; apply Hnotin.
        destruct (Nat.eqb_spec m n); subst; constructor; auto.
    + intros m x Hbound; apply Hnotin.
      destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Lemma not_in_infer_fail_0 {A : Type} (l : nat) (t : tree A) :
  not_in l t ->
  infer_fail l t == 0.
Proof.
  induction t; intro Hnotin; simpl.
  - reflexivity.
  - destruct (Nat.eqb_spec n l); subst.
    + inversion Hnotin; subst; congruence.
    + reflexivity.
  - inversion Hnotin; subst; rewrite IHt1, IHt2; auto; field.
  - inversion Hnotin; subst; rewrite IHt; auto; apply Qdiv_0_num.
Qed.

Lemma sum_Q_list_infer_fail_choice_l {A : Type} (l : list nat) (t1 t2 : tree A) (p : Q) :
  wf_tree t1 -> wf_tree t2 ->
  (forall x, In x l -> not_bound_in x t1) ->
  (forall x, In x l -> not_bound_in x t2) ->
  NoDup l ->
  0 < p -> p < 1 ->
  sum_Q_list (map (flip infer_fail (Choice p t1 t2)) l) == 1 ->
  sum_Q_list (map (flip infer_fail t1) l) == 1.
Proof.
  unfold flip; simpl.
  intros Hwf1 Hwf2 Hnotbound1 Hnotbound2 Hnodup Hlt0 Hlt1 Hsum.
  rewrite sum_Q_list_map_plus in Hsum.
  rewrite <- 2!sum_Q_list_distr in Hsum.
  eapply convex_l; eauto.
  - split.
    + apply sum_Q_list_nonnegative.
      intros x Hin. apply in_map_iff in Hin.
      destruct Hin as [y [? Hy]]; subst.
      eapply infer_fail_0_le; auto.
    + apply infer_fail_sum_le_1; auto.
  - split.
    + apply sum_Q_list_nonnegative.
      intros x Hin. apply in_map_iff in Hin.
      destruct Hin as [y [? Hy]]; subst.
      apply infer_fail_0_le; auto.
    + apply infer_fail_sum_le_1; auto.
Qed.

Lemma sum_Q_list_infer_fail_choice_r {A : Type} (l : list nat) (t1 t2 : tree A) (p : Q) :
  wf_tree t1 -> wf_tree t2 ->
  (forall x, In x l -> not_bound_in x t1) ->
  (forall x, In x l -> not_bound_in x t2) ->
  NoDup l ->
  0 < p -> p < 1 ->
  sum_Q_list (map (flip infer_fail (Choice p t1 t2)) l)  == 1 ->
  sum_Q_list (map (flip infer_fail t2) l) == 1.
Proof.
  unfold flip; simpl.
  intros Hwf1 Hwf2 Hnotbound1 Hnotbound2 Hnodup Hlt0 Hlt1 Hsum.
  rewrite sum_Q_list_map_plus in Hsum.
  rewrite <- 2!sum_Q_list_distr in Hsum.
  eapply convex_r; eauto.
  - split.
    + apply sum_Q_list_nonnegative.
      intros x Hin. apply in_map_iff in Hin.
      destruct Hin as [y [? Hy]]; subst.
      apply infer_fail_0_le; auto.
    + apply infer_fail_sum_le_1; auto.
  - split.
    + apply sum_Q_list_nonnegative.
      intros x Hin. apply in_map_iff in Hin.
      destruct Hin as [y [? Hy]]; subst.
      apply infer_fail_0_le; auto.
    + apply infer_fail_sum_le_1; auto.
Qed.

Lemma infer_f_fail_aux {A : Type} (t : tree A) (f : A -> Q) (m : nat) (l : list nat) :
  wf_tree t ->
  (forall x : nat, In x l -> not_bound_in x t) ->
  NoDup l ->
  not_bound_in m t ->
  sum_Q_list (map (flip infer_fail t) l) == 1 ->
  infer_f f t == 0.
Proof.
  revert l. induction t; simpl; intros l Hwf Hin_notbound Hnodup Hnotbound Hsum.
  - rewrite sum_Q_list_map_const_0 in Hsum; inversion Hsum.
  - reflexivity.
  - inversion Hwf; inversion Hnotbound; subst.
    destruct (Qeq_dec q 0).
    + rewrite q0. rewrite Qmult_0_l, Qplus_0_l, Qminus_0_r, Qmult_1_l.
      eapply IHt2 with (l:=l); auto.
      * eapply in_not_bound_choice2; eauto.
      * rewrite sum_Q_list_proper; eauto.
        unfold flip; intros ?; simpl; rewrite q0; lra.
    + destruct (Qeq_dec q 1).
      * rewrite q0. rewrite Qminus_cancel, Qmult_1_l, Qmult_0_l, Qplus_0_r.
        eapply IHt1 with (l:=l); auto.
        ++ eapply in_not_bound_choice1; eauto.
        ++ rewrite sum_Q_list_proper; eauto.
           unfold flip; intros ?; simpl; rewrite q0; lra.
      * rewrite IHt1 with (l:=l), IHt2 with (l:=l); auto. lra.
        ++ eapply in_not_bound_choice2; eauto.
        ++ apply sum_Q_list_infer_fail_choice_r in Hsum; eauto; try lra.
           ** eapply in_not_bound_choice1; eauto.
           ** eapply in_not_bound_choice2; eauto.
        ++ eapply in_not_bound_choice1; eauto.
        ++ apply sum_Q_list_infer_fail_choice_l in Hsum; eauto; try lra.
           ** eapply in_not_bound_choice1; eauto.
           ** eapply in_not_bound_choice2; eauto.
  - unfold flip in *; simpl in *.
    inversion Hwf; inversion Hnotbound; subst.
    rewrite IHt with (l:=n::l); auto.
    + apply Qdiv_0_num.
    + intros x [Hin|Hin]; subst; auto.
      apply Hin_notbound in Hin. inversion Hin; subst; auto.
    + constructor; auto. intro HC. apply Hin_notbound in HC.
      inversion HC; subst; congruence.
    + simpl.
      destruct (Qeq_dec (infer_fail n t) 1).
      * rewrite sum_Q_list_proper in Hsum.
        ++ rewrite sum_Q_list_map_const_0 in Hsum; lra.
        ++ intros ?; rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity.
      * rewrite sum_Q_list_map_div_scalar in Hsum.
        ++ rewrite Qplus_comm; apply Qlem_2; auto.
        (* ++ generalize (@infer_fail_le_1 A t n H1 H2); intros; lra. *)
Qed.

Lemma infer_f_fail {A : Type} (t : tree A) (f : A -> Q) (l : nat) :
  wf_tree t ->
  not_bound_in l t ->
  infer_fail l t == 1 ->
  infer_f f t == 0.
Proof.
  intros Hwf Hnotbound Heq.
  eapply infer_f_fail_aux with (l0:=[l]); auto.
  - intros x Hin. destruct Hin; subst; auto; contradiction.
  - constructor; auto; constructor.
  - apply Hnotbound.
  - simpl; unfold flip; rewrite Heq; reflexivity.
Qed.

Lemma infer_f_lib_fail_1 {A : Type} (t : tree A) (l : list nat) :
  wf_tree t ->
  (forall x : nat, In x l -> not_bound_in x t) ->
  (forall x, free_in x t -> In x l) ->
  NoDup l ->
  sum_Q_list (map (flip infer_fail t) l) + infer_f_lib (const 1) t == 1.
Proof.
  revert l; induction t; simpl; intros l Hwf Hin_notbound Hfree Hnodup.
  - unfold flip; simpl; rewrite sum_Q_list_map_const_0; reflexivity.
  - rewrite Qplus_0_r. unfold flip. simpl.
    specialize (Hfree n (free_in_fail n)).
    apply in_nodup_sum_Q_list; auto.
  - unfold flip. simpl.
    rewrite sum_Q_list_map_plus.
    rewrite 2!sum_Q_list_map_mult_scalar.
    inversion Hwf; subst.
    set (a := sum_Q_list (map (fun x : nat => infer_fail x t1) l)).
    set (b := sum_Q_list (map (fun x : nat => infer_fail x t2) l)).
    set (c := infer_f_lib (const 1) t1).
    set (d := infer_f_lib (const 1) t2).
    destruct (Qeq_bool q 0) eqn:Hq0.
    { apply Qeq_bool_eq in Hq0.
      rewrite Hq0, 2!Qmult_0_l, Qplus_0_l, Qminus_0_r, 2!Qmult_1_l, Qplus_0_l.
      apply IHt2; auto.
      * intros x Hin. apply Hin_notbound in Hin.
        inversion Hin; auto.
      * intros x Hfreein; apply Hfree; solve [constructor; auto]. }
    apply Qeq_bool_neq in Hq0.
    destruct (Qeq_bool q 1) eqn:Hq1.
    { apply Qeq_bool_eq in Hq1.
      rewrite Hq1, 2!Qmult_1_l, Qminus_cancel, 2!Qmult_0_l, 2!Qplus_0_r.
      apply IHt1; auto.
      - intros x Hin. apply Hin_notbound in Hin.
        inversion Hin; auto.
      - intros x Hfreein; apply Hfree; solve [constructor; auto]. }
    apply Qeq_bool_neq in Hq1.
    assert (H0: a + c == 1).
    { apply IHt1; auto.
      - intros x Hin. apply Hin_notbound in Hin.
        inversion Hin; auto.
      - intros x Hfreein.
        apply Hfree; solve [constructor; auto]. }
    assert (H1: b + d == 1).
    { apply IHt2; auto.
      - intros x Hin. apply Hin_notbound in Hin.
        inversion Hin; auto.
      - intros x Hfreein.
        apply Hfree; solve [constructor; auto]. }
    nra.
  - destruct (Qeq_bool (infer_fail n t) 1) eqn:HQeq.
    + apply Qeq_bool_eq in HQeq.
      unfold flip. simpl.
      rewrite sum_Q_list_map_div_scalar.
      rewrite HQeq, Qminus_cancel, Qdiv_0_den; lra.
    + apply Qeq_bool_neq in HQeq.
      unfold flip; simpl.
      rewrite sum_Q_list_map_div_scalar.
      rewrite Qdiv_combine_terms.
      apply ratio_Qeq_sum; auto.
      cut (sum_Q_list (map (fun x => infer_fail x t) (n :: l)) + infer_f_lib (const 1) t == 1).
      { simpl; lra. }
      inversion Hwf; subst.
      apply IHt; auto.
      * intros x []; subst; auto.
        apply Hin_notbound in H; inversion H; subst; auto.
      * intros x Hfreein.
        destruct (Nat.eqb_spec x n); subst; try solve[left; auto].
        right; apply Hfree; constructor; auto.
      * constructor; auto.
        intro Hin; apply Hin_notbound in Hin.
        inversion Hin; subst; congruence.
Qed.

(* Lemma infer_f_lib_fail_1 {A : Type} (t : tree A) (l : list nat) : *)
(*   wf_tree t -> *)
(*   (forall x : nat, In x l -> not_bound_in x t) -> *)
(*   (forall x, free_in x t -> In x l) -> *)
(*   NoDup l -> *)
(*   sum_Q_list (map (flip infer_fail t) l) + infer_f_lib (const 1) t == 1. *)
(* Proof. *)
(*   revert l; induction t; simpl; intros l Hwf Hin_notbound Hfree Hnodup. *)
(*   - unfold flip; simpl; rewrite sum_Q_list_map_const_0; reflexivity. *)
(*   - rewrite Qplus_0_r. unfold flip. simpl. *)
(*     specialize (Hfree n (free_in_fail n)). *)
(*     apply in_nodup_sum_Q_list; auto. *)
(*   - unfold flip. simpl. *)
(*     rewrite sum_Q_list_map_plus. *)
(*     rewrite 2!sum_Q_list_map_mult_scalar. *)
(*     inversion Hwf; subst. *)
(*     set (a := sum_Q_list (map (fun x : nat => infer_fail x t1) l)). *)
(*     set (b := sum_Q_list (map (fun x : nat => infer_fail x t2) l)). *)
(*     set (c := infer_f_lib (const 1) t1). *)
(*     set (d := infer_f_lib (const 1) t2). *)
(*     assert (H0: a + c == 1). *)
(*     { apply IHt1; auto. *)
(*       - intros x Hin. apply Hin_notbound in Hin. *)
(*         inversion Hin; auto. *)
(*       - intros x Hfreein. *)
(*         apply Hfree; solve [constructor; auto]. } *)
(*     assert (H1: b + d == 1). *)
(*     { apply IHt2; auto. *)
(*       - intros x Hin. apply Hin_notbound in Hin. *)
(*         inversion Hin; auto. *)
(*       - intros x Hfreein. *)
(*         apply Hfree; solve [constructor; auto]. } *)
(*     nra. *)
(*   - destruct (Qeq_bool (infer_fail n t) 1) eqn:HQeq. *)
(*     + apply Qeq_bool_eq in HQeq. *)
(*       unfold flip. simpl. *)
(*       rewrite sum_Q_list_map_div_scalar. *)
(*       rewrite HQeq, Qminus_cancel, Qdiv_0_den; lra. *)
(*     + apply Qeq_bool_neq in HQeq. *)
(*       unfold flip; simpl. *)
(*       rewrite sum_Q_list_map_div_scalar. *)
(*       rewrite Qdiv_combine_terms. *)
(*       apply ratio_Qeq_sum; auto. *)
(*       cut (sum_Q_list (map (fun x => infer_fail x t) (n :: l)) + infer_f_lib (const 1) t == 1). *)
(*       { simpl; lra. } *)
(*       inversion Hwf; subst. *)
(*       apply IHt; auto. *)
(*       * intros x []; subst; auto. *)
(*         apply Hin_notbound in H; inversion H; subst; auto. *)
(*       * intros x Hfreein. *)
(*         destruct (Nat.eqb_spec x n); subst; try solve[left; auto]. *)
(*         right; apply Hfree; constructor; auto. *)
(*       * constructor; auto. *)
(*         intro Hin; apply Hin_notbound in Hin. *)
(*         inversion Hin; subst; congruence. *)
(* Qed. *)

(* Lemma infer_f_lib_fail_1 {A : Type} (t : tree A) (l : list nat) : *)
(*   wf_tree t -> *)
(*   (* (forall x : nat, In x l -> not_bound_in x t) -> *) *)
(*   (forall x, free_in x t -> In x l) -> *)
(*   NoDup l -> *)
(*   sum_Q_list (map (flip infer_fail t) l) + infer_f_lib (const 1) t == 1. *)
(* Proof. *)
(*   revert l; induction t; simpl; intros l Hwf Hfree Hnodup. *)
(*   - unfold flip; simpl; rewrite sum_Q_list_map_const_0; reflexivity. *)
(*   - rewrite Qplus_0_r. unfold flip. simpl. *)
(*     specialize (Hfree n (free_in_fail n)). *)
(*     apply in_nodup_sum_Q_list; auto. *)
(*   - unfold flip. simpl. *)
(*     rewrite sum_Q_list_map_plus. *)
(*     rewrite 2!sum_Q_list_map_mult_scalar. *)
(*     inversion Hwf; subst. *)
(*     set (a := sum_Q_list (map (fun x : nat => infer_fail x t1) l)). *)
(*     set (b := sum_Q_list (map (fun x : nat => infer_fail x t2) l)). *)
(*     set (c := infer_f_lib (const 1) t1). *)
(*     set (d := infer_f_lib (const 1) t2). *)
(*     assert (H0: a + c == 1). *)
(*     { apply IHt1; auto. *)
(*       (* - intros x Hin. apply Hin_notbound in Hin. *) *)
(*       (*   inversion Hin; auto. *) *)
(*       - intros x Hfreein. *)
(*         apply Hfree; solve [constructor; auto]. } *)
(*     assert (H1: b + d == 1). *)
(*     { apply IHt2; auto. *)
(*       (* - intros x Hin. apply Hin_notbound in Hin. *) *)
(*       (*   inversion Hin; auto. *) *)
(*       - intros x Hfreein. *)
(*         apply Hfree; solve [constructor; auto]. } *)
(*     nra. *)
(*   - destruct (Qeq_bool (infer_fail n t) 1) eqn:HQeq. *)
(*     + apply Qeq_bool_eq in HQeq. *)
(*       unfold flip. simpl. *)
(*       rewrite sum_Q_list_map_div_scalar. *)
(*       rewrite HQeq, Qminus_cancel, Qdiv_0_den; lra. *)
(*     + apply Qeq_bool_neq in HQeq. *)
(*       unfold flip; simpl. *)
(*       rewrite sum_Q_list_map_div_scalar. *)
(*       rewrite Qdiv_combine_terms. *)
(*       apply ratio_Qeq_sum; auto. *)
(*       cut (sum_Q_list (map (fun x => infer_fail x t) (n :: l)) + infer_f_lib (const 1) t == 1). *)
(*       { simpl; lra. } *)
(*       inversion Hwf; subst. *)
(*       apply IHt; auto. *)
(*       (* * intros x []; subst; auto. *) *)
(*       (*   apply Hin_notbound in H; inversion H; subst; auto. *) *)
(*       * intros x Hfreein. *)
(*         destruct (Nat.eqb_spec x n); subst; try solve[left; auto]. *)
(*         right; apply Hfree; constructor; auto. *)
(*       * constructor; auto. *)
(*         intro Hin; apply Hin_notbound in Hin. *)
(*         inversion Hin; subst; congruence. *)
(* Qed. *)

Lemma infer_f_lib_fail_aux {A : Type} (t : tree A) (f : A -> Q) (m : nat) (l : list nat) :
  wf_tree t ->
  (forall x : nat, In x l -> not_bound_in x t) ->
  NoDup l ->
  not_bound_in m t ->
  sum_Q_list (map (flip infer_fail t) l) == 1 ->
  infer_f_lib f t == 0.
Proof.
  revert l; induction t; simpl; intros l Hwf Hin_notbound Hnodup Hnotbound Hsum.
  - rewrite sum_Q_list_map_const_0 in Hsum; inversion Hsum.
  - reflexivity.
  - inversion Hwf; inversion Hnotbound; subst.
    destruct (Qeq_dec q 0).
    + rewrite q0. rewrite Qmult_0_l, Qplus_0_l, Qminus_0_r, Qmult_1_l.
      eapply IHt2 with (l:=l); auto.
      * eapply in_not_bound_choice2; eauto.
      * rewrite sum_Q_list_proper; eauto.
        unfold flip; intros ?; simpl; rewrite q0; lra.
    + destruct (Qeq_dec q 1).
      * rewrite q0. rewrite Qminus_cancel, Qmult_1_l, Qmult_0_l, Qplus_0_r.
        eapply IHt1 with (l:=l); auto.
        ++ eapply in_not_bound_choice1; eauto.
        ++ rewrite sum_Q_list_proper; eauto.
           unfold flip; intros ?; simpl; rewrite q0; lra.
      * rewrite IHt1 with (l:=l), IHt2 with (l:=l); auto. lra.
        ++ eapply in_not_bound_choice2; eauto.
        ++ apply sum_Q_list_infer_fail_choice_r in Hsum; eauto; try lra.
           ** eapply in_not_bound_choice1; eauto.
           ** eapply in_not_bound_choice2; eauto.
        ++ eapply in_not_bound_choice1; eauto.
        ++ apply sum_Q_list_infer_fail_choice_l in Hsum; eauto; try lra.
           ** eapply in_not_bound_choice1; eauto.
           ** eapply in_not_bound_choice2; eauto.
  - unfold flip in *; simpl in *.
    inversion Hwf; inversion Hnotbound; subst.
    destruct (Qeq_dec (infer_fail n t) 1).
    { (* Hsum is contradictory because the sum must equal 0 *)
      assert (sum_Q_list (map (fun y => infer_fail y t / (1 - infer_fail n t)) l) == 0).
      { erewrite <- sum_Q_list_map_const_0. apply sum_Q_list_proper.
        intro y. rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity. }
      lra. }
    rewrite Qeq_bool_false; auto.
    rewrite IHt with (l:=n::l); auto.
    + apply Qdiv_0_num.
    + intros x [Hin|Hin]; subst; auto.
      apply Hin_notbound in Hin. inversion Hin; subst; auto.
    + constructor; auto. intro HC. apply Hin_notbound in HC.
      inversion HC; subst; congruence.
    + simpl.
      destruct (Qeq_dec (infer_fail n t) 1).
      * rewrite sum_Q_list_proper in Hsum.
        ++ rewrite sum_Q_list_map_const_0 in Hsum; lra.
        ++ intros ?; rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity.
      * rewrite sum_Q_list_map_div_scalar in Hsum.
        ++ rewrite Qplus_comm; apply Qlem_2; auto.
        (* ++ generalize (@infer_fail_le_1 A t n H1 H2); intros; lra. *)
Qed.

Lemma infer_f_lib_fail {A : Type} (t : tree A) (f : A -> Q) (l : nat) :
  wf_tree t ->
  not_bound_in l t ->
  infer_fail l t == 1 ->
  infer_f_lib f t == 0.
Proof.
  intros Hwf Hnotbound Heq.
  eapply infer_f_lib_fail_aux with (l0:=[l]); auto.
  - intros x Hin. destruct Hin; subst; auto; contradiction.
  - constructor; auto; constructor.
  - apply Hnotbound.
  - simpl; unfold flip; rewrite Heq; reflexivity.
Qed.

Lemma not_bound_in_infer_fail_tree_bind t e n m :
  n <> m ->
  not_bound_in m t ->
  infer_fail n (tree_bind t (fun st => if e st : bool then Fail St m else Leaf st)) ==
  infer_fail n t.
Proof.
  revert n m e.
  induction t; intros n0 m e Hneq Hnotbound;
    unfold tree_bind in *; simpl; inversion Hnotbound; subst.
  - destruct (e a); simpl.
    destruct (Nat.eqb_spec m n0); subst; congruence. reflexivity.
  - reflexivity.
  - rewrite IHt1; auto; rewrite IHt2; auto; reflexivity.
  - rewrite IHt; auto. rewrite IHt; auto. reflexivity.
Qed.

Lemma infer_fail_tree_bind_infer_f e t m :
  not_in m t ->
  wf_tree t ->
  infer_fail m (tree_bind t (fun st => if e st : bool then Fail St m else Leaf st)) ==
  infer_f (fun st => if e st then 1 else 0) t.
Proof.
  unfold tree_bind; revert e m.
  induction t; intros e m Hnotbound Hwf; simpl;
    inversion Hnotbound; inversion Hwf; subst.
  - destruct (e a); simpl; try rewrite Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb_spec n m); subst; congruence.
  - rewrite IHt1; auto; rewrite IHt2; auto; reflexivity.
  - rewrite IHt; auto.
    generalize (@not_bound_in_infer_fail_tree_bind t e n m (not_eq_sym H2)).
    intro Heq; rewrite Heq.
    + reflexivity.
    + apply bound_in_not_bound_in; intro HC.
      apply not_in_not_bound_and_not_free in H3. destruct H3 as [_ HC'].
      apply bound_in_not_bound_in in HC'; congruence.
Qed.

Lemma infer_f_bind_fail t e f m :
  not_bound_in m t ->
  infer_f (fun st => if e st : bool then 0 else f st) t ==
  infer_f f (tree_bind t (fun st => if e st then Fail St m else Leaf st)).
Proof.
  revert e f m.
  induction t; intros e f m Hnotbound;
    unfold tree_bind; simpl; inversion Hnotbound; subst.
  - destruct (e a); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; eauto; reflexivity.
  - rewrite IHt; eauto.
    generalize (@not_bound_in_infer_fail_tree_bind t e n m (not_eq_sym H2) H3).
    intro Heq; rewrite Heq; reflexivity.
Qed.

Lemma infer_f_lib_bind_fail t e f m :
  not_bound_in m t ->
  infer_f_lib (fun st => if e st : bool then 0 else f st) t ==
  infer_f_lib f (tree_bind t (fun st => if e st then Fail St m else Leaf st)).
Proof.
  revert e f m.
  induction t; intros e f m Hnotbound;
    unfold tree_bind; simpl; inversion Hnotbound; subst.
  - destruct (e a); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; eauto; reflexivity.
  - destruct (Qeq_dec (infer_fail n t) 1).
    + rewrite q; simpl.
      destruct (Qeq_dec (infer_fail n (tree_bind t (fun x => if e x then Fail _ m else Leaf x))) 1).
      * unfold tree_bind in q0; rewrite q0; reflexivity.
      * rewrite not_bound_in_infer_fail_tree_bind in n0; auto; congruence.
    + rewrite Qeq_bool_false; auto.
      destruct (Qeq_dec (infer_fail n (tree_bind t (fun x => if e x then Fail _ m else Leaf x))) 1).
      * rewrite not_bound_in_infer_fail_tree_bind in q; auto; congruence.
      * rewrite Qeq_bool_false; auto.
        rewrite IHt; eauto.
        generalize (@not_bound_in_infer_fail_tree_bind t e n m (not_eq_sym H2) H3).
        intro Heq; rewrite Heq; reflexivity.
Qed.

Instance Proper_infer_f {A : Type}
  : Proper ((@f_Qeq A) ==> eq ==> Qeq) infer_f.
Proof.
  intros f g Hfeq ? t ?; subst; revert f g Hfeq.
  induction t; intros f g Hfeq; simpl; auto.
  - reflexivity.
  - rewrite IHt1, IHt2; eauto; reflexivity.
  - rewrite IHt; eauto; reflexivity.
Qed.

Lemma infer_f_proper {A : Type} (t : tree A) (f g : A -> Q) :
  f ==f g ->
  infer_f f t == infer_f g t.
Proof. intros; apply Proper_infer_f; auto. Qed.

Instance Proper_infer_f_lib {A : Type}
  : Proper ((@f_Qeq A) ==> eq ==> Qeq) infer_f_lib.
  intros f g Hfeq ? t ?; subst; revert f g Hfeq.
  induction t; intros f g Hfeq; simpl; auto.

  - reflexivity.
  - rewrite IHt1, IHt2; eauto; reflexivity.
  - destruct (Qeq_dec (infer_fail n t) 1).
    + rewrite q; reflexivity.
    + rewrite Qeq_bool_false; auto; rewrite IHt; eauto; reflexivity.
Qed.

Lemma infer_f_lib_proper {A : Type} (t : tree A) (f g : A -> Q) :
  f ==f g ->
  infer_f_lib f t == infer_f_lib g t.
Proof. intros; apply Proper_infer_f_lib; auto. Qed.

(* Lemma all_support_true_infer_f (e : St -> bool) (f g : St -> Q) (t : tree St) : *)
(*   wf_tree t -> *)
(*   all_support (fun x => e x = true) t -> *)
(*   infer_f (fun x => if e x then f x else g x) t == *)
(*   infer_f f t. *)
(* Proof. *)
(*   induction t; intros Hwf Hsupp; inversion Hwf; subst; simpl. *)
(*   - inversion Hsupp; subst. rewrite H0; reflexivity. *)
(*   - reflexivity. *)
(*   - inversion Hsupp; subst. *)
(*     + rewrite H1, 2!Qmult_0_l, 2!Qplus_0_l, Qminus_0_r, 2!Qmult_1_l. *)
(*       apply IHt2; auto. *)
(*     + rewrite H1, Qmult_1_l, Qminus_cancel, *)
(*       2!Qmult_0_l, Qmult_1_l, 2!Qplus_0_r. *)
(*       apply IHt1; auto. *)
(*     + rewrite IHt1, IHt2; auto; reflexivity. *)
(*   - inversion Hsupp; subst. *)
(*     rewrite IHt; auto; reflexivity. *)
(* Qed. *)

Lemma infer_f_bind_fail_f_neg (e : exp) t f n :
  not_bound_in n t ->
  infer_f f (tree_bind t (fun x => if e x then Fail St n else Leaf x)) ==
  infer_f (fun x => if e x then 0 else f x) t.
Proof.
  unfold tree_bind.
  revert e f n. induction t; intros e f m Hnotbound; simpl.
  - destruct (e a); reflexivity.
  - reflexivity.
  - inversion Hnotbound; subst; rewrite IHt1, IHt2; auto; reflexivity.
  - inversion Hnotbound; subst.
    rewrite IHt; auto.
    generalize (@not_bound_in_infer_fail_tree_bind t e n m (not_eq_sym H2) H3).
    intro Heq; rewrite Heq; reflexivity.
Qed.

Lemma infer_f_lib_bind_fail_f_neg (e : exp) t f n :
  not_bound_in n t ->
  infer_f_lib f (tree_bind t (fun x => if e x then Fail St n else Leaf x)) ==
  infer_f_lib (fun x => if e x then 0 else f x) t.
Proof.
  unfold tree_bind.
  revert e f n. induction t; intros e f m Hnotbound; simpl.
  - destruct (e a); reflexivity.
  - reflexivity.
  - inversion Hnotbound; subst; rewrite IHt1, IHt2; auto; reflexivity.
  - inversion Hnotbound; subst.
      generalize (@not_bound_in_infer_fail_tree_bind t e n m (not_eq_sym H2) H3).
      intro Heq.
    destruct (Qeq_dec (infer_fail n (join (fmap (fun x : St => if e x then Fail St m else Leaf x) t))) 1).
    + rewrite <- Heq, q; simpl; rewrite q; reflexivity.
    + rewrite Qeq_bool_false; auto.
      destruct (Qeq_dec (infer_fail n t) 1).
      { rewrite q in Heq. unfold tree_bind in Heq. congruence. }
      rewrite Qeq_bool_false; auto.
      rewrite IHt; auto.
      rewrite Heq; reflexivity.
Qed.

(* Instance monotone_infer_f {A : Type} (f : A -> Q) (Hexp : expectation f) *)
(*   : Proper (tree_leq ==> Qle) (infer_f f). *)
(* Proof. *)
(*   intros t1 t2 Hleq. *)
(*   induction Hleq; simpl. *)
(*   - lra. *)
(*   - apply infer_f_expectation_0_le; auto. *)

(* Lemma monotone_infer_f {A : Type} (f : A -> Q) (t1 t2 : tree A) : *)
(*   wf_tree t1 -> wf_tree t2 -> *)
(*   expectation f -> *)
(*   tree_leq t1 t2 -> *)
(*   infer_f f t1 <= infer_f f t2. *)
(* Proof. *)
(*   intros Hwf1 Hwf2 Hexp Hleq. *)
(*   induction Hleq; simpl. *)
(*   - lra. *)
(*   - apply infer_f_expectation_0_le; auto. *)
(*   - inversion Hwf1; inversion Hwf2; subst. *)
(*     specialize (IHHleq1 H4 H10). *)
(*     specialize (IHHleq2 H5 H11). *)
(*     rewrite H; nra. *)
(*   - inversion Hwf1; inversion Hwf2; subst. *)
(*     specialize (IHHleq H1 H5). *)

(* Lemma nondivergent_infer_fail_lt_1 {A : Type} (n : nat) (t : tree A) : *)
(*   nondivergent t -> *)
(*   wf_tree t -> *)
(*   infer_fail n t < 1. *)
(* Proof. *)
(*   intros Hnd. induction Hnd; intro Hwf; simpl; inversion Hwf; subst. *)
(*   - lra. *)
(*   - rewrite H; apply IHHnd in H5; lra. *)
(*   - rewrite H; apply IHHnd in H4; lra. *)
(*   - apply IHHnd1 in H5; apply IHHnd2 in H6; nra. *)
(*   - assert (infer_fail n0 t <= 1). *)
(*     { apply infer_fail_le_1; auto. } *)

(* Lemma nondivergent'_infer_fail_sum_lt_1 {A : Type} (t : tree A) *)
(*       (l : list nat) : *)
(*   (forall m, t <> Fail _ m) -> *)
(*   nondivergent' l t -> *)
(*   wf_tree t -> *)
(*   NoDup l -> *)
(*   (forall x, In x l -> not_bound_in x t) -> *)
(*   (* (forall x, bound_in x t -> ~ In x lbls) -> *) *)
(*   sum_Q_list (map (fun n => infer_fail n t) l) < 1. *)
(* Proof. *)
(*   revert l. induction t; intros l Hneq Hnd Hwf Hnodup Hnotbound; simpl. *)
(*   - induction l; simpl. *)
(*     + lra. *)
(*     + inversion Hnodup; subst. *)
(*       apply IHl in H2. lra. *)
(*       constructor. *)
(*       intros; apply Hnotbound; right; auto. *)
(*   - specialize (Hneq n); congruence. *)
(*     (* inversion Hnd; subst. *) *)
(*     (* apply Hnotbound in H1.  *) *)
(*   - rewrite sum_Q_list_map_plus, 2!sum_Q_list_map_mult_scalar. *)
(*     inversion Hwf; subst. *)
(*     inversion Hnd; subst. *)
(*     + rewrite H5; field_simplify; rewrite 2!Qdiv_1_den. *)
(*       apply IHt2; auto. *)
(*       * intros m Heq; subst. *)
(*         inversion H7; subst. *)
(*       * intros x Hin. *)
(*         apply Hnotbound in Hin; inversion Hin; subst; auto. *)
(*     + rewrite H5; field_simplify; rewrite 2!Qdiv_1_den. *)
(*       apply IHt1; auto; intros x Hin. *)
(*       apply Hnotbound in Hin; inversion Hin; subst; auto. *)
(*     + assert (Ht1: forall x, In x l -> not_bound_in x t1). *)
(*       { intros x Hin; specialize (Hnotbound x Hin). *)
(*         inversion Hnotbound; subst; auto. } *)
(*       assert (Ht2: forall x, In x l -> not_bound_in x t2). *)
(*       { intros x Hin; specialize (Hnotbound x Hin). *)
(*         inversion Hnotbound; subst; auto. } *)
(*       specialize (IHt1 l H8 H3 Hnodup Ht1). *)
(*       specialize (IHt2 l H9 H4 Hnodup Ht2). *)
(*       nra. *)
(*   - inversion Hwf; subst. *)
(*     inversion Hnd; subst. *)
(*     assert (~ In n l). *)
(*     { intro HC. apply Hnotbound in HC. inversion HC; subst. congruence. } *)
(*     assert (Hlt: sum_Q_list (map (fun n => infer_fail n t) [n]) < 1). *)
(*     { apply IHt; auto. *)
(*       - constructor; auto; constructor. *)
(*       - intros x Hin. inversion Hin; subst; auto. *)
(*         inversion H3. } *)
(*     simpl in Hlt. rewrite Qplus_0_r in Hlt. *)
(*     rewrite sum_Q_list_map_div_scalar; try lra. *)
(*     apply Qlt_shift_div_r; try lra. *)
(*     rewrite Qmult_1_l. *)
(*     assert (Hnodup': NoDup (n :: l)). *)
(*     { constructor; auto. } *)
(*     apply IHt in Hnodup'; auto. *)
(*     + simpl in Hnodup'. lra. *)
(*     + intros x Hin. inversion Hin; subst; auto. *)
(*       apply Hnotbound in H3. inversion H3; subst; auto. *)
(* Qed. *)

Lemma nondivergent_infer_fail_sum_lt_1 {A : Type} (t : tree A) (l : list nat) :
  nondivergent t ->
  wf_tree t ->
  NoDup l ->
  (forall x, In x l -> not_bound_in x t) ->
  sum_Q_list (map (fun n => infer_fail n t) l) < 1.
Proof.
  revert l. induction t; intros l Hnd Hwf Hnodup Hnotbound; simpl.
  - induction l; simpl.
    + lra.
    + inversion Hnodup; subst.
      apply IHl in H2. lra.
      intros; apply Hnotbound; right; auto.
  - inversion Hnd.
  - rewrite sum_Q_list_map_plus, 2!sum_Q_list_map_mult_scalar.
    inversion Hwf; subst.
    inversion Hnd; subst.
    + rewrite H1; field_simplify; apply IHt2; auto; intros x Hin.
      apply Hnotbound in Hin; inversion Hin; subst; auto.
    + rewrite H1; field_simplify; apply IHt1; auto; intros x Hin.
      apply Hnotbound in Hin; inversion Hin; subst; auto.
    + assert (Ht1: forall x, In x l -> not_bound_in x t1).
      { intros x Hin; specialize (Hnotbound x Hin).
        inversion Hnotbound; subst; auto. }
      assert (Ht2: forall x, In x l -> not_bound_in x t2).
      { intros x Hin; specialize (Hnotbound x Hin).
        inversion Hnotbound; subst; auto. }
      destruct H7 as [H7 | H7].
      * specialize (IHt1 l H7 H3 Hnodup Ht1).
        assert (sum_Q_list (map (fun n => infer_fail n t2) l) <= 1).
        { apply infer_fail_sum_le_1; auto. }
        nra.
      * specialize (IHt2 l H7 H4 Hnodup Ht2).
        assert (sum_Q_list (map (fun n => infer_fail n t1) l) <= 1).
        { apply infer_fail_sum_le_1; auto. }
        nra.
      (* specialize (IHt1 l H7 H3 Hnodup Ht1). *)
      (* specialize (IHt2 l H8 H4 Hnodup Ht2). *)
      (* nra. *)
  - inversion Hwf; subst.
    inversion Hnd; subst.
    assert (~ In n l).
    { intro HC. apply Hnotbound in HC. inversion HC; subst. congruence. }
    assert (Hlt: sum_Q_list (map (fun n => infer_fail n t) [n]) < 1).
    { apply IHt; auto.
      - constructor; auto; constructor.
      - intros x Hin. inversion Hin; subst; auto.
        inversion H3. }
    simpl in Hlt. rewrite Qplus_0_r in Hlt.
    rewrite sum_Q_list_map_div_scalar; try lra.
    apply Qlt_shift_div_r; try lra.
    rewrite Qmult_1_l.
    assert (Hnodup': NoDup (n :: l)).
    { constructor; auto. }
    apply IHt in Hnodup'; auto.
    + simpl in Hnodup'. lra.
    + intros x Hin. inversion Hin; subst; auto.
      apply Hnotbound in H3. inversion H3; subst; auto.
Qed.

Lemma nondivergent_infer_fail_lt_1 {A : Type} (t : tree A) (n : nat) :
  nondivergent t ->
  wf_tree t ->
  not_bound_in n t ->
  infer_fail n t < 1.
Proof.
  intros Hnd Hwf Hnotbound.
  assert (Hnodup: NoDup [n]).
  { constructor; auto; constructor. }
  assert (H: forall x, In x [n] -> not_bound_in x t).
  { intros x [Hin | ?]; subst; auto; inversion H. }
  generalize (nondivergent_infer_fail_sum_lt_1 Hnd Hwf Hnodup H); simpl; lra.
Qed.

(** Not true after changing nondivergent (choice case 3). *)
(* Lemma nondivergent_infer_f_infer_f_lib {A : Type} (f : A -> Q) (t : tree A) : *)
(*   nondivergent t -> *)
(*   wf_tree t -> *)
(*   infer_f f t == infer_f_lib f t. *)
(* Proof. *)
(*   induction t; intros Hnd Hwf; simpl; try lra. *)
(*   - inversion Hwf; subst; inversion Hnd; subst. *)
(*     + rewrite H1, IHt2; auto; lra. *)
(*     + rewrite H1, IHt1; auto; lra. *)
(*     + rewrite IHt1, IHt2; auto; lra. *)
(*   - inversion Hwf; inversion Hnd; subst. *)
(*     destruct (Qeq_dec (infer_fail n t) 1). *)
(*     + generalize (@nondivergent_infer_fail_lt_1 _ t n H4 H1 H2); lra. *)
(*     + rewrite IHt; auto. rewrite Qeq_bool_false; auto; reflexivity. *)
(* Qed. *)

(** infer_f and infer_f_lib coincide on "perfect" trees. Really only
  nondivergence is necessary, and "perfect" is stronger. *)
Lemma perfect_infer_f_infer_f_lib {A : Type} (f : A -> Q) (t : tree A) :
  perfect t ->
  infer_f f t == infer_f_lib f t.
Proof.
  induction 1; simpl; try lra.
  rewrite IHperfect1, IHperfect2; lra.
Qed.

(* Lemma nondivergent_no_fix_infer_fail_lt_1 {A : Type} (n : nat) (t : tree A) : *)
(*   not_bound_in n t -> *)
(*   wf_tree t -> *)
(*   nondivergent t -> *)
(*   no_fix t -> *)
(*   infer_fail n t < 1. *)
(* Proof. intros; apply nondivergent_infer_fail_lt_1; auto. Qed. *)
(*   induction t; intros Hnotbound Hwf Hnd Hnf; simpl; *)
(*     inversion Hwf; inversion Hnotbound; subst. *)
(*   - lra. *)
(*   - inversion Hnd. *)
(*   - inversion Hnf; inversion Hnd; subst. *)
(*     + rewrite H11; specialize (IHt2 H10 H4 H13 H6); lra. *)
(*     + rewrite H11; specialize (IHt1 H8 H3 H13 H1); lra. *)
(*     + destruct H14 as [H14 | H14]. *)
(*       * specialize (IHt1 H8 H3 H14 H1). *)
(*         assert (infer_fail n t2 <= 1). *)
(*         { apply infer_fail_le_1; auto. } *)
(*         nra. *)
(*       * specialize (IHt2 H10 H4 H14 H6). *)
(*         assert (infer_fail n t1 <= 1). *)
(*         { apply infer_fail_le_1; auto. } *)
(*         nra. *)
(*   - inversion Hnf. *)
(* Qed. *)

Lemma infer_f_bind_choice {A : Type} (f : A -> Q) (t : tree bool) (t1 t2 : tree A) :
  (forall (n : nat) (x : bool), bound_in n t -> not_in n (if x then t1 else t2)) ->
  infer_f f (bind t (fun b => if b : bool then t1 else t2)) ==
  infer_f (fun b => if b : bool then 1 else 0) t * infer_f f t1 +
  infer_f (fun b => if b : bool then 0 else 1) t * infer_f f t2.
Proof.
  intros Hnotin.
  rewrite <- infer_f_bind; auto.
  unfold compose; induction t; simpl.
  - destruct a; lra.
  - lra.
  - rewrite IHt1, IHt2; try lra;
      intros; apply Hnotin; solve [constructor; auto].
  - rewrite IHt.
    + destruct (Qeq_dec (infer_fail n t) 1).
      * rewrite q, Qminus_cancel, 3!Qdiv_0_den; lra.
      * field; lra.
    + intros; apply Hnotin.
      destruct (Nat.eqb_spec n0 n); subst; constructor; auto.
Qed.

Lemma infer_f_lib_bind_choice {A : Type} (f : A -> Q) (t : tree bool) (t1 t2 : tree A) :
  (forall (n : nat) (x : bool), bound_in n t -> not_in n (if x then t1 else t2)) ->
  infer_f_lib f (bind t (fun b => if b : bool then t1 else t2)) ==
  infer_f_lib (fun b => if b : bool then 1 else 0) t * infer_f_lib f t1 +
  infer_f_lib (fun b => if b : bool then 0 else 1) t * infer_f_lib f t2 -
  infer_f_lib (const 0) t * (infer_f_lib f t1 + infer_f_lib f t2) +
  infer_f_lib (const 0) t.
Proof.
  intros Hnotin.
  rewrite <- infer_f_lib_bind; auto.
  unfold compose; induction t; simpl.
  - unfold const; destruct a; lra.
  - lra.
  - rewrite IHt1, IHt2; try lra;
      intros; apply Hnotin; solve [constructor; auto].
  - destruct (Qeq_dec (infer_fail n t) 1).
    + rewrite q; simpl; rewrite 3!Qmult_1_l;lra.
    + rewrite Qeq_bool_false; auto.
      rewrite IHt.
      * field; lra.
      * intros; apply Hnotin.
        destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
Qed.

Lemma infer_fail_bind_choice {A : Type} (t : tree bool) (t1 t2 : tree A) (lbl : nat) :
  (forall (n : nat) (x : bool), bound_in n t -> not_in n (if x then t1 else t2)) ->
  not_in lbl t ->
  infer_fail lbl (bind t (fun b => if b : bool then t1 else t2)) ==
  (infer_f (fun b => if b : bool then 1 else 0) t) * infer_fail lbl t1 +
  (infer_f (fun b => if b : bool then 0 else 1) t) * infer_fail lbl t2.
Proof.
  intros Hnotin Hnotin'.
  rewrite <- infer_fail_bind; auto.
  unfold compose; induction t; simpl; inversion Hnotin'; subst.
  - destruct a; lra.
  - lra.
  - rewrite IHt1, IHt2; auto; try lra;
      intros; apply Hnotin; solve [constructor; auto].
  - rewrite IHt; auto.
    + destruct (Qeq_dec (infer_fail n t) 1).
      * rewrite q, Qminus_cancel, 3!Qdiv_0_den; lra.
      * field; lra.
    + intros; apply Hnotin.
      destruct (Nat.eqb_spec n0 n); subst; constructor; auto.
Qed.

Lemma infer_f_linear {A : Type} (f g : A -> Q) (t : tree A) :
  infer_f (fun x => f x + g x) t == infer_f f t + infer_f g t.
Proof.
  induction t; simpl; try lra.
  - rewrite IHt1, IHt2; lra.
  - rewrite IHt.
    destruct (Qeq_dec (infer_fail n t) 1).
    + rewrite q, Qminus_cancel, 3!Qdiv_0_den; lra.
    + field; lra.
Qed.

Lemma infer_f_lib_linear {A : Type} (f g : A -> Q) (t : tree A) :
  infer_f_lib (fun x => f x + g x) t ==
  infer_f_lib f t + infer_f_lib g t - infer_f_lib (const 0) t.
Proof.
  unfold const; induction t; simpl; try lra.
  - rewrite IHt1, IHt2; lra.
  - destruct (Qeq_dec (infer_fail n t) 1).
    + rewrite Qeq_eq_bool; auto; lra.
    + rewrite Qeq_bool_false; auto.
      rewrite IHt; field; lra.
Qed.

Lemma infer_fail_lt_1 {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  ~ infer_fail n t == 1 ->
  infer_fail n t < 1.
Proof.
  intros Hwf Hnotbound Hneq.
  assert (infer_fail n t <= 1).
  { apply infer_fail_le_1; auto. }
  lra.
Qed.

(** Here we define "infer_mixed", which is a single function that
  subsumes infer_f and infer_fail but operates on trees in which the
  leaves contain sum types, fail nodes have been replaced by inl
  leaves, and leaves replaced by inr leaves.

  We prove the obvious connections to infer_f and infer_fail. The
  whole point is to aid in the proof of [infer_f_bounded]. By using
  infer_mixed, we can make the induction hypothesis in
  [infer_mixed_disjoint_le_1] sufficiently general. *)

Definition lbl_indicator {A : Type} (n : nat) (x : nat + A) : Q :=
  match x with
  | inl m => if m =? n then 1 else 0
  | inr _ => 0
  end.

Definition mixf {A B : Type} : (B -> Q) -> A + B -> Q :=
  cotuple (const 0).

Fixpoint infer_mixed {A : Type} (f : nat + A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf x => f (inr x)
  | Fail _ n => f (inl n)
  | Choice p t1 t2 => p * infer_mixed f t1 + (1-p) * infer_mixed f t2
  | Fix m t1 =>
    let a := infer_mixed f t1 in
    let b := infer_mixed (lbl_indicator m) t1 in
    a / (1 - b)
  end.

Fixpoint infer_mixed' {A : Type} (f : nat + A -> Q) (t : tree (nat + A)) : Q :=
  match t with
  | Leaf x => f x
  | Fail _ n => 0
  | Choice p t1 t2 => p * infer_mixed' f t1 + (1-p) * infer_mixed' f t2
  | Fix m t1 =>
    let a := infer_mixed' f t1 in
    let b := infer_mixed' (lbl_indicator m) t1 in
    a / (1 - b)
  end.

Fixpoint defail {A : Type} (t : tree A) : tree (nat + A) :=
  match t with
  | Leaf x => Leaf (inr x)
  | Fail _ n => Leaf (inl n)
  | Choice p t1 t2 => Choice p (defail t1) (defail t2)
  | Fix n t1 => Fix n (defail t1)
  end.

Lemma defail_no_fail {A : Type} (t : tree A) :
  no_fail (defail t).
Proof. induction t; constructor; auto. Qed.

Lemma infer_mixed_infer_fail {A : Type} (t : tree A) (n : nat) :
  infer_mixed (lbl_indicator n) t == infer_fail n t.
Proof.
  revert n.
  induction t; simpl; intro m; try reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite 2!IHt; reflexivity.
Qed.

Lemma infer_mixed'_infer_fail {A : Type} (t : tree A) (n : nat) :
  infer_mixed' (lbl_indicator n) (defail t) == infer_fail n t.
Proof.
  revert n.
  induction t; simpl; intro m; try reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite 2!IHt; reflexivity.
Qed.

Lemma infer_mixed'_infer_f {A : Type} (t : tree A) (f : A -> Q) :
  infer_mixed' (mixf f) (defail t) == infer_f f t.
Proof.
  revert f.
  induction t; simpl; intro f; try reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite infer_mixed'_infer_fail, IHt; reflexivity.
Qed.

Lemma infer_mixed_infer_f {A : Type} (t : tree A) (f : A -> Q) :
  infer_mixed (mixf f) t ==
  infer_f f t.
Proof.
  induction t; simpl; try reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt, infer_mixed_infer_fail; reflexivity.
Qed.

Lemma infer_mixed'_lbl_indicator {A B : Type}
      (n : nat) (t : tree (nat + A)) (k : nat + A -> tree (nat + B)) :
  (forall n, k (inl n) = Leaf (inl n)) ->
  (forall x, infer_mixed' (lbl_indicator n) (k x) == 0) ->
  infer_mixed' (fun x : nat + A => infer_mixed' (lbl_indicator n) (k x)) t ==
  infer_mixed' (lbl_indicator n) t.
Proof.
  induction t; intros Hleaf H0.
  - simpl; destruct a.
    + rewrite Hleaf; reflexivity.
    + rewrite H0; reflexivity.
  - reflexivity.
  - simpl; rewrite IHt1, IHt2; auto; reflexivity.
  - simpl; rewrite IHt; auto; reflexivity.
Qed.

Lemma infer_mixed'_bind {A B : Type}
      (f : (nat + B) -> Q) (t : tree (nat + A)) (k : (nat + A) -> tree (nat + B)) :
  (forall n, k (inl n) = Leaf (inl n)) ->
  (forall n x, bound_in n t -> infer_mixed' (lbl_indicator n) (k x) == 0) ->
  (* (forall n x, bound_in n t -> ~ in_tree (inl n) (k x)) -> *)
  infer_mixed' (infer_mixed' f ∘ k) t == infer_mixed' f (tree_bind t k).
Proof.
  unfold compose, tree_bind.
  revert f k.
  induction t; simpl; intros f k Hleaf H0; try reflexivity.
  - rewrite <- IHt1, <- IHt2; try lra; auto;
      intros n x Hbound; apply H0; solve [constructor; auto].
  - rewrite IHt; auto.
    + assert (H: infer_mixed' (lbl_indicator n) (join (fmap k t)) ==
                 infer_mixed' (fun x => infer_mixed' (lbl_indicator n) (k x)) t).
      { rewrite IHt; auto; try reflexivity;
          intros m x Hbound; apply H0;
            destruct (Nat.eqb_spec m n); subst; constructor; auto. }
      rewrite H.
      rewrite infer_mixed'_lbl_indicator; auto; try reflexivity.
      intro x; apply H0; constructor.
    + intros m x Hbound; apply H0;
        destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Definition mixed_bind {A B : Type}
           (t : tree (nat + A)) (k : A -> tree (nat + B)) : tree (nat + B) :=
  tree_bind t (fun x => match x with
                     | inl n => Leaf (inl n)
                     | inr a => k a
                     end).

(** Functions f and g are "disjoint". *)
Definition disjoint {A : Type} (f g : A -> Q) :=
  forall x, (0 < f x -> g x == 0) /\ (0 < g x -> f x == 0).

Lemma infer_mixed_disjoint_le_1 {A : Type} (l : list (nat + A -> Q)) (t : tree A) :
  wf_tree t ->
  NoDup l ->
  (forall f g, In f l -> In g l -> f <> g -> disjoint f g) ->
  (forall f, In f l -> bounded f 1) ->
  (forall lbl, bound_in lbl t -> forall f, In f l -> f (inl lbl) == 0) ->
  sum_Q_list (map (fun f => infer_mixed f t) l) <= 1.
Proof.
  revert l.
  induction t; simpl; intros l Hwf Hnodup Hdisjoint Hbounded Hboundin.
  - induction l; simpl; try lra.
    rename a0 into f.
    destruct (Qlt_le_dec 0 (f (inr a))).
    + assert (H: sum_Q_list (map (fun g => g (inr a)) l) == 0).
      { clear IHl Hbounded.
        induction l; simpl.
        - reflexivity.
        - rename a0 into g.
          apply (Hdisjoint f g) in q.
          + rewrite q. rewrite Qplus_0_l.
            apply IHl.
            * inversion Hnodup; subst.
              inversion H2; subst.
              constructor; auto.
              intro HC; apply H1; right; auto.
            * intros f' g' Hinf Hing Hneq.
              apply Hdisjoint; auto.
              -- destruct Hinf; subst.
                 ++ left; auto.
                 ++ right; right; auto.
              -- destruct Hing; subst.
                 ++ left; auto.
                 ++ right; right; auto.
            * intros ? Hbound. inversion Hbound.
          + left; auto.
          + right; left; auto.
          + eapply nodup_not_equal; eauto. }
      rewrite H, Qplus_0_r.
      apply Hbounded; left; auto.
    + cut (sum_Q_list (map (fun g => g (inr a)) l) <= 1).
      { lra. }
      apply IHl.
      * inversion Hnodup; auto.
      * intros g h Hing Hinh. apply Hdisjoint; right; auto.
      * intros g Hin; apply Hbounded; right; auto.
      * intros ? Hbound; inversion Hbound.
  - induction l; simpl; try lra.
    rename a into f.
    destruct (Qlt_le_dec 0 (f (inl n))).
    + assert (H: sum_Q_list (map (fun g => g (inl n)) l) == 0).
      { clear IHl Hbounded.
        induction l; simpl.
        - reflexivity.
        - rename a into g.
          apply (Hdisjoint f g) in q.
          + rewrite q. rewrite Qplus_0_l.
            apply IHl.
            * inversion Hnodup; subst.
              inversion H2; subst.
              constructor; auto.
              intro HC; apply H1; right; auto.
            * intros f' g' Hinf Hing Hneq.
              apply Hdisjoint; auto.
              -- destruct Hinf; subst.
                 ++ left; auto.
                 ++ right; right; auto.
              -- destruct Hing; subst.
                 ++ left; auto.
                 ++ right; right; auto.
            * intros ? Hbound; inversion Hbound.
          + left; auto.
          + right; left; auto.
          + eapply nodup_not_equal; eauto. }
      rewrite H, Qplus_0_r.
      apply Hbounded; left; auto.
    + cut (sum_Q_list (map (fun g => g (inl n)) l) <= 1).
      { lra. }
      apply IHl.
      * inversion Hnodup; auto.
      * intros g h Hing Hinh. apply Hdisjoint; right; auto.
      * intros g Hin; apply Hbounded; right; auto.
      * intros ? Hbound; inversion Hbound.
  - rewrite sum_Q_list_map_plus.
    rewrite 2!sum_Q_list_map_mult_scalar.
    inversion Hwf; subst.
    assert (Hboundin1: forall lbl, bound_in lbl t1 ->
                              forall f, In f l -> f (inl lbl) == 0).
    { intros lbl Hbound f Hin.
      apply Hboundin; auto; constructor; auto. }
    assert (Hboundin2: forall lbl, bound_in lbl t2 ->
                              forall f, In f l -> f (inl lbl) == 0).
    { intros lbl Hbound f Hin.
      apply Hboundin; auto; solve [constructor; auto]. }
    specialize (IHt1 l H3 Hnodup Hdisjoint Hbounded Hboundin1).
    specialize (IHt2 l H4 Hnodup Hdisjoint Hbounded Hboundin2).
    nra.
  - destruct (Qeq_dec (infer_mixed (lbl_indicator n) t) 1).
    + apply Qle_trans with 0; try lra.
      rewrite <- sum_Q_list_map_const_0 with (l0:=l).
      apply Qle_lteq; right.
      eapply sum_Q_list_proper.
      intro g; rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity.
    + assert (infer_mixed (lbl_indicator n) t <= 1).
      { inversion Hwf; subst.
        rewrite infer_mixed_infer_fail; apply infer_fail_le_1; auto. }
      rewrite sum_Q_list_map_div_scalar; try lra.
      apply ratio_Qle_sum; try lra.
      rewrite Qmult_1_r.
      inversion Hwf; subst.
      cut (sum_Q_list (map (fun g => infer_mixed g t) (lbl_indicator n :: l)) <= 1).
      { simpl; lra. }
      apply IHt; auto.
      * constructor; auto.
        assert (Hbound: bound_in n (Fix n t)).
        { constructor. }
        intro Hin.
        apply Hboundin with (f:=lbl_indicator n) in Hbound; auto.
        unfold lbl_indicator in Hbound; rewrite Nat.eqb_refl in Hbound; lra.
      * intros g h Hing Hinh Hneq.
        assert (forall g, In g l -> disjoint (lbl_indicator n) g).
        { intros g' Hin' x. split; intro Hlt.
          - unfold lbl_indicator in Hlt; destruct x; try lra.
            + destruct (Nat.eqb_spec n1 n); subst.
              * apply Hboundin; auto; constructor.
              * lra.
          - destruct x.
            + assert (Hneq': n1 <> n).
              { intro HC; subst.
                apply Hboundin with (lbl:=n) in Hin'; try lra; constructor. }
              unfold lbl_indicator.
              apply Nat.eqb_neq in Hneq'; rewrite Hneq'; lra.
            + unfold lbl_indicator; lra. }
        destruct Hing; subst; destruct Hinh; subst.
        ++ congruence.
        ++ apply H0; auto.
        ++ intro x. apply and_comm. apply H0; auto.
        ++ apply Hdisjoint; auto.
      * intros g Hin.
        destruct Hin; subst.
        ++ intros []; simpl; try lra.
           destruct (Nat.eqb_spec n1 n); subst; lra.
        ++ apply Hbounded; auto.
      * intros lbl Hbound g Hin.
        destruct (Nat.eqb_spec lbl n); subst.
        -- apply bound_in_not_bound_in in H3; congruence.
        -- destruct Hin; subst.
           ++ unfold lbl_indicator.
              apply Nat.eqb_neq in n1; rewrite n1; reflexivity.
           ++ apply Hboundin; auto; constructor; auto.
Qed.

Lemma infer_f_bounded {A : Type} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  bounded f 1 ->
  infer_f f t <= 1.
Proof.
  intros Hwf Hbounded.
  rewrite <- infer_mixed_infer_f.
  assert (H: infer_mixed (mixf f) t ==
             sum_Q_list (map (fun h => infer_mixed h t) [mixf f])).
  { simpl; rewrite Qplus_0_r; reflexivity. }
  rewrite H; clear H.
  apply infer_mixed_disjoint_le_1; auto.
  - constructor; intuition; constructor.
  - intros h k Hinh Hink Hneq.
    inversion Hinh; inversion Hink; subst.
    + congruence.
    + inversion H0.
    + inversion H.
    + inversion H.
  - intros h Hin x; inversion Hin; subst.
    + destruct x; simpl; auto; unfold const; lra.
    + inversion H.
  - intros lbl Hbound h Hin.
    destruct Hin; subst; simpl; unfold const; try lra; inversion H.
Qed.

Lemma infer_f_scalar {A : Type} (f : A -> Q) (t : tree A) (a : Q) :
  infer_f (fun x => a * f x) t == a * infer_f f t.
Proof.
  induction t; simpl; try lra.
  - rewrite IHt1, IHt2; lra.
  - rewrite IHt.
    destruct (Qeq_dec (infer_fail n t) 1); subst.
    + rewrite q, Qminus_cancel, 2!Qdiv_0_den; lra.
    + field; lra.
Qed.

(** infer_f preserves [const 0]. *)
Lemma infer_f_const_0 {A : Type} (t : tree A) :
  infer_f (const 0) t == 0.
Proof.
  induction t; simpl; unfold const; try reflexivity.
  - rewrite IHt1, IHt2; lra.
  - rewrite IHt; reflexivity.
Qed.

(** General upper bound. *)
Lemma infer_f_bounded' {A : Type} (f : A -> Q) (t : tree A) (b : Q) :
  0 <= b ->
  wf_tree t ->
  bounded_expectation f b ->
  infer_f f t <= b.
Proof.
  intros Hle Hwf Hboundedexp.
  set (g := fun x => f x / b).
  destruct (Qeq_dec b 0).
  - assert (infer_f f t == 0).
    { rewrite <- infer_f_const_0 with (t0:=t).
      apply Proper_infer_f; auto.
      intro x; unfold const; destruct (Hboundedexp x); lra. }
    lra.
  - assert (Hg: bounded g 1).
    { intro x. unfold g.
      destruct (Hboundedexp x).
      apply Qle_shift_div_r; lra. }
    assert (infer_f f t == infer_f (fun x => b * (f x / b)) t).
    { apply Proper_infer_f; auto.
      intro x; field; auto. }
    rewrite H.
    rewrite infer_f_scalar.
    assert (infer_f g t <= 1).
    { apply infer_f_bounded; auto. }
    unfold g in H0. nra.
Qed.

Lemma tree_eq_infer_fail {A : Type} (t1 t2 : tree A) (n : nat) :
  tree_eq t1 t2 ->
  infer_fail n t1 == infer_fail n t2.
Proof.
  intro Heq. revert n.
  induction Heq; simpl; intro n; try lra.
  - rewrite H, IHHeq1, IHHeq2; reflexivity.
  - rewrite 2!IHHeq; reflexivity.
Qed.

Lemma tree_eq_infer_f {A : Type} (t1 t2 : tree A) (f : A -> Q) :
  tree_eq t1 t2 ->
  infer_f f t1 == infer_f f t2.
Proof.
  induction 1; simpl; try lra.
  - rewrite H, IHtree_eq1, IHtree_eq2; reflexivity.
  - rewrite IHtree_eq, tree_eq_infer_fail; eauto; reflexivity.
Qed.

Lemma tree_eq_infer_f_lib {A : Type} (t1 t2 : tree A) (f : A -> Q) :
  tree_eq t1 t2 ->
  infer_f_lib f t1 == infer_f_lib f t2.
Proof.
  induction 1; simpl; try lra.
  - rewrite H, IHtree_eq1, IHtree_eq2; reflexivity.
  - apply tree_eq_infer_fail with (n:=l) in H; rewrite H.
    destruct (Qeq_bool (infer_fail l t2) 1) eqn:Heq; try lra.
    apply Qeq_bool_neq in Heq.
    rewrite H, IHtree_eq; reflexivity.
Qed.

(* Lemma diverges_infer_fail {A : Type} (t : tree A) (n : nat) : *)
(*   wf_tree t -> *)
(*   diverges t [n] -> *)
(*   infer_fail n t == 1. *)
(* Proof. *)
(*   revert n; induction t; intros m Hwf Hdiv; simpl. *)
(*   - inversion Hdiv. *)
(*   - inversion Hdiv; subst. *)
(*     destruct H0; subst; auto. *)
(*     + rewrite Nat.eqb_refl; reflexivity. *)
(*     + inversion H. *)
(*   - inversion Hwf; subst. *)
(*     inversion Hdiv; subst. *)
(*     + assert (Hq: q == 1). *)
(*       { lra. } *)
(*       rewrite Hq, IHt1; auto; lra. *)
(*     + assert (Hq: q == 0). *)
(*       { lra. } *)
(*       rewrite Hq, IHt2; auto; lra. *)
(*     + rewrite IHt1, IHt2; auto; lra. *)
(*   - inversion Hwf; subst. *)
(*     inversion Hdiv; subst. *)

(* Lemma diverges_infer_fail {A : Type} (t : tree A) (n : nat) (ns : list nat) : *)
(*   wf_tree t -> *)
(*   In n ns -> *)
(*   (forall m, free_in m t -> n = m) -> *)
(*   diverges t ns -> *)
(*   infer_fail n t == 1. *)
(* Proof. *)
(*   revert n ns; induction t; intros m ns Hwf Hin Hfree Hdiv; simpl. *)
(*   - inversion Hdiv. *)
(*   - inversion Hdiv; subst. *)
(*     erewrite Hfree; try constructor. *)
(*     rewrite Nat.eqb_refl; reflexivity. *)
(*   - inversion Hwf; subst. *)
(*     inversion Hdiv; subst. *)
(*     + assert (Hq: q == 1). *)
(*       { lra. } *)
(*       rewrite Hq, (IHt1 m ns); auto; try lra. *)
(*       intros k Hk; apply Hfree; constructor; auto. *)
(*     + assert (Hq: q == 0). *)
(*       { lra. } *)
(*       rewrite Hq, (IHt2 m ns); auto; try lra. *)
(*       intros k Hk; apply Hfree; solve [constructor; auto]. *)
(*     + rewrite (IHt1 m ns), (IHt2 m ns); auto; try lra. *)
(*       intros k Hk; apply Hfree; solve [constructor; auto]. *)
(*       intros k Hk; apply Hfree; constructor; auto. *)
(*   - inversion Hwf; subst. *)
(*     inversion Hdiv; subst. *)
(*     rewrite (IHt m (n :: ns)); auto. *)

Lemma infer_fail_infer_fail_le_1 {A : Type} (t : tree A) (m n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  not_bound_in m t ->
  n <> m ->
  infer_fail m t + infer_fail n t <= 1.
Proof.
  intros Hwf Hn Hm Hneq.
  rewrite <- 2!infer_mixed_infer_fail.
  generalize (@infer_mixed_disjoint_le_1 _ [lbl_indicator m; lbl_indicator n] t Hwf).
  simpl; rewrite Qplus_0_r; intro H; apply H; clear H.
  - constructor; simpl.
    + intros []; auto.
      assert (forall x : nat + A, lbl_indicator n x = lbl_indicator m x).
      { intros x; rewrite H; reflexivity. }
      specialize (H0 (inl n)); simpl in H0.
      rewrite Nat.eqb_refl in H0.
      destruct (Nat.eqb_spec n m); subst; auto; congruence.
    + constructor; auto; constructor.
  - intros f g [|[]] [|[]] Hneq' []; subst; simpl; auto; try lra;
      destruct (Nat.eqb_spec n0 n); subst; try lra;
        destruct (Nat.eqb_spec n m); subst; try lra; congruence.
  - intros f [|[]] []; subst; simpl; try lra.
    destruct (Nat.eqb_spec n0 m); lra.
    destruct (Nat.eqb_spec n0 n); lra.
  - intros lbl Hbound f [|[]]; subst; simpl; firstorder.
    + destruct (Nat.eqb_spec lbl m); try lra; subst.
      apply bound_in_not_bound_in in Hm; congruence.
    + destruct (Nat.eqb_spec lbl n); try lra; subst.
      apply bound_in_not_bound_in in Hn; congruence.
Qed.

Lemma infer_f_infer_fail_le_1 {A : Type} (t : tree A) (f : A -> Q) (n : nat) :
  wf_tree t ->
  bounded_expectation f 1 ->
  not_bound_in n t ->
  infer_f f t + infer_fail n t <= 1.
Proof.
  intros Hwf Hbounded_expectation Hnotbound.
  rewrite <- infer_mixed_infer_f.
  rewrite <- infer_mixed_infer_fail.
  generalize (@infer_mixed_disjoint_le_1 _ [mixf f; lbl_indicator n] t Hwf).
  simpl; rewrite Qplus_0_r; intro H; apply H; clear H.
  - constructor; simpl.
    + intros []; auto.
      assert (forall x, lbl_indicator n x = mixf f x).
      { intro x; rewrite H; reflexivity. }
      specialize (H0 (inl n)); simpl in H0.
      rewrite Nat.eqb_refl in H0; unfold const in H0; congruence.
    + constructor; auto; constructor.
  - intros g h [|[]] [|[]] Hneq; subst; try congruence;
      solve[intros []; split; simpl; unfold const; intro Hlt; lra].
  - intros g [|[]] []; subst; simpl; unfold const; try lra.
    + apply Hbounded_expectation.
    + destruct (Nat.eqb_spec n0 n); lra.
  - intros lbl Hbound g [|[]]; subst; simpl; unfold const; try lra.
    destruct (Nat.eqb_spec lbl n); subst; try lra.
    apply bound_in_not_bound_in in Hnotbound; congruence.
Qed.

Lemma infer_f_lib_infer_fail_complement {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  (forall m, free_in m t -> m = n) ->
  infer_f_lib (const 1) t == 1 - infer_fail n t.
Proof.
  intros Hwf Hnotbound Hfree.
  cut (sum_Q_list (map (fun x => infer_fail x t) [n]) + infer_f_lib (const 1) t == 1).
  { simpl; lra. }
  apply infer_f_lib_fail_1; auto.
  - intros x Hin. inversion Hin; subst; auto. inversion H.
  - intros x Hfreein; left; symmetry; apply Hfree; auto.
  - constructor; auto; constructor.
Qed.

(* Lemma nondivergent_infer_fail_sum_lt_1 {A : Type} (t : tree A) (l : list nat) : *)
(*   nondivergent t -> *)
(*   wf_tree t -> *)
(*   NoDup l -> *)
(*   (forall x, In x l -> not_bound_in x t) -> *)
(*   sum_Q_list (map (fun n => infer_fail n t) l) < 1. *)
(* Proof. *)
(*   revert l. induction t; intros l Hnd Hwf Hnodup Hnotbound; simpl. *)
(*   - induction l; simpl. *)
(*     + lra. *)
(*     + inversion Hnodup; subst. *)
(*       apply IHl in H2. lra. *)
(*       intros; apply Hnotbound; right; auto. *)
(*   - inversion Hnd. *)
(*   - rewrite sum_Q_list_map_plus, 2!sum_Q_list_map_mult_scalar. *)
(*     inversion Hwf; subst. *)
(*     inversion Hnd; subst. *)
(*     + rewrite H1; field_simplify; apply IHt2; auto; intros x Hin. *)
(*       apply Hnotbound in Hin; inversion Hin; subst; auto. *)
(*     + rewrite H1; field_simplify; apply IHt1; auto; intros x Hin. *)
(*       apply Hnotbound in Hin; inversion Hin; subst; auto. *)
(*     + assert (Ht1: forall x, In x l -> not_bound_in x t1). *)
(*       { intros x Hin; specialize (Hnotbound x Hin). *)
(*         inversion Hnotbound; subst; auto. } *)
(*       assert (Ht2: forall x, In x l -> not_bound_in x t2). *)
(*       { intros x Hin; specialize (Hnotbound x Hin). *)
(*         inversion Hnotbound; subst; auto. } *)
(*       destruct H7 as [H7 | H7]. *)
(*       * specialize (IHt1 l H7 H3 Hnodup Ht1). *)
(*         assert (sum_Q_list (map (fun n => infer_fail n t2) l) <= 1). *)
(*         { apply infer_fail_sum_le_1; auto. } *)
(*         nra. *)
(*       * specialize (IHt2 l H7 H4 Hnodup Ht2). *)
(*         assert (sum_Q_list (map (fun n => infer_fail n t1) l) <= 1). *)
(*         { apply infer_fail_sum_le_1; auto. } *)
(*         nra. *)
(*       (* specialize (IHt1 l H7 H3 Hnodup Ht1). *) *)
(*       (* specialize (IHt2 l H8 H4 Hnodup Ht2). *) *)
(*       (* nra. *) *)
(*   - inversion Hwf; subst. *)
(*     inversion Hnd; subst. *)
(*     assert (~ In n l). *)
(*     { intro HC. apply Hnotbound in HC. inversion HC; subst. congruence. } *)
(*     assert (Hlt: sum_Q_list (map (fun n => infer_fail n t) [n]) < 1). *)
(*     { apply IHt; auto. *)
(*       - constructor; auto; constructor. *)
(*       - intros x Hin. inversion Hin; subst; auto. *)
(*         inversion H3. } *)
(*     simpl in Hlt. rewrite Qplus_0_r in Hlt. *)
(*     rewrite sum_Q_list_map_div_scalar; try lra. *)
(*     apply Qlt_shift_div_r; try lra. *)
(*     rewrite Qmult_1_l. *)
(*     assert (Hnodup': NoDup (n :: l)). *)
(*     { constructor; auto. } *)
(*     apply IHt in Hnodup'; auto. *)
(*     + simpl in Hnodup'. lra. *)
(*     + intros x Hin. inversion Hin; subst; auto. *)
(*       apply Hnotbound in H3. inversion H3; subst; auto. *)
(* Qed. *)

Lemma fail_reachable_infer_fail_positive {A : Type} (t : tree A) (n : nat) :
  wf_tree'' t ->
  fail_reachable n t ->
  not_bound_in n t ->
  0 < infer_fail n t.
Proof.
  revert n.
  induction t; simpl; intros m Hwf Hreach Hnotbound.
  - inversion Hreach.
  - inversion Hreach; subst.
    rewrite Nat.eqb_refl; lra.
  - inversion Hwf; subst.
    inversion Hnotbound; subst.
    assert (0 <= infer_fail m t1).
    { apply infer_fail_0_le; auto; apply wf_tree''_wf_tree; auto. }
    assert (0 <= infer_fail m t2).
    { apply infer_fail_0_le; auto; apply wf_tree''_wf_tree; auto. }
    inversion Hreach; subst.
    + destruct H7 as [Hfail | Hfail].
      * specialize (IHt1 m H4 Hfail H6); nra.
      * specialize (IHt2 m H5 Hfail H8); nra.
  - inversion Hwf; subst.
    inversion Hnotbound; subst.
    inversion Hreach; subst.
    specialize (IHt m H1 H0 H5).
    assert (infer_fail n t < 1).
    { assert (infer_fail m t + infer_fail n t <= 1).
      { apply infer_fail_infer_fail_le_1; auto; apply wf_tree''_wf_tree; auto. }
      lra. }
    apply Qlt_shift_div_l; lra.
Qed.

Lemma no_leaf_reachable_infer_f_0 {A : Type} (t : tree A) (f : A -> Q) :
  no_leaf_reachable t ->
  infer_f f t == 0.
Proof.
  induction t; simpl; intro Hleaf.
  - inversion Hleaf.
  - reflexivity.
  - inversion Hleaf; subst.
    + rewrite H1, Qmult_0_l, Qplus_0_l, Qminus_0_r, Qmult_1_l; auto.
    + rewrite H1, Qmult_1_l, Qminus_cancel, Qmult_0_l, Qplus_0_r; auto.
    + rewrite IHt1, IHt2; auto; lra.
  - inversion Hleaf; subst.
    rewrite IHt, Qdiv_0_num; auto; reflexivity.
Qed.

Lemma leaf_reachable_infer_f_positive {A : Type} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  leaf_reachable t ->
  (forall x, 0 < f x) ->
  (forall x, f x <= 1) ->
  0 < infer_f f t.
Proof.
  induction t; simpl; intros Hwf Hreach Hpos Hle1; auto.
  - inversion Hreach.
  - inversion Hwf; subst.
    assert (0 <= infer_f f t1).
    { apply infer_f_expectation_0_le; auto.
      intro x; specialize (Hpos x); lra. }
    assert (0 <= infer_f f t2).
    { apply infer_f_expectation_0_le; auto.
      intro x; specialize (Hpos x); lra. }
    inversion Hreach; subst; clear Hreach.
    + apply (IHt2 H4) in H8; auto; clear IHt1 IHt2; nra.
    + apply (IHt1 H3) in H8; auto; clear IHt1 IHt2; nra.
    + destruct H9 as [Hleaf | Hleaf].
      * apply (IHt1 H3) in Hleaf; auto; clear IHt1 IHt2; nra.
      * apply (IHt2 H4) in Hleaf; auto; clear IHt1 IHt2; nra.
  - inversion Hwf; subst.
    inversion Hreach; subst.
    specialize (IHt H1 H0 Hpos Hle1).
    assert (H3: infer_fail n t < 1).
    { assert (H4: infer_f f t + infer_fail n t <= 1).
      { apply infer_f_infer_fail_le_1; auto. 
        intros x; specialize (Hpos x); specialize (Hle1 x); lra. }
      lra. }
    apply Qlt_shift_div_l; lra.
Qed.

Lemma leaf_reachable_infer_fail_nonzero {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  leaf_reachable t ->
  not_bound_in n t ->
  ~ infer_fail n t == 1.
Proof.
  intros Hwf Hreach Hnotbound.
  intro HC.
  assert (0 < infer_f (const 1) t).
  { apply leaf_reachable_infer_f_positive; auto; intro x; unfold const; lra. }
  assert (infer_f (const 1) t + infer_fail n t <= 1).
  { apply infer_f_infer_fail_le_1; auto; intro x; unfold const; lra. }
  lra.
Qed.

Lemma fail_reachable_infer_fail_not_one {A : Type} (t : tree A) (n m : nat) :
  wf_tree'' t ->
  fail_reachable m t ->
  n <> m ->  
  not_bound_in n t ->
  not_bound_in m t ->
  ~ infer_fail n t == 1.
Proof.
  intros Hwf Hreach Hneq Hn Hm.
  intro HC.
  generalize (fail_reachable_infer_fail_positive Hwf Hreach Hm); intro H0.
  assert (H2: infer_fail m t + infer_fail n t <= 1).
  { apply infer_fail_infer_fail_le_1; auto; apply wf_tree''_wf_tree; auto. }
  lra.
Qed.

(* infer_f and infer_f_lib coincide on nondivergent trees. *)
Lemma nondivergent'_infer_f_infer_f_lib {A : Type} (t : tree A) (ls : list nat) (f : A -> Q) :
  wf_tree'' t ->
  (forall l, In l ls -> not_bound_in l t) ->
  nondivergent' ls t ->
  infer_f f t == infer_f_lib f t.
Proof.
  revert ls.
  induction t; intros ls Hwf Hls Hnd; simpl; try reflexivity.
  - inversion Hwf; subst.
    inversion Hnd; subst.
    rewrite IHt1, IHt2; eauto; try lra.
    eapply in_not_bound_choice2; eauto.
    eapply in_not_bound_choice1; eauto.
  - inversion Hwf; subst.
    inversion Hnd; subst.
    rewrite IHt; eauto.
    + destruct (Qeq_bool (infer_fail n t) 1) eqn:Heq.
      * apply Qeq_bool_eq in Heq.
        destruct H4 as [Hreach | [k [Hin Hreach]]].
        -- apply leaf_reachable_infer_fail_nonzero with (n0:=n) in Hreach; auto.
           ++ congruence.
           ++ apply wf_tree''_wf_tree; auto.
        -- eapply fail_reachable_infer_fail_not_one with (n0:=n) in Hreach; auto.
           ++ congruence.
           ++ intro HC; subst.
              apply Hls in Hin.
              inversion Hin; congruence.
           ++ apply Hls in Hin.
              inversion Hin; subst; auto.
      * reflexivity.
    + intros l [? | H]; subst; auto.
      specialize (Hls l H).
      inversion Hls; subst; auto.
Qed.

Lemma fail_reachable_free_in {A : Type} (t : tree A) (n : nat) :
  not_bound_in n t ->
  fail_reachable n t ->
  free_in n t.
Proof.
  induction t; simpl; intros H0 H1; inversion H0; inversion H1;
    subst; try solve[constructor; auto].
  destruct H8 as [Hfail | Hfail]; solve [constructor; auto].
Qed.

Lemma nondivergent'_infer_f_positive {A : Type} (t : tree A) (n : nat) (f : A -> Q) :
  wf_tree t ->
  nondivergent'' n t ->
  (forall x, 0 < f x) ->
  (forall x, f x <= 1) ->
  0 < infer_f f t.
Proof.
  intros Hwf Hnd Hpos Hle1.
  inversion Hnd; subst.
  destruct H2 as [Hreach | [? [[] ?]]].
  apply leaf_reachable_infer_f_positive; auto.
Qed.

(** The syntactic notion of nondivergence implies the semantic one
    (nondivergent'' is sound wrt infer). Strategy: show that infer_f
    and infer_f_lib coincide on syntactically nondivergent trees. *)
Lemma nondivergent''_infer_1 {A : Type} (t : tree A) (n : nat) :
  wf_tree'' t ->
  not_bound_in n t ->
  (forall m, free_in m t -> m = n) ->
  nondivergent'' n t ->
  infer (const 1) t == 1.
Proof.
  intros Hwf Hnotbound Hfree Hnd.
  unfold infer.
  rewrite <- nondivergent'_infer_f_infer_f_lib with (ls:=[n]); eauto.
  - assert (0 < infer_f (const 1) t).
    { eapply nondivergent'_infer_f_positive; eauto;
        try apply wf_tree''_wf_tree; auto;
          intro x; unfold const; lra. }
    field; lra.
  - intros l []; subst; auto; inversion H.
  - inversion Hnd; subst; auto.
Qed.

Lemma divergent_infer_f_le_infer_f_lib {A : Type} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer_f f t <= infer_f_lib f t.
Proof.
  induction t; simpl; intro Hwf; try lra; inversion Hwf; subst.
  - specialize (IHt1 H3); specialize (IHt2 H4); nra.
  - destruct (Qeq_bool (infer_fail n t) 1) eqn:Hq1.
    { apply Qeq_bool_eq in Hq1.
      rewrite Hq1, Qminus_cancel, Qdiv_0_den; lra. }
    apply Qeq_bool_neq in Hq1.
    assert (infer_fail n t <= 1).
    { apply infer_fail_le_1; auto. }
    apply Qle_Qdiv; auto; lra.
Qed.

Lemma fail_not_reachable_infer_fail_0 {A : Type} (t : tree A) (n : nat) :
  fail_not_reachable n t ->
  infer_fail n t == 0.
Proof.
  induction t; simpl; intros H0; inversion H0; subst.
  - reflexivity.
  - destruct (Nat.eqb_spec n0 n); congruence.
  - rewrite IHt1, IHt2; auto; lra.
  - rewrite IHt; auto; rewrite Qdiv_0_num; reflexivity.
Qed.

Lemma nondivergent'_infer_fail_1 {A : Type} (t : tree A) (n : nat) (ls : list nat) :
  wf_tree'' t ->
  not_bound_in n t ->
  no_leaf_reachable t ->
  (forall m, In m ls -> fail_not_reachable m t) ->
  (forall m, free_in m t -> m = n) ->
  (forall m, In m ls -> not_bound_in m t) ->
  nondivergent' (n :: ls) t ->
  infer_fail n t == 1.
Proof.
  revert ls; induction t; simpl; intros ls Hwf Hnotbound Hleaf Hfail H0 Hnotbound' Hnd.
  - inversion Hleaf.
  - specialize (H0 n0 (free_in_fail n0)); subst; rewrite Nat.eqb_refl; reflexivity.
  - inversion Hnotbound; subst.
    inversion Hwf; subst.
    inversion Hleaf; subst.
    + rewrite H2, Qmult_0_l, Qplus_0_l, Qminus_0_r, Qmult_1_l.
      eapply IHt2 with ls; eauto.
      * intros m Hin; specialize (Hfail m Hin).
        inversion Hfail; subst; auto; lra.
      * intros m Hfree; apply H0; solve [constructor; auto].
      * intros m Hin; specialize (Hnotbound' m Hin); inversion Hnotbound'; auto.
      * inversion Hnd; subst; auto; try lra.
    + rewrite H2, Qmult_1_l, Qminus_cancel, Qmult_0_l, Qplus_0_r.
      eapply IHt1 with ls; eauto.
      * intros m Hin; specialize (Hfail m Hin).
        inversion Hfail; subst; auto; lra.
      * intros m Hfree; apply H0; solve [constructor; auto].
      * intros m Hin; specialize (Hnotbound' m Hin); inversion Hnotbound'; auto.
      * inversion Hnd; subst; auto; try lra.
    + rewrite IHt1 with ls; eauto.
      rewrite IHt2 with ls; eauto.
      * lra.
      * intros m Hin; specialize (Hfail m Hin); inversion Hfail; subst; try lra; auto.
      * intros M Hm; apply H0; solve [constructor; auto].
      * intros m Hin; specialize (Hnotbound' m Hin); inversion Hnotbound'; auto.
      * inversion Hnd; subst; auto; try lra.
      * intros m Hin; specialize (Hfail m Hin); inversion Hfail; subst; try lra; auto.
      * intros M Hm; apply H0; solve [constructor; auto].
      * intros m Hin; specialize (Hnotbound' m Hin); inversion Hnotbound'; auto.
      * inversion Hnd; subst; auto; try lra.
  - inversion Hnotbound; subst.
    inversion Hwf; subst.
    inversion Hleaf; subst.
    inversion Hnd; subst.
    destruct H8 as [Hleaf' | [m [Hin Hfail']]].
    + apply not_leaf_reachable_no_leaf_reachable in H1; congruence.
    + destruct Hin as [? | Hin]; subst.
      * generalize (@infer_f_lib_fail_1 A t (m :: n0 :: []) (wf_tree''_wf_tree H2)).
        intro H'. simpl in H'.
        unfold flip in H'.
        rewrite Qplus_0_r in H'.
        assert (H'': infer_f_lib (const 1) t == 0).
        { rewrite <- nondivergent'_infer_f_infer_f_lib; eauto.
          2: { intros l [? | [? | Hin]]; subst; auto.
               apply Hnotbound' in Hin; inversion Hin; auto. }
          apply no_leaf_reachable_infer_f_0; auto. }
        rewrite H'' in H'. rewrite Qplus_0_r in H'.
        assert (~ infer_fail n0 t == 1).
        { eapply fail_reachable_infer_fail_not_one; eauto. }
        apply Qdiv_Qeq_1; try lra.
        cut (infer_fail m t + infer_fail n0 t == 1).
        { lra. }
        apply H'.
        -- intros x [? | [? | []]]; subst; auto.
        -- intros x Hfree.
           destruct (Nat.eqb_spec n0 x); subst; auto.
           left; symmetry; apply H0; constructor; auto.
        -- constructor.
           ++ intro HC; inversion HC; subst.
              ** congruence.
              ** inversion H6.
           ++ constructor; auto; constructor.
      * apply Hfail in Hin.
        inversion Hin; subst.
        apply not_fail_reachable_fail_not_reachable in H6; congruence.
Qed.

(* infer_f is less than infer_f_lib on divergent trees. *)
Lemma divergent_infer_f_lt_infer_f_lib {A : Type} (t : tree A) (ls : list nat) (f : A -> Q) :
  wf_tree'' t ->
  (forall l, In l ls -> not_bound_in l t) ->
  (forall l, free_in l t -> In l ls) ->
  divergent ls t ->
  infer_f f t < infer_f_lib f t.
Proof.
  revert ls.
  induction t; simpl; intros ls Hwf Hnotbound Hfree Hdiv.
  - inversion Hdiv.
  - inversion Hdiv; subst; exfalso; apply H1, Hfree; constructor.
  - inversion Hwf; subst.
    inversion Hdiv; try lra; subst.
    destruct H1 as [H | H].
    + assert (H': forall l, In l ls -> not_bound_in l t1).
      { intros l Hin; specialize (Hnotbound l Hin); inversion Hnotbound; auto. }
      assert (H'': forall l, free_in l t1 -> In l ls).
      { intros l Hl; apply Hfree. solve [constructor; auto]. }
      specialize (IHt1 ls H4 H' H'' H).
      assert (infer_f f t2 <= infer_f_lib f t2).
      { apply divergent_infer_f_le_infer_f_lib; auto; apply wf_tree''_wf_tree; auto. }
      nra.
    + assert (H': forall l, In l ls -> not_bound_in l t2).
      { intros l Hin; specialize (Hnotbound l Hin); inversion Hnotbound; auto. }
      assert (H'': forall l, free_in l t2 -> In l ls).
      { intros l Hl; apply Hfree; solve [constructor; auto]. }
      specialize (IHt2 ls H5 H' H'' H).
      assert (infer_f f t1 <= infer_f_lib f t1).
      { apply divergent_infer_f_le_infer_f_lib; auto; apply wf_tree''_wf_tree; auto. }
      nra.
  - inversion Hwf; subst.
    inversion Hdiv; subst.
    destruct (Qeq_bool (infer_fail n t) 1) eqn:H0.
    + apply Qeq_bool_eq in H0.
      rewrite H0, Qminus_cancel, Qdiv_0_den; lra.
    + apply Qeq_bool_neq in H0.
      assert (infer_fail n t <= 1).
      { apply infer_fail_le_1; auto; apply wf_tree''_wf_tree; auto. }
      apply Qlt_Qdiv; try lra.
      destruct H3 as [[Hleaf Hfail] | Hdiv'].
      * destruct (nondivergent'_dec (n :: ls) t).
        -- assert (infer_fail n t == 1).
           { eapply nondivergent'_infer_fail_1; eauto.
             - intros m Hm.
               destruct (Nat.eqb_spec m n); subst; auto.
               assert (In m ls).
               { apply Hfree; constructor; auto. }
               apply Hfail in H3.
               apply free_in'_fail_not_reachable in Hm.
               apply not_fail_reachable_fail_not_reachable in H3.
               congruence.
             - intros m Hm; specialize (Hnotbound m Hm); inversion Hnotbound; auto. }
           congruence.
        -- eapply IHt; eauto.
           ++ intros l [? | Hin]; subst; auto.
              specialize (Hnotbound l Hin); inversion Hnotbound; auto.
           ++ intros l Hl.
              destruct (Nat.eqb_spec l n); subst.
              ** left; auto.
              ** right; apply Hfree; constructor; auto.
      * eapply IHt; eauto.
        -- intros l [? | Hin]; subst; auto.
           apply Hnotbound in Hin; inversion Hin; subst; auto.
        -- intros l Hl; destruct (Nat.eqb_spec l n); subst.
           ++ left; auto.
           ++ right; apply Hfree; constructor; auto.
Qed.

Lemma divergent'_infer_lt_1 {A : Type} (t : tree A) (n : nat) :
  wf_tree'' t ->
  not_bound_in n t ->
  (forall m, free_in m t -> m = n) ->
  divergent' n t ->
  infer (const 1) t < 1.
Proof.
  intros Hwf Hnotbound Hfree Hdiv.
  unfold infer.
  unfold divergent' in Hdiv.
  inversion Hdiv; subst.
  destruct H1 as [[Hleaf Hfail] | Hdiv'].
  - rewrite no_leaf_reachable_infer_f_0; auto.
    rewrite Qdiv_0_num; lra.
  - destruct (Qeq_bool (infer_f_lib (const 1) t) 0) eqn:H0.
    { apply Qeq_bool_eq in H0.
      rewrite H0, Qdiv_0_den; lra. }
    apply Qeq_bool_neq in H0.
    assert (0 <= infer_f_lib (const 1) t).
    { apply infer_f_lib_expectation_0_le; auto;
        try apply wf_tree''_wf_tree; auto;
          intro x; unfold const; lra. }
    apply Qlt_shift_div_r; try lra.
    rewrite Qmult_1_l.
    eapply divergent_infer_f_lt_infer_f_lib; eauto.
    + intros l [? | Hin]; subst; auto; inversion Hin.
    + intros l Hl; left; symmetry; apply Hfree; auto.
Qed.

(** Semantic nondivergence implies syntactic nondivergence (the
    syntactic notion is complete wrt infer). Strategy: proof by
    contradiction (suppose that t is divergent and derive from that
    [infer (const 1) t < 1], contradicting the hypothesis) which is
    constructively valid since the syntactic notion of
    divergence/nondivergence is decidable. *)
Lemma infer_1_nondivergent' {A : Type} (t : tree A) (n : nat) :
  wf_tree'' t ->
  not_bound_in n t ->
  (forall m, free_in m t -> m = n) ->
  infer (const 1) t == 1 ->
  nondivergent'' n t.
Proof.
  intros Hwf Hnotbound Hfree Hinfer.
  destruct (nondivergent''_dec n t); auto.
  apply divergent'_infer_lt_1 in d; auto; lra.
Qed.

(** Our syntactic notion of nondivergence coincides with the semantic
    notion on well-formed trees. *)
Theorem nondivergent''_spec {A : Type} (t : tree A) (n : nat) :
  wf_tree'' t ->
  not_bound_in n t ->
  (forall m, free_in m t -> m = n) ->
  nondivergent'' n t <-> infer (const 1) t == 1.
Proof.
  intros Hwf Hnotbound Hfree; split; intro H0.
  - eapply nondivergent''_infer_1; eauto.
  - apply infer_1_nondivergent'; auto.
Qed.
