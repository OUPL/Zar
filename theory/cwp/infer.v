(** Inference on trees. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import Nat.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope program_scope.

Require Import cpGCL.
Require Import geometric.
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.

(** Inference on trees. *)

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

Fixpoint infer_fail_lib {A : Type} (n : nat) (t : tree A) : Q :=
  match t with
  | Leaf _ => 0
  | Fail _ m => if m =? n then 1 else 0
  | Choice p t1 t2 => p * infer_fail_lib n t1 + (1-p) * infer_fail_lib n t2
  | Fix m t =>
    let a := infer_fail_lib n t in
    let b := infer_fail_lib m t in
    if Qeq_bool b 1 then 1 else a / (1 - b)
  end.

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

Fixpoint infer_f_lib' {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf x => f x
  | Fail _ _ => 1
  | Choice p t1 t2 => p * infer_f_lib' f t1 + (1-p) * infer_f_lib' f t2
  | Fix m t =>
    let a := infer_f_lib' f t in
    let b := infer_fail_lib m t in
    if Qeq_bool b 1 then 1 else a / (1 - b)
  end.

Definition infer {A : Type} (f : A -> Q) (t : tree A) : Q :=
  let a := infer_f f t in
  let b := infer_f_lib (const 1) t in
  a / b.


(** Proofs about inference. *)

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
        ++ generalize (@infer_fail_le_1 A t n H1 H2); intros; lra.
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

Lemma infer_f_lib_fail_aux {A : Type} (t : tree A) (f : A -> Q) (m : nat) (l : list nat) :
  wf_tree t ->
  (forall x : nat, In x l -> not_bound_in x t) ->
  NoDup l ->
  not_bound_in m t ->
  sum_Q_list (map (flip infer_fail t) l) == 1 ->
  infer_f_lib f t == 0.
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
        ++ generalize (@infer_fail_le_1 A t n H1 H2); intros; lra.
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
  wf_tree' t ->
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

Lemma all_support_true_infer_f (e : St -> bool) (f g : St -> Q) (t : tree St) :
  wf_tree t ->
  all_support (fun x => e x = true) t ->
  infer_f (fun x => if e x then f x else g x) t ==
  infer_f f t.
Proof.
  induction t; intros Hwf Hsupp; inversion Hwf; subst; simpl.
  - inversion Hsupp; subst. rewrite H0; reflexivity.
  - reflexivity.
  - inversion Hsupp; subst.
    + rewrite H1, 2!Qmult_0_l, 2!Qplus_0_l, Qminus_0_r, 2!Qmult_1_l.
      apply IHt2; auto.
    + rewrite H1, Qmult_1_l, Qminus_cancel,
      2!Qmult_0_l, Qmult_1_l, 2!Qplus_0_r.
      apply IHt1; auto.
    + rewrite IHt1, IHt2; auto; reflexivity.
  - inversion Hsupp; subst.
    rewrite IHt; auto; reflexivity.
Qed.

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
