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

(* Fixpoint infer_f_lib {A : Type} (f : A -> Q) (t : tree A) : Q := *)
(*   match t with *)
(*   | Leaf x => f x *)
(*   | Fail _ _ => 0 *)
(*   | Choice p t1 t2 => p * infer_f_lib f t1 + (1-p) * infer_f_lib f t2 *)
(*   | Fix m t => *)
(*     let a := infer_f_lib f t in *)
(*     let b := infer_fail_lib m t in *)
(*     if Qeq_bool b 1 then 1 else a / (1 - b) *)
(*   end. *)

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
  (* let b := infer_fail O t in *)
  (* a / (1 - b). *)


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

Lemma infer_f_lib_bind {A B : Type} (f : B -> Q) (t : tree A) (k : A -> tree B) :
  (forall n x, bound_in n t -> not_in n (k x)) ->
  infer_f_lib (infer_f_lib f ∘ k) t == infer_f_lib f (tree_bind t k).
Proof.
  revert f k. induction t; intros f k Hnotin; try reflexivity.
  - simpl; rewrite IHt1, IHt2; try reflexivity;
      intros n st Hbound; apply Hnotin;
        try solve [apply bound_in_choice2; auto]; constructor; auto.
  - simpl.
    destruct (Qeq_dec (infer_fail n t) 1).
    { rewrite q; simpl.
      destruct (Qeq_dec (infer_fail n (tree_bind t k)) 1).
      { rewrite q0; simpl; reflexivity. }
      (* rewrite Qeq_bool_false; auto. *)
      (* TODO: q and n0 are contradictory because q implies infer_fail
         n (bind t k) == 1 for any k. *)
      admit. }
    destruct (Qeq_dec (infer_fail n (tree_bind t k)) 1).
    { rewrite q. simpl.
      rewrite Qeq_bool_false; auto.
      rewrite IHt.
      - admit.
      - intros m x Hbound; apply Hnotin.
        destruct (Nat.eqb_spec m n); subst; constructor; auto. }
    rewrite 2!Qeq_bool_false; auto.
    rewrite IHt; auto.
    + admit.
    + intros m x Hbound; apply Hnotin.
      destruct (Nat.eqb_spec m n); subst; constructor; auto.
Admitted.
      
(*     apply Qeq_Qdiv. *)
(*     + apply IHt; intros n0 st Hbound; apply Hnotin. *)
(*       destruct (Nat.eqb_spec n0 n); subst; constructor; auto. *)
(*     + apply Qeq_Qminus; try reflexivity. *)
(*       clear IHt. revert Hnotin. revert k n. induction t; intros k m Hnotin. *)
(*       * simpl. rewrite not_in_infer_fail. reflexivity. apply Hnotin. constructor. *)
(*       * simpl. reflexivity. *)
(*       * simpl. rewrite IHt1, IHt2. reflexivity. *)
(*         intros m' x Hbound. apply Hnotin. inversion Hbound; subst. *)
(*         constructor. constructor; auto. apply bound_in_choice2; auto. *)
(*         intros m' x Hbound. apply Hnotin. inversion Hbound; subst. *)
(*         constructor. constructor; auto. constructor; auto. *)
(*       * simpl. rewrite IHt. rewrite IHt. reflexivity. *)
(*         intros m' x Hbound. apply Hnotin. *)
(*         inversion Hbound; subst. *)
(*         destruct (Nat.eqb_spec n m); subst. constructor. constructor; auto. *)
(*         destruct (Nat.eqb_spec m' m); subst. constructor. constructor; auto. *)
(*         intros m' x Hbound. apply Hnotin. *)
(*         inversion Hbound; subst. *)
(*         constructor. *)
(*         constructor; auto. *)
(*         destruct (Nat.eqb_spec m' n); subst. constructor. constructor; auto. *)
(* Qed. *)

Lemma infer_fail_fbind {A : Type} (t1 t2  : tree A) (l m : nat) :
  l <> m ->
  wf_tree t1 ->
  not_bound_in l t1 ->
  (forall n, bound_in n t1 -> ~ free_in n t1) ->
  (forall n, bound_in n t1 -> not_in n t2) ->
  infer_fail m (fbind l t1 t2) == infer_fail m t1 + infer_fail l t1 * infer_fail m t2.
Proof.
  revert m.
  induction t1; intros m H0 H1 H2 H3 H4; simpl.
  - lra.
  - destruct (Nat.eqb_spec l n); subst; simpl.
    + destruct (Nat.eqb_spec n m); subst; try congruence.
      rewrite Nat.eqb_refl; lra.
    + destruct (Nat.eqb_spec n m); subst.
      * destruct (Nat.eqb_spec m l); subst; try congruence; lra.
      * destruct (Nat.eqb_spec n l); subst; try congruence; lra.
  - inversion H1; inversion H2; subst.
    rewrite IHt1_1; auto.
    + rewrite IHt1_2; auto.
      * lra.
      * intros n Hbound HC; eapply H3.
        ** apply bound_in_choice2; eauto.
        ** apply free_in_choice2; auto.
      * intros; apply H4; apply bound_in_choice2; auto.
    + intros n Hbound HC. eapply H3; constructor; eauto.
    + intros; apply H4; constructor; auto.
  - inversion H2; subst.
    destruct (Nat.eqb_spec n l); subst; try congruence.
    assert (H': forall n1, bound_in n1 t1 -> ~ free_in n1 t1).
    { intros n1 Hbound HC.
      eapply H3 with n1.
      destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
      destruct (Nat.eqb_spec n1 n); subst.
      - inversion H1; subst; apply bound_in_not_bound_in in H9; congruence.
      - constructor; auto. }
    assert (H'': forall n1, bound_in n1 t1 -> not_in n1 t2).
    { intros n1 Hbound. apply H4.
      destruct (Nat.eqb_spec n1 n); subst; constructor; auto. }
    inversion H1; subst.
    rewrite IHt1; auto.
    rewrite IHt1; auto.
    assert (Hnotin: not_in n t2).
    { apply H4; constructor. }
    (** Here we use that infer_fail n t2 must be zero since n doesn't
        appear in t2. *)
    apply not_in_infer_fail in Hnotin.
    eapply infer_fail_le_1 in H6; eauto.
    apply Qle_lteq in H6. destruct H6; rewrite Hnotin.
    + field; lra.
    + rewrite H.
      rewrite Qminus_cancel.
      rewrite 2!Qdiv_0_den.
      rewrite Qmult_0_r, Qmult_0_l, Qplus_0_r.
      rewrite Qminus_cancel, Qdiv_0_den; reflexivity.
Qed.

Lemma infer_fbind {A : Type} (f : A -> Q) (t1 t2  : tree A) (l : nat) :
  wf_tree t1 ->
  (forall n1 : nat, bound_in n1 t1 -> ~ free_in n1 t1) ->
  (forall n, bound_in n t1 -> not_in n t2) ->
  not_bound_in l t1 ->
  not_bound_in l t2 ->
  infer_f f (fbind l t1 t2) == infer_f f t1 + infer_fail l t1 * infer_f f t2.
Proof.
  induction t1; intros Hwf Hnotfree Hnotin Ht1 Ht2; simpl; try lra.
  - destruct (Nat.eqb_spec l n); subst.
    + rewrite Nat.eqb_refl; lra.
    + destruct (Nat.eqb_spec n l); subst; simpl; try congruence; lra.
  - inversion Ht1; subst; inversion Hwf; subst.
    rewrite IHt1_1; auto. rewrite IHt1_2; auto; try lra.
    + intros n1 Hbound HC; eapply Hnotfree with n1.
      * apply bound_in_choice2; auto.
      * apply free_in_choice2; auto.
    + intros; apply Hnotin; apply bound_in_choice2; auto.
    + intros n1 Hbound HC; apply Hnotfree with n1; constructor; auto.
    + intros; apply Hnotin; constructor; auto.
  - inversion Ht1; inversion Hwf; subst.
    destruct (Nat.eqb_spec n l); subst.
    + congruence.
    + assert (H': forall n1 : nat, bound_in n1 t1 -> ~ free_in n1 t1).
      { intros n1 Hbound HC. apply Hnotfree with n1.
        - destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
        - destruct (Nat.eqb_spec n1 n); subst.
          + apply bound_in_not_bound_in in H7; congruence.
          + constructor; auto. }
      assert (H'': forall n1 : nat, bound_in n1 t1 -> not_in n1 t2).
      { intros n1 ?; apply Hnotin;
          destruct (Nat.eqb_spec n1 n); subst; constructor; auto. }
      rewrite IHt1; auto.
      rewrite infer_fail_fbind; auto.
      (** Again, since n is not in t2 by Hnotin, infer_fail n t2 must
          be zero. *)
      assert (Hnotin': not_in n t2).
      { apply Hnotin; constructor. }
      (** Here we use that infer_fail n t2 must be zero since n doesn't
        appear in t2. *)   
      apply not_in_infer_fail in Hnotin'.
      rewrite Hnotin'. rewrite Qmult_0_r, Qplus_0_r.
      eapply infer_fail_le_1 in H7; auto.      
      apply Qle_lteq in H7. destruct H7.
      * field; lra.
      * rewrite H. rewrite Qminus_cancel, 3!Qdiv_0_den. field.
Qed.

(* Lemma infer_f_fbind_fail {A : Type} {t : tree A} (f : A -> Q) (l : nat) : *)
(*   infer_f f (fbind l (Fail _ l) t) = infer_f f t. *)
(* Proof. simpl; rewrite Nat.eqb_refl; reflexivity. Qed. *)

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

Lemma infer_fail_fbind_t1 {A : Type} (l m : nat) (t1 t2 : tree A) :
  l <> m ->
  not_in m t2 ->
  (forall n, bound_in n t1 -> not_in n t2) ->
  infer_fail m (fbind l t1 t2) == infer_fail m t1.
Proof.
  revert t2 l m; induction t1; intros t2 l m Hneq Hnotin Hbound; simpl.
  - reflexivity.
  - destruct (Nat.eqb_spec l n); destruct (Nat.eqb_spec n m); subst; simpl.
    + congruence.
    + apply not_in_infer_fail_0; auto.
    + rewrite Nat.eqb_refl; reflexivity.
    + destruct (Nat.eqb_spec n m); subst; congruence.
  - rewrite IHt1_1, IHt1_2; auto; try reflexivity.
    + intros n H; apply Hbound; apply bound_in_choice2; auto.
    + intros n H; apply Hbound; apply bound_in_choice1; auto.
  - destruct (Nat.eqb_spec n l); subst; try congruence.
    rewrite 2!IHt1; auto; try reflexivity; intros; auto; apply Hbound.
    + constructor.
    + destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
    + destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
Qed.

Lemma infer_f_fbind_geom {A : Type} {t1 t2 : tree A} (f : A -> Q) (l : nat) :
  (forall n, bound_in n t1 -> not_in n t2) ->
  not_bound_in l t1 ->
  infer_f f (fbind l t1 t2) == infer_f f t1 + infer_fail l t1 * infer_f f t2.
Proof.
  revert t2 f l. induction t1; intros t2 f l H0 H1; simpl.
  - field.
  - destruct (Nat.eqb_spec l n); subst; simpl.
    + rewrite Nat.eqb_refl; field.
    + destruct (Nat.eqb_spec n l); subst. congruence. field.
  - inversion H1; subst; rewrite IHt1_1, IHt1_2; auto;
      try field; intros n Hbound; apply H0.
    + apply bound_in_choice2; auto.
    + constructor; auto.
  - inversion H1; subst.
    destruct (Nat.eqb_spec n l); subst.
    + congruence.
    + rewrite IHt1; auto.
      * rewrite infer_fail_fbind_t1; auto; try solve [apply H0; constructor].
        destruct (Qeq_dec (infer_fail n t1) 1).
        ** rewrite q. 
           rewrite 3!Qdiv_0_den. field.
        ** field; lra.
        ** intros; apply H0.
           destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
      * intros m Hbound. apply H0.
        destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Lemma not_in_subst_l_infer_fail {A : Type} (t : tree A) (l n m : nat) :
  l <> n ->
  l <> m ->
  not_bound_in m t ->
  infer_fail l (subst_l n m t) == infer_fail l t.
Proof.
  revert l; induction t; intros l H0 H1 Hnotbound;
    simpl; inversion Hnotbound; subst.
  - reflexivity.
  - destruct (Nat.eqb_spec n0 n); subst.
    + destruct (Nat.eqb_spec m l); subst.
      * congruence.
      * destruct (Nat.eqb_spec n l); subst.
        ++ congruence.
        ++ reflexivity.
    + destruct (Nat.eqb_spec n0 l); subst; reflexivity.
  - rewrite IHt1, IHt2; auto; reflexivity.
  - destruct (Nat.eqb_spec n0 n); subst.
    + reflexivity.
    + rewrite IHt; auto. rewrite IHt; auto.
      reflexivity.
Qed.

(** If m was bound somewhere in t, and n appeared free underneath it,
   then substituting n for m would cause m to be captured. *)
Lemma not_in_subst_l_infer {A : Type} (t : tree A) (f : A -> Q) (n m : nat) :
  not_bound_in m t ->
  infer_f f (subst_l n m t) == infer_f f t.
Proof.
  induction t; intro Hnotin; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hnotin; subst.
    rewrite IHt1, IHt2; auto; reflexivity.
  - inversion Hnotin; subst.
    destruct (Nat.eqb_spec n0 n); subst.
    + reflexivity.
    + rewrite IHt; auto.
      rewrite not_in_subst_l_infer_fail; auto. reflexivity.
Qed.

Lemma infer_fail_subst_l {A : Type} (t : tree A) (l m : nat) :
  not_bound_in l t ->
  not_in m t ->
  infer_fail m (subst_l l m t) == infer_fail l t.
Proof.
  revert m; induction t; intros m Hnotbound Hnotfree; simpl.
  - reflexivity.
  - destruct (Nat.eqb_spec n l); subst.
    + rewrite Nat.eqb_refl; reflexivity.
    + inversion Hnotfree; subst.
      destruct (Nat.eqb_spec n m); subst. congruence. reflexivity.
  - inversion Hnotfree; inversion Hnotbound; subst;
      rewrite IHt1, IHt2; auto; reflexivity.
  - destruct (Nat.eqb_spec n l); subst.
    + inversion Hnotbound; subst; congruence.
    + rewrite IHt; auto.
      destruct (Nat.eqb_spec n m); subst.
      * inversion Hnotfree; subst; congruence.
      * rewrite not_in_subst_l_infer_fail; auto. reflexivity.
        inversion Hnotfree; subst. apply not_in_not_bound_in; auto.
      * inversion Hnotbound; subst; auto.
      * inversion Hnotfree; subst; auto.
Qed.

Lemma infer_fail_alpha_convert {A : Type} (t : tree A) (g : nat -> nat) (m : nat) :
  wf_tree' t ->
  (forall x y : nat, g x = g y -> x = y) ->
  (forall x, (x < g x)%nat) ->
  (forall l, bound_in l t -> ~ label_in (g l) t) ->
  not_bound_in m t ->
  (forall l, bound_in l t -> (m < l)%nat) ->
  infer_fail m (alpha_convert g t) == infer_fail m t.
Proof.
  revert m.
  induction t; simpl; intros m Hwf Hinj Hlt Hnotin Hnotbound Hbound_lt;
    try reflexivity; inversion Hwf; subst.
  - rewrite IHt1, IHt2; auto; try reflexivity.
    + intros l Hbound.
      inversion Hnotbound; subst.
      intro HC.
      apply label_in_bound_or_free in HC.
      eapply Hnotin.
      apply bound_in_choice2; eauto.
      destruct HC as [Hbound'|Hfree].
      * apply label_in_choice2. apply bound_in_label_in; auto.
      * apply label_in_choice2. apply free_in_label_in; auto.
    + apply bound_in_not_bound_in; intro HC.
      apply bound_in_not_bound_in in Hnotbound; apply Hnotbound.
      solve [constructor; auto].
    + intros; apply Hbound_lt; solve [constructor; auto].
    + intros l Hbound HC; eapply Hnotin; constructor; eauto.
    + apply bound_in_not_bound_in; intro HC.
      apply bound_in_not_bound_in in Hnotbound.
      apply Hnotbound; constructor; auto.
    + intros; apply Hbound_lt; constructor; auto.
  - assert (H': infer_fail m (subst_l n (g n) (alpha_convert g t)) ==
                infer_fail m t).
    { pose proof Hnotin as Hnotin'.
      specialize (Hnotin n (bound_in_fix1 _ _)).
      inversion Hnotbound; subst.
      rewrite not_in_subst_l_infer_fail; auto.
      - apply IHt; auto.
        + intros l Hbound.
          destruct (Nat.eqb_spec l n); subst.
          * specialize (Hnotin' n (bound_in_fix1 _ _)); auto.
            intro HC. apply Hnotin'. constructor; auto.
            specialize (Hlt n); lia.
          * specialize (Hnotin' l (bound_in_fix2 n0 Hbound)).
            intro HC; apply Hnotin'. 
            destruct (Nat.eqb_spec (g l) n); subst; constructor; auto.
        + intros l Hbound. apply Hbound_lt.
          destruct (Nat.eqb_spec l n); subst; constructor; auto.
      - specialize (Hbound_lt n (bound_in_fix1 _ _)).
        intro HC; subst. specialize (Hlt n); lia.
      - apply not_bound_in_alpha_convert; auto.
        apply bound_in_not_bound_in; intro HC; apply H2 in HC; lia. }
    rewrite H'; clear H'.
    assert (H': infer_fail (g n) (subst_l n (g n) (alpha_convert g t)) ==
                infer_fail n t).
    { rewrite infer_fail_subst_l.
      - apply IHt; auto.
        + intros l Hbound.
          destruct (Nat.eqb_spec l n); subst.
          specialize (Hnotin n (bound_in_fix1 _ _)).
            intro HC; apply Hnotin; constructor; auto.
            specialize (Hlt n); lia.
          * specialize (Hnotin l (bound_in_fix2 n0 Hbound)).
            intro HC. apply Hnotin.
            destruct (Nat.eqb_spec (g l) n); subst; constructor; auto.
        + apply bound_in_not_bound_in; intro HC.
          apply H2 in HC; lia.
      - apply bound_in_not_bound_in; intro HC.
        apply bound_in_alpha_convert_exists in HC.
        destruct HC as [l [Hbound ?]]; subst.
        apply H2 in Hbound.
        specialize (Hlt l); lia.
      - apply not_in_alpha_convert; auto.
        + intros x HC; specialize (Hlt x); lia.
        + apply bound_in_not_bound_in; intro HC.
          apply H2 in HC; lia.
        + apply free_in_not_free_in; intro HC.
          apply H3 in HC. specialize (Hlt n); lia. }
    rewrite H'; reflexivity.
Qed.

Lemma not_in_alpha_convert_infer {A : Type} (t : tree A) (f : A -> Q) (g : nat -> nat) :
  wf_tree' t ->
  (forall x : nat, (x < g x)%nat) ->
  (forall x y : nat, g x = g y -> x = y) ->
  (forall l, bound_in l t -> not_in (g l) t) ->
  infer_f f (alpha_convert g t) == infer_f f t.
Proof.
  induction t; intros Hwf Hlt Hinj H0; simpl;
    try reflexivity; inversion Hwf; subst.
  - rewrite IHt1, IHt2; try reflexivity; auto; intros l Hbound.
    + specialize (H0 l (bound_in_choice2 _ _ Hbound)).
      inversion H0; subst; auto.
    + specialize (H0 l (bound_in_choice1 _ _ Hbound)).
      inversion H0; subst; auto.
  - assert (H': infer_f f (subst_l n (g n) (alpha_convert g t)) ==
                infer_f f (alpha_convert g t)).
    { specialize (H0 n (bound_in_fix1 _ _)).
      inversion H0; subst.
      apply not_in_subst_l_infer; auto.
      apply not_bound_in_alpha_convert; auto.
      apply bound_in_lt_not_bound_in; auto. }
    rewrite H'; clear H'.
    rewrite IHt; auto.
    assert (H': infer_fail (g n) (subst_l n (g n) (alpha_convert g t)) ==
                infer_fail n (alpha_convert g t)).
    { specialize (H0 n (bound_in_fix1 _ _)).
      inversion H0; subst.
      apply infer_fail_subst_l.
      - apply bound_in_not_bound_in; intro HC.
        (* H3 implies that n is less than anything bound in t, but HC
        implies that it's greater than the least thing in t, yielding
        a contradiction. *)
        apply bound_in_alpha_convert_exists in HC.
        destruct HC as [m [HC0 HC1]]; subst.
        apply H3 in HC0.
        specialize (Hlt m). lia.
      - apply not_in_alpha_convert; auto.
        + intro x; specialize (Hlt x); lia.
        + apply bound_in_lt_not_bound_in; auto.
        + apply not_in_not_free_in; auto. }
    rewrite H'; clear H'.
    rewrite infer_fail_alpha_convert; auto.
    + reflexivity.
    + intros l Hbound.
      apply label_in_not_in.
      destruct (Nat.eqb_spec l n); subst.
      * specialize (H0 n (bound_in_fix1 _ _)); inversion H0; subst; auto.
      * specialize (H0 l (bound_in_fix2 n0 Hbound)); inversion H0; subst; auto.
    + apply bound_in_not_bound_in; intro HC.
      apply H3 in HC; lia.
    + intros l Hbound.
      destruct (Nat.eqb_spec l n); subst.
      * specialize (H0 n (bound_in_fix1 _ _)).
        inversion H0; subst; auto.
      * specialize (H0 l (bound_in_fix2 n0 Hbound)).
        inversion H0; subst; auto.
Qed.

Lemma infer_fail_fbind_prod {A : Type} (t1 t2 : tree A) (l : nat) :
  not_bound_in l t1 ->
  (forall m, bound_in m t1 -> not_in m t2) ->
  infer_fail l (fbind l t1 t2) == infer_fail l t1 * infer_fail l t2.
Proof.
  revert l. induction t1; intros l Hnotbound Hnotin.
  - simpl; lra.
  - simpl; destruct (Nat.eqb_spec l n); subst; simpl.
    + rewrite Nat.eqb_refl; lra.
    + destruct (Nat.eqb_spec n l); subst.
      * congruence.
      * lra.
  - inversion Hnotbound; subst; simpl; rewrite IHt1_1, IHt1_2; auto;
      try lra; intros m Hbound; apply Hnotin; solve [constructor; auto].
  - inversion Hnotbound; subst. simpl.
    destruct (Nat.eqb_spec n l); subst.
    + congruence.
    + rewrite IHt1; auto.
      * rewrite infer_fail_fbind_t1; auto.
        ++ destruct (Qeq_dec (infer_fail n t1) 1).
           ** rewrite q; rewrite Qminus_cancel, 2!Qdiv_0_den; lra.
           ** field; lra.
        ++ apply Hnotin; constructor.
        ++ intros m Hbound; apply Hnotin.
           destruct (Nat.eqb_spec m n); subst; constructor; auto.
      * intros m Hbound; apply Hnotin.
        destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Lemma infer_fail_tree_chain_Qpow {A : Type} (t : tree A) (l n : nat) :
  wf_tree' t ->
  (forall n m, free_in n t -> bound_in m t -> (n < m)%nat) ->
  (forall n, bound_in n t -> (l < n)%nat) ->
  infer_fail l (tree_chain t l n) == infer_fail l t * Qpow (infer_fail l t) n.
Proof.
  induction n; intros Hwf Hlt' Hlt.
  - simpl; field.
  - assert (H': infer_fail l (tree_chain t l (S n)) ==
                infer_fail l (tree_chain t l n) * infer_fail l t).
    { assert (not_bound_in l t).
      { apply bound_in_not_bound_in; intro HC.
        apply Hlt in HC; lia. }
      simpl; rewrite infer_fail_fbind_prod.
      - rewrite infer_fail_alpha_convert; auto.
        + reflexivity.
        + intros; lia.
        + intros; lia.
        + intros m Hbound HC.
          apply label_in_bound_or_free in HC.
          destruct HC as [Hbound'|Hfree].
          * (* Hbound and Hbound' contradict. *)
            apply bound_labels_spec, list_max_spec in Hbound.
            apply bound_labels_spec, list_max_spec in Hbound'.
            assert ((list_max (bound_labels t) <=
                     list_max (all_labels (tree_chain t l n)))%nat).
            { apply list_max_monotone; intros x Hin.
              apply bound_labels_spec in Hin.
              apply all_labels_spec, label_in_bound_or_free; left.
              apply bound_in_tree_chain; auto. }
            lia.
          * specialize (Hlt' _ _ Hfree Hbound); lia.
      - (* anything bound in (tree_chain t l n) must either be bound
           in t or greater than anything bound in t, but we know l is
           strictly less than anything bound in t, so it can't be
           bound in the chain. *)
        apply bound_in_not_bound_in; intro HC.
        pose proof HC as HC'.
        apply bound_in_tree_chain_exists in HC'.
        apply bound_in_tree_chain_lt in HC; auto.
        destruct HC' as [m Hbound].
        destruct HC as [HC|HC].
        apply bound_in_not_bound_in in H; congruence.
        specialize (Hlt m Hbound); specialize (HC m Hbound); lia.
      - intros m Hbound.
        apply not_in_not_bound_and_not_free. split.
        + apply not_free_in_alpha_convert; auto.
          apply free_in_not_free_in; intro HC.
          (* From (free_in n t -> bound_in m t -> n < m) we can derive
             (free_in n t -> bound_in m (tree_chain t l i) -> n < m),
             leading to a contradictory proof of (m < m). *)
          eapply free_in_bound_in_chain_lt in Hlt'; eauto; lia.
        + apply not_bound_in_alpha_convert_lt; intro x.
          apply bound_in_label_in, all_labels_spec, list_max_spec in Hbound.
          lia. }
    rewrite H'; clear H'.
    rewrite IHn; auto; simpl; lra.
Qed.

Lemma infer_chain_geometric {A : Type} (t : tree A) (f : A -> Q) (l : nat) :
  wf_tree' t ->
  (forall n m : nat, free_in n t -> bound_in m t -> (n < m)%nat) ->
  (free_in l t) ->
  infer_f f ∘ tree_chain t l ==f geometric_series (infer_f f t) (infer_fail l t).
Proof.
  intros Hwf Hlt Hfree n. unfold compose. revert Hwf Hlt Hfree. revert t f l.
  induction n; intros t f l Hwf Hlt Hfree.
  - simpl. unfold tree_chain. simpl. reflexivity.
  - simpl. rewrite infer_f_fbind_geom.
    + rewrite IHn; auto. apply Qplus_inj_l.
      rewrite infer_fail_tree_chain_Qpow; auto.
      * rewrite not_in_alpha_convert_infer; auto; try (intros; lia); try field.
        intros m Hbound.
        apply list_max_lt_not_in.
        assert (list_max (all_labels t) <= list_max (all_labels (tree_chain t l n)))%nat.
        { apply list_max_subset.
          intros x Hin; apply all_labels_tree_chain_subset; auto. }
        lia.
    + intros n0 Hbound.
      apply not_in_not_bound_or_free. intros [HC|HC].
      * pose proof Hbound as Hbound'.
        eapply bound_in_tree_chain_lt in Hbound'; auto.
        apply free_in_alpha_convert in HC; auto.
        destruct Hbound' as [Hbound'|Hbound_lt].
        ++ eapply Hlt in HC; eauto. lia.
        ++ apply bound_in_tree_chain_exists in Hbound.
           destruct Hbound as [m Hbound].
           specialize (Hlt _ _ HC Hbound).
           apply Hbound_lt in Hbound; lia.
        ++ intros; lia.
      * apply bound_in_alpha_convert_lt in HC.
        apply bound_in_label_in, all_labels_spec, list_max_spec in Hbound.
        lia.
    + clear IHn. induction n; simpl; auto.
      * apply bound_in_not_bound_in; intro HC.
        specialize (Hlt l l Hfree HC); lia.
      * destruct (free_in_dec l t); auto.
        ++ apply not_bound_in_fbind; auto.
           apply bound_in_not_bound_in. intro HC.
           apply bound_in_alpha_convert_exists in HC.
           destruct HC as [m [HC0 HC1]].
           specialize (Hlt l m H HC0); lia.
        ++ rewrite not_free_fbind; auto.
           apply not_free_tree_chain; auto.
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

Lemma infer_f_fail_chain {A : Type} (t : tree A) (f : A -> Q) (l n : nat) :
  wf_tree' t ->
  not_bound_in l (tree_chain t l n) ->
  (forall n m, bound_in m t -> free_in n t -> (n < m)%nat) ->
  infer_fail l t == 1 ->
  infer_f f (tree_chain t l n) == 0.
Proof.
  induction n; simpl; intros Hwf Hnotbound Hle Heq.
  - eapply infer_f_fail; eauto. apply wf_tree'_wf_tree; auto.
  - rewrite infer_f_fbind_geom; auto.
    + rewrite IHn; auto.
      rewrite not_in_alpha_convert_infer; auto.
      * rewrite infer_f_fail; eauto.
        ++ lra.
        ++ apply wf_tree'_wf_tree; auto.
        ++ apply bound_in_not_bound_in; intro HC.
           apply bound_in_not_bound_in in Hnotbound; apply Hnotbound.
           apply bound_in_fbind, bound_in_tree_chain; auto.
      * intros; lia.
      * intros; lia.
      * intros m Hbound.
        apply not_in_not_bound_and_not_free; split.
        ++ apply free_in_not_free_in; intro HC.
           eapply Hle in HC; eauto; lia.
        ++ apply bound_in_not_bound_in; intro HC.
           apply bound_labels_spec, list_max_spec in Hbound.
           apply bound_labels_spec, list_max_spec in HC.
           assert (list_max (bound_labels t) <=
                   list_max (all_labels (tree_chain t l n)))%nat.
           { apply list_max_monotone.
             intros y Hin.
             apply bound_labels_leq_all_labels.
             apply bound_labels_spec. apply bound_in_tree_chain.
             apply bound_labels_spec; auto. }
           lia.
      * apply bound_in_not_bound_in; intro HC.
        apply bound_in_not_bound_in in Hnotbound; apply Hnotbound.
        apply bound_in_fbind; auto.
    + intros m Hbound.
      apply label_in_not_in; intro HC.
      apply label_in_bound_or_free in HC; destruct HC as [HC|HC].
      * apply bound_in_alpha_convert_lt in HC.
        apply bound_in_label_in in Hbound.
        apply all_labels_spec in Hbound.
        apply list_max_spec in Hbound. lia.
      * pose proof Hbound as Hbound'.
        apply bound_in_tree_chain_exists in Hbound.
        apply bound_in_tree_chain_lt in Hbound'; auto.
        apply free_in_alpha_convert in HC; auto.
        ++ destruct Hbound' as [Hbound'|Hbound'].
           ** eapply Hle in HC; eauto; lia.
           ** destruct Hbound as [m' Hbound].
             specialize (Hle m m' Hbound HC).
             specialize (Hbound' m' Hbound). lia.
        ++ intros; lia.
    + apply bound_in_not_bound_in; intro HC.
        apply bound_in_not_bound_in in Hnotbound; apply Hnotbound.
        apply bound_in_fbind; auto.
Qed.

(* Inference computes the supremum of the chain of unnormalized
   expectations on successive approximations of the input tree (wrt a
   particular label). *)
Lemma infer_f_supremum {A : Type} (t : tree A) (f : A -> Q) (l : nat) :
  expectation f ->
  wf_tree' t ->
  (forall m, bound_in m t -> (l < m)%nat) -> (* implies l not bound in chain *)
  (forall n m : nat, bound_in m t -> free_in n t -> (n < m)%nat) ->
  supremum (infer_f f t / (1 - infer_fail l t)) (infer_f f ∘ tree_chain t l).
Proof.
  intros Hexp Hwf Hnotbound Hlt.
  destruct (free_in_dec l t).
  { destruct (Qeq_dec (infer_fail l t) 1).
    - eapply Proper_supremum_Q.
      + rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity.
      + unfold compose. intro n. transitivity (const 0 n).
        * unfold const. apply infer_f_fail_chain; auto.
          apply bound_in_not_bound_in; intro HC.
          pose proof HC as HC'.
          apply bound_in_tree_chain_lt in HC; auto; destruct HC as [HC|HC].
          ++ apply Hnotbound in HC; lia.
          ++ apply bound_in_tree_chain_exists in HC'.
             destruct HC' as [x HC'].
             specialize (Hnotbound x HC'); specialize (HC x HC'); lia.
        * reflexivity.
      + apply const_supremum; intros; unfold const, equ, leq; simpl; lra.
    - assert (infer_fail l t <= 1).
      { apply infer_fail_le_1; auto.
        - apply wf_tree'_wf_tree; auto.
        - apply bound_in_not_bound_in; intro HC.
          apply Hnotbound in HC; lia. }
      apply geometric_supremum.
      + apply infer_f_expectation_0_le; auto; apply wf_tree'_wf_tree; auto.
      + apply infer_fail_0_le; auto.
        * apply wf_tree'_wf_tree; auto.
        * apply bound_in_not_bound_in; intro HC.
          apply Hnotbound in HC; lia.
      + lra.
      + apply infer_chain_geometric; auto. }
  { apply const_supremum.
    intro i. unfold equ, leq, compose; simpl.
    rewrite not_free_in_tree_chain; auto.
    rewrite not_in_infer_fail.
    rewrite Qminus_0_r, Qdiv_1_den; lra.
    apply not_in_not_bound_and_not_free; split; auto.
    apply bound_in_not_bound_in; intro HC.
    apply Hnotbound in HC; lia. }
Qed.

Theorem infer_f_supremum_expectation {A : Type} (k : St -> tree A) (f : A -> Q) (l : nat) :
  expectation f ->
  (forall st, wf_tree' (k st)) ->
  (forall st m, bound_in m (k st) -> (l < m)%nat) -> (* implies l not bound in chain *)
  (forall st n m, bound_in m (k st) -> free_in n (k st) -> (n < m)%nat) ->
  supremum (fun st => infer_f f (k st) / (1 - infer_fail l (k st)))
           (fun i => fun st => infer_f f (tree_chain (k st) l i)).
Proof.
  intros Hexp Hwf Hbound_lt Hfree_lt.
  apply supremum_pointwise.
  intro st. apply infer_f_supremum; auto; intros.
  - eapply Hbound_lt; eauto.
  - eapply Hfree_lt; eauto.
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

Lemma infer_lib_chain_geometric {A : Type} (t : tree A) (f : A -> Q) (l : nat) :
  wf_tree' t ->
  (forall n m : nat, free_in n t -> bound_in m t -> (n < m)%nat) ->
  (free_in l t) ->
  infer_f_lib' f ∘ tree_chain t l
  ==f geometric_series (infer_f_lib f t) (infer_fail_lib l t).
Proof.
Admitted.

Lemma infer_f_lib_supremum {A : Type} (t : tree A) (f : A -> Q) (l : nat) :
  expectation f ->
  wf_tree' t ->
  (forall m, bound_in m t -> (l < m)%nat) -> (* implies l not bound in chain *)
  (forall n m : nat, bound_in m t -> free_in n t -> (n < m)%nat) ->
  infimum (infer_f_lib f t / (1 - infer_fail_lib l t))
          (infer_f_lib' f ∘ tree_chain t l).
Proof.
Admitted.

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
(*   revert e f m. *)
(*   induction t; intros e f m Hnotbound; *)
(*     unfold tree_bind; simpl; inversion Hnotbound; subst. *)
(*   - destruct (e a); reflexivity. *)
(*   - reflexivity. *)
(*   - rewrite IHt1, IHt2; eauto; reflexivity. *)
(*   - rewrite IHt; eauto. *)
(*     generalize (@not_bound_in_infer_fail_tree_bind t e n m (not_eq_sym H2) H3). *)
(*     intro Heq; rewrite Heq; reflexivity. *)
(* Qed. *)
Admitted.

Lemma infer_f_proper {A : Type} (t : tree A) (f g : A -> Q) :
  f ==f g ->
  infer_f f t == infer_f g t.
Proof.
  induction t; unfold f_Qeq; simpl; intro Heq.
  - apply Heq.
  - reflexivity.
  - rewrite IHt1, IHt2; auto; reflexivity.
  - rewrite IHt; auto; reflexivity.
Qed.

Lemma infer_f_lib'_bind {A B : Type} (f : B -> Q) (t : tree A) (k : A -> tree B) :
  (forall n x, bound_in n t -> not_in n (k x)) ->
  infer_f_lib' (infer_f_lib' f ∘ k) t == infer_f_lib' f (tree_bind t k).
Admitted.

Lemma infer_f_lib_proper {A : Type} (t : tree A) (f g : A -> Q) :
  f ==f g ->
  infer_f_lib f t == infer_f_lib g t.
Admitted.

Lemma infer_f_lib'_proper {A : Type} (t : tree A) (f g : A -> Q) :
  f ==f g ->
  infer_f_lib' f t == infer_f_lib' g t.
Proof.
(*   induction t; unfold f_Qeq; simpl; intro Heq. *)
(*   - apply Heq. *)
(*   - reflexivity. *)
(*   - rewrite IHt1, IHt2; auto; reflexivity. *)
(*   - rewrite IHt; auto; reflexivity. *)
(* Qed. *)
Admitted.
