Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Require Import infer.
Require Import order.
Require Import Q.
Require Import tree.

(** Tree reduction. *)

Fixpoint coalesce_children {A : Type} `{EqType A} (t : tree A) : tree A :=
  match t with
  | Choice p t1 t2 =>
    let t1' := coalesce_children t1 in
    let t2' := coalesce_children t2 in
    if Qeq_bool p (1#2) && tree_eqb t1' t2' then t1' else Choice p t1' t2'
  | Fix n t1 => Fix n (coalesce_children t1)
  | _ => t
  end.

Lemma coalesce_children_bound_in_iff {A : Type} `{EqType A} (t : tree A) (n : nat) :
  bound_in n t <-> bound_in n (coalesce_children t).
Proof.
  split.
  - induction 1; simpl; try solve[constructor; auto];
      destruct (Qeq_bool p (1#2)); simpl; try solve[constructor; auto];
        destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
        try constructor; auto; rewrite t; auto.
  - induction t; simpl; auto; intro Hbound.
    + destruct (Qeq_bool q (1#2)); simpl in *;
        destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
        inversion Hbound; subst; solve [constructor; auto].
    + inversion Hbound; subst; constructor; auto.
Qed.

Lemma coalesce_children_free_in_iff {A : Type} `{EqType A} (t : tree A) (n : nat) :
  free_in n t <-> free_in n (coalesce_children t).
Proof.
  split.
  - induction 1; simpl; try solve[constructor; auto];
      destruct (Qeq_bool p (1#2)); simpl;
        destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
        try constructor; auto; rewrite t; auto.
  - induction t; simpl; auto; intro Hfree.
    + destruct (Qeq_bool q (1#2)); simpl in *;
        destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
        inversion Hfree; subst; solve [constructor; auto].
    + inversion Hfree; subst; constructor; auto.
Qed.

Lemma coalesce_children_wf_tree {A : Type} `{EqType A} (t : tree A) :
  wf_tree t ->
  wf_tree (coalesce_children t).
Proof.
  induction 1; try solve[constructor]; simpl.
  - destruct (Qeq_bool p (1#2)); simpl; try constructor; auto.
    + destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
        try constructor; auto.
  - constructor; auto.
    apply bound_in_not_bound_in; intro HC.
    apply bound_in_not_bound_in in H1.
    apply H1, coalesce_children_bound_in_iff; auto.
Qed.

Lemma coalesce_children_wf_tree' {A : Type} `{EqType A} (t : tree A) :
  wf_tree' t ->
  wf_tree' (coalesce_children t).
Proof.
  induction 1; try solve[constructor]; simpl.
  - destruct (Qeq_bool p (1#2)); simpl; try constructor; auto.
    + destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
        try constructor; auto.
  - constructor; auto.
    + intros m Hbound; apply coalesce_children_bound_in_iff in Hbound; auto.
    + intros m Hfree; apply coalesce_children_free_in_iff in Hfree; auto.
Qed.

Lemma coalesce_children_unbiased {A : Type} `{EqType A} (t : tree A) :
  unbiased t ->
  unbiased (coalesce_children t).
Proof.
  induction 1; try constructor; auto; simpl.
  rewrite H0, Qeq_bool_refl; simpl.
  destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2));
    try constructor; auto.
Qed.

Lemma coalesce_children_infer_fail {A : Type} `{EqType A} (t : tree A) (n : nat) :
  wf_tree t ->
  infer_fail n (coalesce_children t) == infer_fail n t.
Proof.
  intro Hwf; revert n.
  induction t; intro m; simpl; try lra; inversion Hwf; subst.
  - destruct (Qeq_bool q (1#2)) eqn:Hq; simpl.
    + destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2)).
      * rewrite <- IHt1, <- IHt2; auto.
        rewrite tree_eq_infer_fail; eauto; lra.
      * simpl; rewrite IHt1, IHt2; auto; reflexivity.
    + rewrite IHt1, IHt2; auto; reflexivity.
  - rewrite 2!IHt; auto; reflexivity.
Qed.

Lemma coalesce_children_infer_f {A : Type} `{EqType A} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer_f f (coalesce_children t) == infer_f f t.
Proof.
  intro Hwf; induction t; simpl; try lra; inversion Hwf; subst.
  - destruct (Qeq_bool q (1#2)) eqn:Hq; simpl.
    + destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2)).
      * rewrite <- IHt1, <- IHt2; auto.
        rewrite tree_eq_infer_f; eauto; lra.
      * simpl; rewrite IHt1, IHt2; auto; reflexivity.
    + rewrite IHt1, IHt2; auto; reflexivity.
  - rewrite IHt, coalesce_children_infer_fail; auto; reflexivity.
Qed.

Lemma coalesce_children_infer_f_lib {A : Type} `{EqType A} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer_f_lib f (coalesce_children t) == infer_f_lib f t.
Proof.
  intro Hwf; induction t; simpl; try lra; inversion Hwf; subst.
  - destruct (Qeq_bool q (1#2)) eqn:Hq; simpl.
    + destruct (tree_eqb_spec (coalesce_children t1) (coalesce_children t2)).
      * rewrite <- IHt1, <- IHt2; auto.
        rewrite tree_eq_infer_f_lib; eauto; lra.
      * simpl; rewrite IHt1, IHt2; auto; reflexivity.
    + rewrite IHt1, IHt2; auto; reflexivity.
  - rewrite coalesce_children_infer_fail; auto.
    destruct (Qeq_bool (infer_fail n t) 1); try lra.
    rewrite IHt, coalesce_children_infer_fail; auto.
    reflexivity.
Qed.

Lemma coalesce_children_infer {A : Type} `{EqType A} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer f (coalesce_children t) == infer f t.
Proof.
  intro Hwf.
  unfold infer. rewrite coalesce_children_infer_f; auto.
  rewrite coalesce_children_infer_f_lib; auto.
  reflexivity.
Qed.


(** Reduce fractions in choices. Do this before de-biasing. *)

Fixpoint reduce_choices {A : Type} (t : tree A) : tree A :=
  match t with
  | Leaf _ => t
  | Fail _ _ => t
  | Choice p t1 t2 =>
    if Qeq_bool p 1 then reduce_choices t1 else
      if Qeq_bool p 0 then reduce_choices t2 else
        Choice (Qred p) (reduce_choices t1) (reduce_choices t2)
  | Fix n t1 => Fix n (reduce_choices t1)
  end.

Lemma reduce_choices_not_0 {A : Type} (t : tree A) (p : Q) :
  p_in p (reduce_choices t) ->
  ~ (p == 0).
Proof.
  induction t; simpl; intro Hin; try solve[inversion Hin; auto].
  destruct (Qeq_bool q 1); auto.
  destruct (Qeq_bool q 0) eqn:Hq0; auto.
  inversion Hin; subst; auto.
  apply Qeq_bool_neq in Hq0; intro HC; apply Hq0.
  rewrite <- Qred_correct; auto.
Qed.

Lemma reduce_choices_not_1 {A : Type} (t : tree A) (p : Q) :
  p_in p (reduce_choices t) ->
  ~ (p == 1).
Proof.
  induction t; simpl; intro Hin; try solve[inversion Hin; auto].
  destruct (Qeq_bool q 1) eqn:Hq1; auto.
  destruct (Qeq_bool q 0); auto.
  inversion Hin; subst; auto.
  apply Qeq_bool_neq in Hq1; intro HC; apply Hq1.
  rewrite <- Qred_correct; auto.
Qed.

Lemma reduce_choices_reduced {A : Type} (t : tree A) (p : Q) :
  p_in p (reduce_choices t) ->
  p = Qred p.
Proof.
  induction t; simpl; intro Hin; try solve[inversion Hin; auto].
  destruct (Qeq_bool q 1) eqn:Hq1; auto.
  destruct (Qeq_bool q 0) eqn:Hq0; auto.
  inversion Hin; subst; auto.
  rewrite Q.Qred_idempotent; reflexivity.
Qed.

Lemma reduce_choices_infer_fail {A : Type} (t : tree A) (n : nat) :
  infer_fail n (reduce_choices t) == infer_fail n t.
Proof.
  revert n; induction t; intro m; simpl; try lra.
  - destruct (Qeq_bool q 1) eqn:Hq1; simpl.
    + rewrite Qeq_bool_iff in Hq1; rewrite Hq1, IHt1; lra.
    + destruct (Qeq_bool q 0) eqn:Hq0; simpl.
      * rewrite Qeq_bool_iff in Hq0; rewrite Hq0, IHt2; lra.
      * rewrite Qred_correct, IHt1, IHt2; reflexivity.
  - rewrite 2!IHt; reflexivity.
Qed.

Lemma reduce_choices_infer_f {A : Type} (t : tree A) (f : A -> Q) :
  infer_f f (reduce_choices t) == infer_f f t.
Proof.
  induction t; simpl; try lra.
  - destruct (Qeq_bool q 1) eqn:Hq1; simpl.
    + rewrite Qeq_bool_iff in Hq1; auto; nra.
    + destruct (Qeq_bool q 0) eqn:Hq0; simpl.
      * rewrite Qeq_bool_iff in Hq0; auto; nra.
      * rewrite Qred_correct, IHt1, IHt2; reflexivity.
  - rewrite reduce_choices_infer_fail, IHt; reflexivity.
Qed.

Lemma reduce_choices_infer_f_lib {A : Type} (t : tree A) (f : A -> Q) :
  infer_f_lib f (reduce_choices t) == infer_f_lib f t.
Proof.
  induction t; simpl; try lra.
  - destruct (Qeq_bool q 1) eqn:Hq1; simpl.
    + rewrite Qeq_bool_iff in Hq1; auto; nra.
    + destruct (Qeq_bool q 0) eqn:Hq0; simpl.
      * rewrite Qeq_bool_iff in Hq0; auto; nra.
      * rewrite Qred_correct, IHt1, IHt2; reflexivity.
  - rewrite reduce_choices_infer_fail.
    destruct (Qeq_bool (infer_fail n t) 1) eqn:Heq; simpl; try lra.
    rewrite reduce_choices_infer_fail, IHt; reflexivity.
Qed.

Lemma reduce_choices_infer {A : Type} (t : tree A) (f : A -> Q) :
  infer f (reduce_choices t) == infer f t.
Proof.
  unfold infer.
  rewrite reduce_choices_infer_f, reduce_choices_infer_f_lib.
  reflexivity.
Qed.

(** TODO: Eliminate redundant fail nodes immediately under a fix? E.g.:

    Fix n          Fix n
      |              |
   /    \     =>     t     =>    t (if Fail n ∉ t) 
Fail n   t

*)

Fixpoint reduce_fail {A : Type} (t : tree A) : tree A :=
  match t with
  | Choice p t1 t2 => Choice p (reduce_fail t1) (reduce_fail t2)
  | Fix n t1 =>
    let t1' := reduce_fail t1 in
    match t1' with
    | Choice p (Fail _ m) r =>
      if n =? m then Fix n r else Fix n t1'
    | Choice p l (Fail _ m) =>
      if n =? m then Fix n l else Fix n t1'
    | _ => Fix n t1'
    end
  | _ => t
  end.

(* TODO: prove reduce_fail preserves inference semantics. *)
(* TODO: assume 0 < p < 1 at choice nodes? *)
(* Lemma reduce_fail_infer_fail {A : Type} (t : tree A) (n : nat) : *)
(*   infer_fail n (reduce_fail t) == infer_fail n t. *)
(* Proof. *)
(*   revert n. *)
(*   induction t; simpl; intro m; try lra. *)
(*   - rewrite IHt1, IHt2; reflexivity. *)
(*   - destruct (reduce_fail t); simpl in *. *)
(*     + rewrite <- IHt; reflexivity. *)
(*     + rewrite 2!IHt; reflexivity. *)
(*     + destruct t0_1; simpl. *)
(*       * destruct t0_2; simpl. *)
(*         -- rewrite <- 2!IHt; simpl; field. *)
(*         -- simpl in IHt. *)
(*            destruct (Nat.eqb_spec n n0); subst. *)
(*            ++ simpl. *)
(*               pose proof (IHt n0) as Hn0. *)
(*               rewrite Nat.eqb_refl in Hn0. *)
(*               rewrite <- Hn0. *)

(*               destruct (Nat.eqb_spec m n0); subst. *)
(*               ** rewrite <- Hn0. *)
(*                  rewrite Qmult_0_r, Qmult_1_r. *)
(*                  rewrite Qplus_0_l. *)
(*                  rewrite Qdiv_0_num. *)
                 
              
(*            simpl. *)
      
(*       * rewrite Qmult_0_r. rewrite 2!Qplus_0_l. *)
(*         assert (H: 1 - (1 - q) == q). *)
(*         { lra. } *)
(*         simpl in IHt. *)
(*         specialize (IHt m). *)
(*         rewrite Qmult_0_r, Qplus_0_l in IHt. rewrite IHt. *)
(*         rewrite <- H. *)
(*         replace (1 - (1 - q)) with q. *)
(* Admitted. *)

(** Eliminate unused fix nodes (for which the bound label never
    appears free within the body). *)
Fixpoint elim_fix {A : Type} (t : tree A) : tree A :=
  match t with
  | Choice p t1 t2 => Choice p (elim_fix t1) (elim_fix t2)
  | Fix n t1 => if negb (free_inb n t1) then t1 else t
  | _ => t
  end.

Lemma elim_fix_infer_fail {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  infer_fail n (elim_fix t) == infer_fail n t.
Proof.
  induction t; simpl; intro Hwf; try lra; inversion Hwf; subst.
  - rewrite IHt1, IHt2; auto; reflexivity.
  - destruct (free_inb_spec n0 t); simpl.
    + reflexivity.
    + rewrite not_in_infer_fail_0 with (l:=n0).
      * rewrite Q.Qminus_0_r, Q.Qdiv_1_den; reflexivity.
      * apply not_in_not_bound_and_not_free; intuition.
        apply free_in_not_free_in; auto.
Qed.

Lemma elim_fix_infer_f {A : Type} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer_f f (elim_fix t) == infer_f f t.
Proof.
  induction t; simpl; intro Hwf; try lra; inversion Hwf; subst.
  - rewrite IHt1, IHt2; auto; reflexivity.
  - destruct (free_inb_spec n t); simpl.
    + reflexivity.
    + rewrite not_in_infer_fail_0 with (l:=n).
      * rewrite Q.Qminus_0_r, Q.Qdiv_1_den; reflexivity.
      * apply not_in_not_bound_and_not_free; intuition.
        apply free_in_not_free_in; auto.
Qed.

Lemma elim_fix_infer_f_lib {A : Type} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer_f_lib f (elim_fix t) == infer_f_lib f t.
Proof.
  induction t; simpl; intro Hwf; try lra; inversion Hwf; subst.
  - rewrite IHt1, IHt2; auto; reflexivity.
  - destruct (free_inb_spec n t) as [H | H]; simpl.
    + reflexivity.
    + rewrite not_in_infer_fail_0; simpl.
      * rewrite not_in_infer_fail_0.
        -- rewrite Q.Qminus_0_r, Q.Qdiv_1_den; reflexivity.
        -- apply not_in_not_bound_and_not_free; intuition.
           apply free_in_not_free_in; auto.
      * apply not_in_not_bound_and_not_free; intuition.
        apply free_in_not_free_in; auto.
Qed.

Lemma elim_fix_infer {A : Type} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer f (elim_fix t) == infer f t.
Proof.
  intro Hwf; unfold infer.
  rewrite elim_fix_infer_f, elim_fix_infer_f_lib; auto; reflexivity.
Qed.

