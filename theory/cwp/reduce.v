Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Require Import infer.
Require Import order.
Require Import tree.

(** Tree reduction. *)

Fixpoint reduce_tree {A : Type} `{EqType A} (t : tree A) : tree A :=
  match t with
  | Choice p t1 t2 =>
    let t1' := reduce_tree t1 in
    let t2' := reduce_tree t2 in
    if Qeq_bool p (1#2) && tree_eqb t1' t2' then t1' else Choice p t1' t2'
  | Fix n t1 => Fix n (reduce_tree t1)
  | _ => t
  end.

Lemma reduce_tree_bound_in_iff {A : Type} `{EqType A} (t : tree A) (n : nat) :
  bound_in n t <-> bound_in n (reduce_tree t).
Proof.
  split.
  - induction 1; simpl; try solve[constructor; auto];
      destruct (Qeq_bool p (1#2)); simpl; try solve[constructor; auto];
        destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
        try constructor; auto; rewrite t; auto.
  - induction t; simpl; auto; intro Hbound.
    + destruct (Qeq_bool q (1#2)); simpl in *;
        destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
        inversion Hbound; subst; solve [constructor; auto].
    + inversion Hbound; subst; constructor; auto.
Qed.

Lemma reduce_tree_free_in_iff {A : Type} `{EqType A} (t : tree A) (n : nat) :
  free_in n t <-> free_in n (reduce_tree t).
Proof.
  split.
  - induction 1; simpl; try solve[constructor; auto];
      destruct (Qeq_bool p (1#2)); simpl;
        destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
        try constructor; auto; rewrite t; auto.
  - induction t; simpl; auto; intro Hfree.
    + destruct (Qeq_bool q (1#2)); simpl in *;
        destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
        inversion Hfree; subst; solve [constructor; auto].
    + inversion Hfree; subst; constructor; auto.
Qed.

Lemma reduce_tree_wf_tree {A : Type} `{EqType A} (t : tree A) :
  wf_tree t ->
  wf_tree (reduce_tree t).
Proof.
  induction 1; try solve[constructor]; simpl.
  - destruct (Qeq_bool p (1#2)); simpl; try constructor; auto.
    + destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
        try constructor; auto.
  - constructor; auto.
    apply bound_in_not_bound_in; intro HC.
    apply bound_in_not_bound_in in H1.
    apply H1, reduce_tree_bound_in_iff; auto.
Qed.

Lemma reduce_tree_wf_tree' {A : Type} `{EqType A} (t : tree A) :
  wf_tree' t ->
  wf_tree' (reduce_tree t).
Proof.
  induction 1; try solve[constructor]; simpl.
  - destruct (Qeq_bool p (1#2)); simpl; try constructor; auto.
    + destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
        try constructor; auto.
  - constructor; auto.
    + intros m Hbound; apply reduce_tree_bound_in_iff in Hbound; auto.
    + intros m Hfree; apply reduce_tree_free_in_iff in Hfree; auto.
Qed.

Lemma reduce_tree_unbiased {A : Type} `{EqType A} (t : tree A) :
  unbiased t ->
  unbiased (reduce_tree t).
Proof.
  induction 1; try constructor; auto; simpl.
  rewrite H0, Qeq_bool_refl; simpl.
  destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2));
    try constructor; auto.
Qed.

Lemma reduce_tree_infer_fail {A : Type} `{EqType A} (t : tree A) (n : nat) :
  wf_tree t ->
  infer_fail n (reduce_tree t) == infer_fail n t.
Proof.
  intro Hwf; revert n.
  induction t; intro m; simpl; try lra; inversion Hwf; subst.
  - destruct (Qeq_bool q (1#2)) eqn:Hq; simpl.
    + destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2)).
      * rewrite <- IHt1, <- IHt2; auto.
        rewrite tree_eq_infer_fail; eauto; lra.
      * simpl; rewrite IHt1, IHt2; auto; reflexivity.
    + rewrite IHt1, IHt2; auto; reflexivity.
  - rewrite 2!IHt; auto; reflexivity.
Qed.

Lemma reduce_tree_infer_f {A : Type} `{EqType A} (t : tree A) (f : A -> Q) :
  wf_tree t ->
  infer_f f (reduce_tree t) == infer_f f t.
Proof.
  intro Hwf; induction t; simpl; try lra; inversion Hwf; subst.
  - destruct (Qeq_bool q (1#2)) eqn:Hq; simpl.
    + destruct (tree_eqb_spec (reduce_tree t1) (reduce_tree t2)).
      * rewrite <- IHt1, <- IHt2; auto.
        rewrite tree_eq_infer_f; eauto; lra.
      * simpl; rewrite IHt1, IHt2; auto; reflexivity.
    + rewrite IHt1, IHt2; auto; reflexivity.
  - rewrite IHt, reduce_tree_infer_fail; auto; reflexivity.
Qed.
