Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Init.Nat.
Require Import PeanoNat.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import Permutation.
Import ListNotations.
Import MonadNotation.
Local Open Scope program_scope.
Local Open Scope monad_scope.

Require Import compile.
Require Import cpGCL.
Require Import infer.
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.

(** This file defines the function "translate_bernoulli" which
    compiles arbitrary trees to equivalent trees containing only
    unbiased choices. The two main theorems,
    [translate_bernoulli_infer_f] and [unbiased_translate_bernoulli],
    are at the bottom of the file. *)

Fixpoint add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) : tree A :=
  match t with
  | Leaf y => Leaf y
  | Fail _ _ => Leaf x
  | Choice p t1 t2 =>
    let t1' := add_to_tree x t1 in
    if tree_eqb t1 t1'
    then Choice p t1 (add_to_tree x t2)
    else Choice p t1' t2
  | Fix n t1 => Fix n (add_to_tree x t1) (* there shouldn't be any Fix nodes *)
  end.

Fixpoint new_tree {A : Type} (lbl n : nat) : tree A :=
  match n with
  | O => Fail _ lbl
  | S n' => Choice (1#2) (new_tree lbl n') (new_tree lbl n')
  end.

Fixpoint list_tree_aux {A : Type} `{EqType A}
         (lbl : nat) (l : list A) (t : tree A) : tree A :=
  match l with
  | [] => t
  | b :: bs =>
    let t' := add_to_tree b t in
    let t'' := if tree_eqb t t'
               then Choice (1#2) t
                           (add_to_tree b (new_tree lbl (heightb t)))
               else t' in
    list_tree_aux lbl bs t''
  end.

Definition list_tree {A : Type} `{EqType A} (lbl : nat) (l : list A) : tree A :=
  list_tree_aux lbl l (Fail _ lbl).

Definition bernoulli_tree_open (lbl n d : nat) : tree bool :=
  list_tree lbl (repeat true n ++ repeat false (d-n)).

Definition bernoulli_tree (lbl n d : nat) : tree bool :=
  Fix lbl (bernoulli_tree_open lbl n d).

Lemma count_infer_f {A : Type} (t : tree A) (f : A -> bool) (n : nat) :
  unbiased t ->
  perfect t ->
  countb f t = n ->
  infer_f (fun x => if f x then 1 else 0) t ==
  Z.of_nat n # Pos.of_nat (terminals t).
Proof.
  revert n.
  induction t; intros m Hu Hp Hc.
  - simpl in *; destruct (f a); subst; field.
  - simpl in *; subst; field.
  - simpl in *.
    inversion Hp; subst.
    inversion Hu; subst.
    specialize (IHt1 (countb f t1) H6 H3 eq_refl).
    specialize (IHt2 (countb f t2) H7 H4 eq_refl).
    rewrite IHt1, IHt2. clear IHt1 IHt2.
    apply (@perfect_congruent_terminals _ _ t1 t2) in H2; auto.
    rewrite H2.
    clear Hp H2 H3 H4.
    rewrite H5. field_simplify_eq.
    apply Q_lem3.
    generalize (terminals_nonzero t2); lia.
  - apply perfect_not_fix with (n0:=n) (t1:=t) in Hp; congruence.
Qed.

Lemma count_infer_fail {A : Type} (t : tree A) (lbl n : nat) :
  unbiased t ->
  perfect t ->
  count_failb lbl t = n ->
  infer_fail lbl t ==
  Z.of_nat n # Pos.of_nat (terminals t).
Proof.
  revert n.
  induction t; intros m Hu Hp Hc.
  - simpl in *; rewrite <- Hc; reflexivity.
  - simpl in *; destruct (Nat.eqb_spec n lbl); subst; reflexivity.
  - simpl in *.
    inversion Hp; subst.
    inversion Hu; subst.
    specialize (IHt1 (count_failb lbl t1) H6 H3 eq_refl).
    specialize (IHt2 (count_failb lbl t2) H7 H4 eq_refl).
    rewrite IHt1, IHt2. clear IHt1 IHt2.
    apply (@perfect_congruent_terminals _ _ t1 t2) in H2; auto.
    rewrite H2.
    clear Hp H2 H3 H4.
    rewrite H5. field_simplify_eq.
    apply Q_lem3.
    generalize (terminals_nonzero t2); lia.
  - apply perfect_not_fix with (n0:=n) (t1:=t) in Hp; congruence.
Qed.

Lemma new_tree_height {A : Type} (lbl n : nat) :
  @heightb A (new_tree lbl n) = n.
Proof.
  induction n; simpl; auto.
  - rewrite IHn, Nat.max_id; reflexivity.
Qed.

Lemma new_tree_perfect {A : Type} (lbl n : nat) :
  @perfect A (new_tree lbl n).
Proof. induction n; simpl; constructor; auto; reflexivity. Qed.

Lemma perfect_new_tree_congruent {A : Type} (lbl : nat) (t : tree A) :
  perfect t ->
  @congruent A A t (new_tree lbl (heightb t)).
Proof.
  intro Hp.
  apply perfect_height_congruent; auto.
  apply new_tree_perfect.
  rewrite new_tree_height; reflexivity.
Qed.

Lemma add_to_tree_congruent {A : Type} `{EqType A} (x : A) (t : tree A) :
  congruent t (add_to_tree x t).
Proof.
  induction t; simpl; try destruct a; try constructor; auto.
  - destruct (tree_eqb t1 (add_to_tree x t1));
      constructor; auto; reflexivity.
Qed.

Lemma list_tree_aux_perfect {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) :
  perfect t ->
  perfect (list_tree_aux lbl l t).
Proof.
  revert t. induction l; auto.
  - intros t Hp. simpl.
    apply IHl.
    destruct (tree_eqb t (add_to_tree a t)).
    + assert (H0: congruent t (add_to_tree a (new_tree lbl (heightb t)))).
      { eapply congruent_trans with (t2:=new_tree lbl (heightb t)).
        apply perfect_new_tree_congruent; auto.
        apply add_to_tree_congruent. }
      constructor; auto.
      * eapply congruent_perfect; eauto.
    + eapply congruent_perfect; eauto.
      apply add_to_tree_congruent.
Qed.

Lemma perfect_bernoulli_tree_open (lbl n d : nat) :
  perfect (bernoulli_tree_open lbl n d).
Proof. apply list_tree_aux_perfect; constructor. Qed.

Lemma unbiased_new_tree {A : Type} (lbl n : nat) :
  @unbiased A (new_tree lbl n).
Proof. induction n; constructor; auto; lra. Qed.

Lemma unbiased_add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) :
  unbiased t ->
  unbiased (add_to_tree x t).
Proof.
  induction 1; simpl; try destruct x0; try constructor; auto.
  destruct (tree_eqb t1 (add_to_tree x t1)); constructor; auto.
Qed.

Lemma unbiased_list_tree_aux {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) :
  unbiased t ->
  unbiased (list_tree_aux lbl l t).
Proof.
  revert t.
  induction l; simpl; auto; intros t Hu.
  apply IHl. destruct (tree_eqb t (add_to_tree a t)).
  - constructor; auto.
    + reflexivity.
    + apply unbiased_add_to_tree, unbiased_new_tree.
  - apply unbiased_add_to_tree; auto.
Qed.

Lemma unbiased_list_tree {A : Type} `{EqType A} (n : nat) (l : list A) :
  unbiased (list_tree n l).
Proof. apply unbiased_list_tree_aux; constructor. Qed.

Lemma unbiased_bernoulli_tree_open (lbl n d : nat) :
  unbiased (bernoulli_tree_open lbl n d).
Proof. apply unbiased_list_tree. Qed.

Lemma add_to_tree_new_tree {A : Type} `{EqType A} (a : A) (lbl n : nat) :
  tree_eqb (new_tree lbl n) (add_to_tree a (new_tree lbl n)) = false.
Proof. induction n; auto; simpl; rewrite 2!IHn; auto. Qed.

Lemma countb_add_to_new_tree {A : Type} `{EqType A}
      (f : A -> bool) (a : A) (lbl n : nat) :
  countb f (add_to_tree a (new_tree lbl n)) =
  ((if f a then 1 else 0) + countb f (new_tree lbl n))%nat.
Proof.
  induction n; auto.
  simpl; rewrite add_to_tree_new_tree; simpl; rewrite IHn; lia.
Qed.

Lemma countb_new_tree {A : Type} (f : A -> bool) lbl n :
  countb f (new_tree lbl n) = O.
Proof. induction n; auto; simpl; rewrite IHn; auto. Qed.

Lemma countb_list_tree_aux {A : Type} `{EqType A}
      (f : A -> bool) (lbl : nat) (l : list A) (t : tree A) :
  countb f (list_tree_aux lbl l t) =
  (countb_list f l + countb f t)%nat.
Proof.
  revert f t. induction l; intros f t; auto.
  simpl. destruct (tree_eqb t (add_to_tree a t)) eqn:H0.
  - rewrite IHl. simpl. clear IHl.
    rewrite countb_add_to_new_tree.
    rewrite countb_new_tree.
    lia.
  - rewrite IHl. clear IHl.
    cut ((countb f (add_to_tree a t))%nat =
         ((if f a then 1 else 0) +
          countb f t)%nat); try lia.
    (* NOTE: countb, add_to_tree *)
    induction t; simpl in *; try congruence.
    + rewrite eqb_refl in H0; congruence.
    + destruct (f a); lia.
    + destruct (tree_eqb t1 (add_to_tree a t1)) eqn:H1.
      * rewrite tree_eqb_refl in H0.
        simpl in H0.
        destruct (Qeq_dec q q).
        -- apply IHt2 in H0; simpl; lia.
        -- congruence.
      * specialize (IHt1 eq_refl); simpl; lia.
    + rewrite Nat.eqb_refl in H0; auto.
Qed.

Lemma list_tree_count {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (f : A -> bool) :
  countb f (list_tree lbl l) = countb_list f l.
Proof.
  unfold list_tree. simpl.
  revert f. induction l; intro f; auto.
  simpl. rewrite <- IHl.
  rewrite 2!countb_list_tree_aux. simpl.
  destruct (f a); auto.
Qed.

Lemma bernoulli_count_n (lbl n d : nat) :
  countb id (bernoulli_tree lbl n d) = n.
Proof.
  unfold bernoulli_tree; simpl; unfold bernoulli_tree_open.
  rewrite list_tree_count.
  rewrite countb_list_app.
  rewrite count_true_n.
  rewrite count_false_0.
  apply Nat.add_0_r.
Qed.

Lemma list_tree_countb {A : Type} `{EqType A} (lbl : nat) (l : list A) :
  countb (const true) (list_tree lbl l) = length l.
Proof.
  unfold list_tree.
  rewrite countb_list_tree_aux; simpl; rewrite Nat.add_0_r.
  induction l; auto; simpl; rewrite IHl; auto.
Qed.

Lemma bernoulli_count_d (lbl n d : nat) :
  (n <= d)%nat ->
  countb (fun _ => true) (bernoulli_tree lbl n d) = d.
Proof.
  intros ?; unfold bernoulli_tree; simpl; unfold bernoulli_tree_open.
  rewrite list_tree_countb, app_length, 2!repeat_length; lia.
Qed.

Lemma bernoulli_tree_open_infer_f (lbl n d : nat) :
  infer_f (fun b => if b:bool then 1 else 0) (bernoulli_tree_open lbl n d) ==
  (Z.of_nat n # Pos.of_nat (terminals (bernoulli_tree_open lbl n d))).
Proof.
  apply count_infer_f.
  - apply unbiased_bernoulli_tree_open.
  - apply perfect_bernoulli_tree_open.
  - apply bernoulli_count_n.
Qed.

Lemma all_fails_new_tree {A : Type} (lbl n : nat) :
  @all_fails A lbl (new_tree lbl n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma all_fails_add_to_tree {A : Type} `{EqType A}
      (lbl : nat) (a : A) (t : tree A) :
  all_fails lbl t ->
  all_fails lbl (add_to_tree a t).
Proof.
  induction t; intro Hall; simpl; auto; inversion Hall; subst.
  - constructor.
  - destruct (tree_eqb t1 (add_to_tree a t1)); constructor; auto.
  - constructor; auto.
Qed.

Lemma all_fails_list_tree_aux {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) :
  all_fails lbl t ->
  all_fails lbl (list_tree_aux lbl l t).
Proof.
  revert t. induction l; intros t Hall; simpl; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl. constructor; auto.
    apply all_fails_add_to_tree, all_fails_new_tree.
  - apply IHl, all_fails_add_to_tree; auto.
Qed.

Lemma list_tree_count_failb {A : Type} `{EqType A} (lbl : nat) (l : list A) :
  count_failb lbl (list_tree lbl l) =
  (terminals (list_tree lbl l) - length l)%nat.
Proof.
  rewrite <- list_tree_countb with (lbl0:=lbl).
  apply all_fails_count_failb.
  apply all_fails_list_tree_aux; constructor; auto.
Qed.

Lemma bernoulli_tree_open_infer_fail (lbl n d : nat) :
  (0 < d)%nat -> (n <= d)%nat ->
  infer_fail lbl (bernoulli_tree_open lbl n d) ==
  Z.of_nat (terminals (bernoulli_tree_open lbl n d) - d) #
           Pos.of_nat (terminals (bernoulli_tree_open lbl n d)).
Proof.
  intros Hlt Hle.
  apply count_infer_fail.
  - apply unbiased_bernoulli_tree_open.
  - apply perfect_bernoulli_tree_open.
  - unfold bernoulli_tree_open.
    set (l := repeat true n ++ repeat false (d - n)).
    assert (Hlen: d = length l).
    { unfold l; rewrite app_length, 2!repeat_length; lia. }
    rewrite Hlen.
    apply list_tree_count_failb.
Qed.

Lemma terminals_add_to_tree_increasing {A : Type} `{EqType A}
      (x : A) (t : tree A) :
  (terminals t <= terminals (add_to_tree x t))%nat.
Proof.
  induction t; simpl; try lia.
  destruct (tree_eqb t1 (add_to_tree x t1)); simpl; lia.
Qed.

Lemma in_tree_add_to_tree {A : Type} `{EqType A} (t : tree A) (x y : A) :
  in_tree x t ->
  in_tree x (add_to_tree y t).
Proof.
  induction t; simpl; intro Hin; auto; inversion Hin; subst;
    try constructor; auto; destruct (tree_eqb t1 (add_to_tree y t1));
      solve [constructor; auto].
Qed.

Lemma neq_in_tree_add_to_tree {A : Type} `{EqType A} (t : tree A) (x : A) :
  ~ tree_eq t (add_to_tree x t) ->
  in_tree x (add_to_tree x t).
Proof.
  induction t; simpl; intro Hneq.
  - exfalso; apply Hneq; constructor.
  - constructor.
  - destruct (tree_eqb t1 (add_to_tree x t1)).
    + apply in_tree_choice2; apply IHt2; intro HC;
        apply Hneq; constructor; auto; reflexivity.
    + apply in_tree_choice1; apply IHt1; intro HC;
        apply Hneq; constructor; auto; reflexivity.
  - constructor; apply IHt; intro HC; apply Hneq; constructor; auto.
Qed.

Lemma neq_add_to_tree {A : Type} `{EqType A} (lbl n : nat) (x : A) :
  ~ tree_eq (new_tree lbl n) (add_to_tree x (new_tree lbl n)).
Proof.
  induction n; simpl.
  - intro HC; inversion HC.
  - destruct (tree_eqb_spec (new_tree lbl n)
                            (add_to_tree x (new_tree lbl n))); try congruence.
    intro HC. inversion HC; subst; congruence.
Qed.

Lemma in_tree_list_tree_aux {A : Type} `{EqType A}
      (x : A) (lbl : nat) (l : list A) (t : tree A) :
  in_tree x t ->
  in_tree x (list_tree_aux lbl l t).
Proof.
  revert t.
  induction l; simpl; intros t Hin; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl; constructor; auto.
  - apply IHl, in_tree_add_to_tree; auto.
Qed.

Lemma in_list_tree_aux {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) (x : A) :
  In x l ->
  in_tree x (list_tree_aux lbl l t).
Proof.
  revert t.
  induction l; simpl; intros t []; subst.
  - destruct (tree_eqb_spec t (add_to_tree x t)).
    + apply in_tree_list_tree_aux.
      apply in_tree_choice2. apply neq_in_tree_add_to_tree.
      apply neq_add_to_tree.
    + apply in_tree_list_tree_aux.
      apply neq_in_tree_add_to_tree; auto.
  - destruct (tree_eqb t (add_to_tree a t)); apply IHl; auto.
Qed.

Lemma in_tree_add_to_tree' {A : Type} `{EqType A} (x y : A) (t : tree A) :
  in_tree x (add_to_tree y t) ->
  x = y \/ in_tree x t.
Proof.
  induction t; simpl; intro Hin.
  - inversion Hin; subst; right; constructor.
  - inversion Hin; subst; left; auto.
  - destruct (tree_eqb t1 (add_to_tree y t1)).
    + inversion Hin; subst.
      * right; solve [constructor; auto].
      * apply IHt2 in H2. destruct H2; auto.
        right; solve [constructor; auto].
    + inversion Hin; subst.
      * apply IHt1 in H2. destruct H2; auto.
        right; solve [constructor; auto].
      * right; solve [constructor; auto].
  - inversion Hin; subst.
    apply IHt in H2. destruct H2; auto.
    right; constructor; auto.
Qed.

Lemma not_in_tree_new_tree {A : Type} `{EqType A} (x : A) (lbl n : nat) :
  ~ in_tree x (new_tree lbl n).
Proof.
  induction n; simpl; intro HC; inversion HC; subst; congruence.
Qed.

Lemma add_to_tree_new_tree_eq {A : Type} `{EqType A} (x y : A) (lbl n : nat) :
  in_tree x (add_to_tree y (new_tree lbl n)) ->
  x = y.
Proof.
  induction n; simpl; intro Hin.
  - inversion Hin; subst; reflexivity.
  - rewrite add_to_tree_new_tree in Hin.
    inversion Hin; subst.
    + apply IHn; auto.
    + exfalso; apply (not_in_tree_new_tree x lbl n); auto.
Qed.

Lemma in_list_tree_aux' {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) (x : A) :
  in_tree x (list_tree_aux lbl l t) ->
  (In x l \/ in_tree x t).
Proof.
  revert t.
  induction l; simpl; intros t Hin.
  - right; auto.
  - destruct (tree_eqb_spec t (add_to_tree a t)).
    + apply IHl in Hin.
      destruct Hin.
      * left; right; auto.
      * inversion H0; subst.
        -- right; auto.
        -- left; left.
           apply add_to_tree_new_tree_eq in H3; auto.
    + apply IHl in Hin.
      destruct Hin.
      * left; right; auto.
      * apply in_tree_add_to_tree' in H0; intuition.
Qed.

Lemma in_list_tree_aux'' {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) (x : A) :
  (forall x, ~ in_tree x t) ->
  in_tree x (list_tree_aux lbl l t) ->
  In x l.
Proof. intros H0 H1; apply in_list_tree_aux' in H1; firstorder. Qed.

(** PLAN: use an alternative construction of the bernoulli tree that
  first builds the tree from a list containing a section of the
  natural numbers (so there are no duplicates) and then maps a
  predicate over that tree to obtain the final result. We can easily
  prove length <= terminals for the section tree and then show that
  terminals is preserved by fmap. *)

Definition seq_tree (lbl n : nat) : tree nat := list_tree lbl (seq 0 n).

Definition bernoulli_tree_open' (lbl n d : nat) : tree bool :=
  fmap (fun i => i <? n) (seq_tree lbl d).

Definition bernoulli_tree' (lbl n d : nat) : tree bool :=
  Fix lbl (bernoulli_tree_open' lbl n d).

Lemma new_tree_fmap {A B : Type} `{EqType A} `{EqType B}
      (f : A -> B) (lbl n : nat) :
  fmap f (new_tree lbl n) = new_tree lbl n.
Proof. induction n; simpl; auto; rewrite IHn; reflexivity. Qed.

Lemma add_to_tree_fmap_new_tree {A B : Type} `{EqType A} `{EqType B}
      (x : A) (f : A -> B) (lbl n : nat) :
  add_to_tree (f x) (new_tree lbl n) = fmap f (add_to_tree x (new_tree lbl n)).
Proof.
  induction n; simpl; auto.
  rewrite 2!add_to_tree_new_tree.
  simpl; rewrite IHn, new_tree_fmap; reflexivity.
Qed.

Lemma new_tree_all_fail {A : Type} (lbl n : nat) :
  @all_fail A (new_tree lbl n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma no_fail_tree_eq_add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) :
  no_fail t <-> tree_eq t (add_to_tree x t).
Proof.
  split.
  - induction 1; simpl.
    + constructor.
    + destruct (tree_eqb_spec t1 (add_to_tree x t1)).
      * constructor; auto; reflexivity.
      * congruence.
    + constructor; auto.
  - induction t; simpl; intro Heq.
    + constructor.
    + inversion Heq.
    + destruct (tree_eqb_spec t1 (add_to_tree x t1)).
      * inversion Heq; subst; constructor; auto.
      * inversion Heq; subst; congruence.
    + inversion Heq; subst; constructor; auto.
Qed.

Lemma tree_eq_congruent'_fmap {A B : Type} `{EqType A} `{EqType B}
      (x : A) (y : B) (t1 : tree A) (t2 : tree B) :
  congruent' t1 t2 ->
  tree_eq t1 (add_to_tree x t1) ->
  tree_eq t2 (add_to_tree y t2).
Proof.
  intros Hcong Heq.
  apply no_fail_tree_eq_add_to_tree.
  apply no_fail_tree_eq_add_to_tree in Heq.
  eapply congruent'_no_fail; eauto.
Qed.

Lemma tree_eq_add_to_tree_fmap {A B : Type} `{EqType A} `{EqType B}
      (f : A -> B) (x : A) (y : B) (t : tree A) :
  tree_eq t (add_to_tree x t) ->
  tree_eq (fmap f t) (add_to_tree y (fmap f t)).
Proof. apply tree_eq_congruent'_fmap, fmap_congruent'. Qed.

Lemma add_to_tree_fmap {A B : Type} `{EqType A} `{EqType B}
      (f : A -> B) (x : A) (t : tree A) :
  add_to_tree (f x) (fmap f t) = fmap f (add_to_tree x t).
Proof.
  induction t; simpl; auto.
  - destruct (tree_eqb_spec (fmap f t1) (add_to_tree (f x) (fmap f t1)));
      destruct (tree_eqb_spec t1 (add_to_tree x t1)).
    + rewrite IHt2; reflexivity.
    + exfalso; apply n.
      eapply tree_eq_congruent'_fmap; eauto.
      apply congruent'_symm, fmap_congruent'.
    + exfalso; apply n.
      apply tree_eq_congruent'_fmap with (x0:=x) (t3:=t1); auto.
      apply fmap_congruent'.
    + rewrite IHt1; reflexivity.
  - rewrite IHt; reflexivity.
Qed.

Lemma congruent'_tree_eq {A B : Type} `{EqType A} `{EqType B}
      (t1 : tree A) (t2 : tree B) (x : A) (y : B) :
  congruent' t1 t2 ->
  tree_eq t1 (add_to_tree x t1) ->
  tree_eq t2 (add_to_tree y t2).
Proof.
  induction 1; simpl; intro Heq.
  - constructor.
  - inversion Heq.
  - destruct (tree_eqb_spec t1 (add_to_tree x t1)); inversion Heq; subst.
    + destruct (tree_eqb_spec t1' (add_to_tree y t1'));
        constructor; auto; reflexivity.
    + congruence.
  - inversion Heq; subst; constructor; auto.
Qed.

Lemma list_tree_aux_map_fmap {A B : Type} `{EqType A} `{EqType B}
      (lbl : nat) (f : A -> B) (l : list A) (t : tree A) :
  list_tree_aux lbl (map f l) (fmap f t) = fmap f (list_tree_aux lbl l t).
Proof.
  revert t.
  induction l; simpl; intro t; auto.
  destruct (tree_eqb_spec (fmap f t) (add_to_tree (f a) (fmap f t))).
  - destruct (tree_eqb_spec t (add_to_tree a t)).
    + rewrite <- IHl; simpl; f_equal; f_equal.
      rewrite add_to_tree_fmap_new_tree, heightb_fmap; reflexivity.
    + subst; exfalso; apply n.
      eapply congruent'_tree_eq; eauto.
      apply congruent'_symm. apply fmap_congruent'.
  - destruct (tree_eqb_spec t (add_to_tree a t)).
    + apply tree_eq_add_to_tree_fmap with (f0:=f) (y:=f a) in t0; congruence.
    + rewrite <- IHl, add_to_tree_fmap; reflexivity.
Qed.

Lemma list_tree_map_fmap {A B : Type} `{EqType A} `{EqType B}
      (lbl : nat) (f : A -> B) (l : list A) :
  list_tree lbl (map f l) = fmap f (list_tree lbl l).
Proof.
  unfold list_tree; simpl.
  rewrite <- list_tree_aux_map_fmap; reflexivity.
Qed.

Lemma bernoulli_tree_bernoulli_tree' (lbl n d : nat) :
  (n <= d)%nat ->
  bernoulli_tree lbl n d = bernoulli_tree' lbl n d.
Proof.
  intro Hle.
  unfold bernoulli_tree, bernoulli_tree'.
  f_equal.
  unfold bernoulli_tree_open, bernoulli_tree_open'.
  unfold seq_tree.
  assert (H: repeat true n ++ repeat false (d - n) =
             map (fun i => i <? n) (seq 0 d)).
  { rewrite seq_app' with (a:=n); auto.
    rewrite map_app.
    f_equal.
    - clear Hle.
      rewrite const_map_repeat with (y:=true).
      + rewrite seq_length; auto.
      + intros x Hin.
        apply in_seq in Hin.
        destruct (Nat.ltb_spec0 x n); auto; lia.
    - rewrite const_map_repeat with (y:=false).
      + rewrite seq_length; auto.
      + intros x Hin.
        apply in_seq in Hin.
        destruct Hin.
        destruct (Nat.ltb_spec0 x n); auto.
        lia. }
  rewrite H; clear H.
  apply list_tree_map_fmap.
Qed.

Lemma denom_le_terminals (lbl n d : nat) :
  (n <= d)%nat ->
  (d <= terminals (bernoulli_tree lbl n d))%nat.
Proof.
  intro Hle.
  rewrite bernoulli_tree_bernoulli_tree'; auto.
  unfold bernoulli_tree'.
  unfold bernoulli_tree_open'.
  simpl.
  rewrite fmap_terminals.
  unfold seq_tree.
  unfold list_tree.
  generalize (seq_length d 0); intro H; rewrite <- H; clear H.
  apply in_tree_length_le_terminals.
  - intros x Hin.
    apply in_list_tree_aux.
    rewrite seq_length; auto.
  - apply seq_NoDup.
Qed.

Lemma bernoulli_tree_spec (lbl n d : nat) :
  (0 < d)%nat -> (n <= d)%nat ->
  infer_f (fun b => if b : bool then 1 else 0) (bernoulli_tree lbl n d) ==
  Z.of_nat n # Pos.of_nat d.
Proof.
  intros Hlt Hle.
  simpl.
  rewrite bernoulli_tree_open_infer_f; auto.
  rewrite bernoulli_tree_open_infer_fail; auto.
  set (n' := Z.of_nat n).
  set (T := terminals (bernoulli_tree_open lbl n d)).
  rewrite Q_lem6.
  assert (H0: (0 < T)%nat).
  { apply terminals_nonzero. }
  assert (H1: (d <= T)%nat).
  { apply denom_le_terminals; auto. }
  rewrite Qdiv_Qmake.
  - rewrite Z_pos_of_nat; auto.
    rewrite <- Nat2Z.inj_sub; try lia.
    assert (H2: (T - (T - d))%nat = d).
    { lia. }
    rewrite H2; clear H2.
    rewrite <- Q_lem1.
    rewrite Z_to_pos_of_nat.
    rewrite Qmake_1; try lia.
    lra.
  - rewrite Z_pos_of_nat; lia.
Qed.

(** A specialized "nondivergent" predicate which is satisfied by trees
  constructed by bernoulli_tree_open. *)
Inductive nd {A : Type} : tree A -> Prop :=
| nd_fix : forall lbl t x,
    no_fix t ->
    only_fail lbl t ->
    in_tree x t ->
    nd (Fix lbl t).

Lemma nd_infer_fail_lt_1 {A : Type} (lbl : nat) (x : A) (t : tree A) :
  wf_tree t ->
  no_fix t ->
  in_tree x t ->
  not_bound_in lbl t ->
  unbiased t ->
  infer_fail lbl t < 1.
Proof.
  induction t; simpl; intros Hwf Hnf Hin Hnotbound Hub.
  - lra.
  - inversion Hin.
  - inversion Hwf; subst.
    inversion Hnf; subst.
    inversion Hnotbound; subst.
    inversion Hub; subst.
    inversion Hin; subst.
    + specialize (IHt1 H3 H1 H5 H7 H10).
      assert (infer_fail lbl t2 <= 1).
      { apply infer_fail_le_1; auto. }
      rewrite H8; lra.
    + specialize (IHt2 H4 H6 H5 H9 H11).
      assert (infer_fail lbl t1 <= 1).
      { apply infer_fail_le_1; auto. }
      rewrite H8; lra.
  - inversion Hnf.
Qed.

(* Lemma no_fix_in_tree_infer_fail_lt_1 {A : Type} (lbl : nat) (x : A) (t : tree A) : *)
(*   wf_tree t -> *)
(*   no_fix t -> *)
(*   in_tree x t -> *)
(*   not_bound_in lbl t -> *)
(*   unbiased t -> *)
(*   infer_fail lbl t < 1. *)
(* Proof. *)
(*   induction t; simpl; intros Hwf Hnf Hin Hnotbound Hub. *)
(*   - lra. *)
(*   - inversion Hin. *)
(*   - inversion Hnf; subst. *)
(*     inversion Hwf; subst. *)
(*     inversion Hnotbound; subst. *)
(*     inversion Hub; subst. *)
(*     inversion Hin; subst. *)
(*     + specialize (IHt1 H5 H1 H2 H7 H10). *)
(*       assert (infer_fail lbl t2 <= 1). *)
(*       { apply infer_fail_le_1; auto. } *)
(*       rewrite H8; lra. *)
(*     + specialize (IHt2 H6 H3 H2 H9 H11). *)
(*       assert (infer_fail lbl t1 <= 1). *)
(*       { apply infer_fail_le_1; auto. } *)
(*       rewrite H8; lra. *)
(*   - inversion Hnf. *)
(* Qed. *)

Lemma infer_f_infer_fail_ge_1 {A : Type} (lbl : nat) (f : A -> Q) (t : tree A) :
  no_fix t ->
  only_fail lbl t ->
  wf_tree t ->
  not_bound_in lbl t ->
  (forall x : A, 1 <= f x) ->
  1 <= infer_f f t + infer_fail lbl t.
Proof.
  induction t; simpl; intros Hnf Hof Hwf Hnotbound Hle.
  - rewrite Qplus_0_r; apply Hle.
  - rewrite Qplus_0_l; inversion Hof; subst; rewrite Nat.eqb_refl; lra.
  - inversion Hnf; subst.
    inversion Hof; subst.
    inversion Hwf; subst.
    inversion Hnotbound; subst.
    specialize (IHt1 H1 H4 H7 H9 Hle).
    specialize (IHt2 H3 H6 H8 H11 Hle).
    nra.
  - inversion Hnf.
Qed.

Lemma nd_infer_f_1_le {A : Type} (f : A -> Q) (t : tree A) :
  nd t ->
  wf_tree t ->
  unbiased t ->
  (forall x, 1 <= f x) ->
  1 <= infer_f f t.
Proof.
  intros Hnd Hwf Hub Hle.
  inversion Hnd; subst. simpl.
  inversion Hwf; subst.
  inversion Hub; subst.
  assert (infer_fail lbl t0 < 1).
  { eapply nd_infer_fail_lt_1; eauto. }
  cut (1 <= infer_f f t0 + infer_fail lbl t0).
  { intro Hle'. apply Qle_shift_div_l; lra. }
  apply infer_f_infer_fail_ge_1; auto.
Qed.

Lemma nd_infer_f_preserves_1 {A : Type} (t : tree A) :
  nd t ->
  unbiased t ->
  wf_tree t ->
  infer_f (const 1) t == 1.
Proof.
  intros Hnd Hub Hwf.
  assert (infer_f (const 1) t <= 1).
  { apply infer_f_bounded; auto.
    intro x; unfold const; lra. }
  assert (1 <= infer_f (const 1) t).
  { apply nd_infer_f_1_le; auto.
    intro x; unfold const; lra. }
  lra.
Qed.

Lemma nd_infer_f_sum_1 {A : Type} (f : A -> bool) (t : tree A) :
  nd t ->
  unbiased t ->
  wf_tree t ->
  infer_f (fun x => if f x then 0 else 1) t +
  infer_f (fun x => if f x then 1 else 0) t == 1.
Proof.
  intros Hnd Hub Hwf.
  rewrite <- infer_f_linear.
  rewrite <- nd_infer_f_preserves_1 with (t0:=t); auto.
  eapply Proper_infer_f; auto.
  intro x; destruct (f x); reflexivity.
Qed.

(* Lemma nd_infer_f_lib_sum_1 {A : Type} (f : A -> bool) (t : tree A) : *)
(*   nd t -> *)
(*   unbiased t -> *)
(*   wf_tree t -> *)
(*   infer_f_lib (fun x => if f x then 0 else 1) t + *)
(*   infer_f_lib (fun x => if f x then 1 else 0) t - *)
(*   infer_f_lib (const 0) t == 1. *)
(* Proof. *)
(*   intros Hnd Hub Hwf. *)
(*   rewrite <- infer_f_lib_linear. *)
(*   rewrite <- nd_infer_f_lib_preserves_1 with (t0:=t); auto. *)
(*   eapply Proper_infer_f; auto. *)
(*   intro x; destruct (f x); reflexivity. *)
(* Qed. *)

Lemma nd_infer_f_complement {A : Type} (f : A -> bool) (t : tree A) :
  nd t ->
  unbiased t ->
  wf_tree t ->
  infer_f (fun x => if f x then 0 else 1) t ==
  1 - infer_f (fun x => if f x then 1 else 0) t.
Proof.
  intros Hnd Hub Hwf.
  generalize (nd_infer_f_sum_1 f t Hnd Hub Hwf); intro Hsum; lra.
Qed.

Lemma no_fix_infer_f_infer_f_lib {A : Type} (f : A -> Q) (t : tree A) :
  no_fix t ->
  infer_f f t == infer_f_lib f t.
Proof.
  induction 1; subst; simpl; try reflexivity.
  rewrite IHno_fix1, IHno_fix2; reflexivity.
Qed.

Lemma nd_infer_f_infer_f_lib {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  unbiased t ->
  nd t ->
  infer_f f t == infer_f_lib f t.
Proof.
  intros Hwf Hub.
  inversion 1; subst; simpl.
  inversion Hwf; inversion Hub; subst.
  assert (infer_fail lbl t0 < 1).
  { eapply nd_infer_fail_lt_1; eauto. }
  destruct (Qeq_bool (infer_fail lbl t0) 1) eqn:Hfail.
  { apply Qeq_bool_eq in Hfail; lra. }
  rewrite no_fix_infer_f_infer_f_lib; auto.
  reflexivity.
Qed.

Lemma nd_infer_f_lib_complement {A : Type} (f : A -> bool) (t : tree A) :
  nd t ->
  unbiased t ->
  wf_tree t ->
  infer_f_lib (fun x => if f x then 0 else 1) t ==
  1 - infer_f_lib (fun x => if f x then 1 else 0) t.
Proof.
  intros Hnd Hub Hwf.
  rewrite <- 2!nd_infer_f_infer_f_lib; auto.
  apply nd_infer_f_complement; auto.
Qed.

(* Lemma nd_infer_f_lib_complement {A : Type} (f : A -> bool) (t : tree A) : *)
(*   nd t -> *)
(*   unbiased t -> *)
(*   wf_tree t -> *)
(*   infer_f_lib (fun x => if f x then 0 else 1) t == *)
(*   1 - infer_f_lib (fun x => if f x then 1 else 0) t + infer_f_lib (const 0) t. *)
(* Proof. *)
(*   intros Hnd Hub Hwf. *)
(*   rewrite <- 3!nd_infer_f_infer_f_lib; auto. *)
(*   generalize (nd_infer_f_sum_1 f t Hnd Hub Hwf); intro Hsum; lra. *)
(* Qed. *)

(* Definition Qnum_nat (p : Q) : nat := Z.to_nat (Qnum p). *)
(* Definition Qden_nat (p : Q) : nat := Pos.to_nat (Qden p). *)

Fixpoint translate_bernoulli_aux {A : Type} (t : tree A) : state nat (tree A) :=
  match t with
  | Leaf x => ret (Leaf x)
  | Fail _ m => ret (Fail _ m)
  | Choice p t1 t2 =>
    t1' <- translate_bernoulli_aux t1 ;;
    t2' <- translate_bernoulli_aux t2 ;;
    lbl <- freshLabel ;;
    ret (bind (bernoulli_tree lbl (Z.to_nat (Qnum p)) (Pos.to_nat (Qden p)))
              (fun b => if b : bool then t1' else t2'))
  | Fix m t1 => t1' <- translate_bernoulli_aux t1 ;; ret (Fix m t1')
  end.

Definition translate_bernoulli {A : Type} (t : tree A) : tree A :=
  evalState (translate_bernoulli_aux t) (list_max (all_labels t)).

Lemma bernoulli_tree_spec' (lbl : nat) (p : Q) :
  0 <= p -> p <= 1 ->
  infer_f (fun b => if b : bool then 1 else 0)
          (bernoulli_tree lbl (Z.to_nat (Qnum p)) (Pos.to_nat (Qden p))) ==
  p.
Proof.
  intros H0 H1.
  rewrite bernoulli_tree_spec.
  - rewrite Z2Nat.id.
    + rewrite Pos2Nat.id; destruct p; reflexivity.
    + destruct p. simpl.
      rewrite Zle_Qle.
      unfold inject_Z.
      unfold Qle in *; simpl in *;lia.
  - lia.
  - destruct p; simpl; unfold Qle in *; simpl in *; lia.
Qed.

Lemma unfold_translate_bernoulli_aux {A : Type}
      f q (t1 t2 t1' t2' : tree A) n m o :
  runState (translate_bernoulli_aux t1) n = (t1', m) ->
  runState (translate_bernoulli_aux t2) m = (t2', o) ->
  infer_f f (evalState (translate_bernoulli_aux (Choice q t1 t2)) n) ==
  infer_f f (tree_bind (bernoulli_tree
                          (S o)
                          (Z.to_nat (Qnum q))
                          (Pos.to_nat (Qden q)))
                       (fun b : bool => if b then t1' else t2')).
Proof.
  simpl. unfold evalState. simpl.
  intros Ht1 Ht2.
  destruct (runState (translate_bernoulli_aux t1) n) eqn:Ht1'.
  inversion Ht1; subst.
  destruct (runState (translate_bernoulli_aux t2) m) eqn:Ht2'.
  inversion Ht2; subst.
  reflexivity.
Qed.

Lemma unfold_translate_bernoulli_aux_lib {A : Type}
      f q (t1 t2 t1' t2' : tree A) n m o :
  runState (translate_bernoulli_aux t1) n = (t1', m) ->
  runState (translate_bernoulli_aux t2) m = (t2', o) ->
  infer_f_lib f (evalState (translate_bernoulli_aux (Choice q t1 t2)) n) ==
  infer_f_lib f (tree_bind (bernoulli_tree
                              (S o)
                              (Z.to_nat (Qnum q))
                              (Pos.to_nat (Qden q)))
                           (fun b : bool => if b then t1' else t2')).
Proof.
  simpl. unfold evalState. simpl.
  intros Ht1 Ht2.
  destruct (runState (translate_bernoulli_aux t1) n) eqn:Ht1'.
  inversion Ht1; subst.
  destruct (runState (translate_bernoulli_aux t2) m) eqn:Ht2'.
  inversion Ht2; subst.
  reflexivity.
Qed.

Lemma no_fix_new_tree {A : Type} (lbl n : nat) :
  @no_fix A (new_tree lbl n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma no_fix_add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) :
  no_fix t ->
  no_fix (add_to_tree x t).
Proof.
  induction t; simpl; intro Hnf; auto; inversion Hnf; subst.
  - constructor.
  - destruct (tree_eqb t1 (add_to_tree x t1)); constructor; auto.
Qed.

Lemma no_fix_list_tree_aux {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) :
  no_fix t ->
  no_fix (list_tree_aux lbl l t).
Proof.
  revert t.
  induction l; simpl; intros t Hnf; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl. constructor; auto.
    apply no_fix_add_to_tree, no_fix_new_tree.
  - apply IHl, no_fix_add_to_tree; auto.
Qed.

Lemma only_fail_new_tree {A : Type} (lbl n : nat) :
  @only_fail A lbl (new_tree lbl n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma only_fail_add_to_tree {A : Type} `{EqType A}
      (lbl : nat) (x : A) (t : tree A) :
  only_fail lbl t ->
  only_fail lbl (add_to_tree x t).
Proof.
  induction t; simpl; intro Hof; auto; inversion Hof; subst.
  - constructor.
  - destruct (tree_eqb t1 (add_to_tree x t1)); constructor; auto.
  - constructor; auto.
Qed.

Lemma only_fail_list_tree_aux {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) :
  only_fail lbl t ->
  only_fail lbl (list_tree_aux lbl l t).
Proof.
  revert t; induction l; intros t Hof; simpl; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl; constructor; auto.
    apply only_fail_add_to_tree, only_fail_new_tree.
  - apply IHl, only_fail_add_to_tree; auto.
Qed.

Lemma not_tree_eq_add_to_tree_has_fail {A : Type} `{EqType A}
      (x : A) (t : tree A) :
  ~ tree_eq t (add_to_tree x t) ->
  has_fail t.
Proof.
  induction t; simpl; intros Hneq.
  - exfalso; apply Hneq; reflexivity.
  - constructor.
  - destruct (tree_eqb t1 (add_to_tree x t1)).
    + assert (H0: ~ tree_eq t2 (add_to_tree x t2)).
      { intro HC; apply Hneq; constructor; auto; reflexivity. }
      apply IHt2 in H0; solve [constructor; auto].
    + assert (H0: ~ tree_eq t1 (add_to_tree x t1)).
      { intro HC; apply Hneq; constructor; auto; reflexivity. }
      apply IHt1 in H0; solve [constructor; auto].
  - constructor; apply IHt; intro HC; apply Hneq; constructor; auto.
Qed.

Lemma has_fail_in_tree_add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) :
  has_fail t ->
  in_tree x (add_to_tree x t).
Proof.
  induction t; simpl; intros Hhf; inversion Hhf; subst.
  - constructor.
  - destruct (tree_eqb_spec t1 (add_to_tree x t1)).
    + apply IHt1 in H1; constructor; eapply in_tree_tree_eq; eauto; intuition.
    + constructor; eauto.
  - destruct (tree_eqb_spec t1 (add_to_tree x t1)).
    + solve [constructor; eauto].
    + constructor; apply IHt1.
      eapply not_tree_eq_add_to_tree_has_fail; eauto.
  - constructor; eauto.
Qed.

Lemma free_in_new_tree {A : Type} `{EqType A} (lbl n : nat) :
  @free_in A lbl (new_tree lbl n).
Proof. induction n; constructor; auto. Qed.

Lemma has_fail_new_tree {A : Type} `{EqType A} (lbl n : nat) :
  @has_fail A (new_tree lbl n).
Proof. induction n; constructor; auto. Qed.

Lemma nd_bernoulli_tree lbl n d :
  (0 < d)%nat ->
  nd (bernoulli_tree lbl n d).
Proof.
  intro Hlt; destruct n.
  + apply nd_fix with (x:=false).
    * apply no_fix_list_tree_aux; constructor.
    * apply only_fail_list_tree_aux; constructor.
    * apply in_list_tree_aux; simpl; destruct d; try lia; left; auto.
  + apply nd_fix with (x:=true).
    * apply no_fix_list_tree_aux; constructor.
    * apply only_fail_list_tree_aux; constructor.
    * apply in_list_tree_aux; left; auto.
Qed.

Lemma wf_new_tree {A : Type} (lbl n : nat) :
  @wf_tree A (new_tree lbl n).
Proof. induction n; simpl; constructor; auto; lra. Qed.

Lemma not_bound_in_add_to_tree {A : Type} `{EqType A}
      (x : A) (t : tree A) (lbl : nat) :
  not_bound_in lbl t ->
  not_bound_in lbl (add_to_tree x t).
Proof.
  induction t; simpl; intro Hnb; inversion Hnb; subst;
    try solve [constructor; auto];
    destruct (tree_eqb t1 (add_to_tree x t1)); constructor; auto.
Qed.

Lemma wf_add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) :
  wf_tree t ->
  wf_tree (add_to_tree x t).
Proof.
  induction t; simpl; intro Hwf; auto.
  - constructor.
  - inversion Hwf; subst.
    destruct (tree_eqb t1 (add_to_tree x t1)); constructor; auto.
  - inversion Hwf; subst; constructor; auto.
    apply not_bound_in_add_to_tree; auto.
Qed.

Lemma wf_list_tree_aux {A : Type} `{EqType A}
      (lbl : nat) (l : list A) (t : tree A) :
  wf_tree t ->
  wf_tree (list_tree_aux lbl l t).
Proof.
  revert t; induction l; intros t Hof; simpl; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl; constructor; auto.
    + lra.
    + apply wf_add_to_tree, wf_new_tree.
  - apply IHl, wf_add_to_tree; auto.
Qed.

Lemma not_bound_in_new_tree {A : Type} (lbl m n : nat) :
  @not_bound_in A lbl (new_tree m n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma not_bound_in_list_tree_aux {A : Type} `{EqType A}
      (lbl m : nat) (l : list A) (t : tree A) :
  not_bound_in lbl t ->
  not_bound_in lbl (list_tree_aux m l t).
Proof.
  revert t; induction l; simpl; intros t Hnotbound; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl; constructor; auto.
    apply not_bound_in_add_to_tree, not_bound_in_new_tree.
  - apply IHl, not_bound_in_add_to_tree; auto.
Qed.

Lemma bound_in_bernoulli_tree (lbl m n d : nat) :
  bound_in lbl (bernoulli_tree m n d) ->
  (lbl = m)%nat.
Proof.
  unfold bernoulli_tree.
  intro Hbound.
  inversion Hbound; subst.
  - reflexivity.
  - assert (H: not_bound_in lbl (bernoulli_tree_open m n d)).
    { apply not_bound_in_list_tree_aux; constructor. }
    apply bound_in_not_bound_in in H; congruence.
Qed.

Lemma unfold_translate_bernoulli_aux' {A : Type}
      q (t1 t2 t1' t2' : tree A) lbl n m o :
  runState (translate_bernoulli_aux t1) n = (t1', m) ->
  runState (translate_bernoulli_aux t2) m = (t2', o) ->
  infer_fail lbl (evalState (translate_bernoulli_aux (Choice q t1 t2)) n) ==
  infer_fail lbl (tree_bind (bernoulli_tree
                               (S o)
                               (Z.to_nat (Qnum q))
                               (Pos.to_nat (Qden q)))
                            (fun b : bool => if b then t1' else t2')).
Proof.
  simpl. unfold evalState. simpl.
  intros Ht1 Ht2.
  destruct (runState (translate_bernoulli_aux t1) n) eqn:Ht1'.
  inversion Ht1; subst.
  destruct (runState (translate_bernoulli_aux t2) m) eqn:Ht2'.
  inversion Ht2; subst.
  reflexivity.
Qed.

Lemma not_in_new_tree {A : Type} (lbl m n : nat) :
  lbl <> m ->
  @not_in A lbl (new_tree m n).
Proof. induction n; constructor; auto. Qed.

Lemma not_in_add_to_tree {A : Type} `{EqType A} (lbl : nat) (x : A) (t : tree A) :
  not_in lbl t ->
  not_in lbl (add_to_tree x t).
Proof.
  induction t; simpl; intro Hnotin; auto; inversion Hnotin; subst.
  - constructor.
  - destruct (tree_eqb t1 (add_to_tree x t1)); constructor; auto.
  - constructor; auto.
Qed.

Lemma not_in_list_tree_aux {A : Type} `{EqType A}
      (lbl m : nat) (l : list A) (t : tree A) :
  lbl <> m ->
  not_in lbl t ->
  not_in lbl (list_tree_aux m l t).
Proof.
  revert t.
  induction l; simpl; intros t Hneq Hnotin; auto.
  destruct (tree_eqb t (add_to_tree a t)).
  - apply IHl; auto.
    constructor; auto.
    apply not_in_add_to_tree, not_in_new_tree; auto.
  - apply IHl, not_in_add_to_tree; auto.
Qed.

Lemma translate_bernoulli_aux_le {A : Type} (t t' : tree A) (n m : nat) :
  runState (translate_bernoulli_aux t) n = (t', m) ->
  (n <= m)%nat.
Proof.
  revert n m t'.
  induction t; simpl; intros n' m t' Heq.
  - inversion Heq; subst; lia.
  - inversion Heq; subst; lia.
  - destruct (runState (translate_bernoulli_aux t1) n') eqn:Ht1.
    destruct (runState (translate_bernoulli_aux t2) n) eqn:Ht2.
    inversion Heq; subst.
    apply IHt1 in Ht1.
    apply IHt2 in Ht2.
    lia.
  - destruct (runState (translate_bernoulli_aux t) n') eqn:Ht.
    inversion Heq; subst.
    apply IHt in Ht; lia.
Qed.

Lemma free_in_add_to_tree {A : Type} `{EqType A} (x : A) (t : tree A) (lbl : nat) :
  free_in lbl (add_to_tree x t) ->
  free_in lbl t.
Proof.
  induction t; simpl; intro Hfree; auto.
  - inversion Hfree.
  - destruct (tree_eqb t1 (add_to_tree x t1));
      inversion Hfree; subst; solve [constructor; auto].
  - inversion Hfree; subst; constructor; auto.
Qed.

Lemma free_in_new_tree' {A : Type} (lbl m n : nat) :
  @free_in A m (new_tree lbl n) ->
  m = lbl.
Proof.
  induction n; simpl; intro Hfree; inversion Hfree; subst; auto.
Qed.

Lemma free_in_list_tree_aux {A : Type} `{EqType A}
      (l : list A) (t : tree A) (m lbl : nat) :
  free_in m (list_tree_aux lbl l t) ->
  free_in m t \/ m = lbl.
Proof.
  revert t.
  induction l; simpl; intros t Hfree.
  - left; auto.
  - destruct (tree_eqb t (add_to_tree a t)).
    + apply IHl in Hfree.
      destruct Hfree; auto.
      inversion H0; subst; auto.
      apply free_in_add_to_tree in H3.
      apply free_in_new_tree' in H3; auto.
    + apply IHl in Hfree.
      destruct Hfree; auto.
      apply free_in_add_to_tree in H0; auto.
Qed.

Lemma translate_bernoulli_aux_not_in {A : Type} (t t' : tree A) (lbl n m : nat) :
  (forall o, (n < o)%nat -> not_in o t) ->
  runState (translate_bernoulli_aux t) n = (t', m) ->
  (m < lbl)%nat ->
  not_in lbl t'.
Proof.
  revert t' lbl n m.
  induction t; simpl; intros t' lbl n' m Hnotin Heq Hlt.
  - inversion Heq; subst; constructor.
  - inversion Heq; subst.
    apply Hnotin; auto.
  - destruct (runState (translate_bernoulli_aux t1) n') eqn:Ht1.
    destruct (runState (translate_bernoulli_aux t2) n) eqn:Ht2.
    inversion Heq; subst; clear Heq.
    (** Instantiate IH for t1. *)
    assert (Hnotin1: forall o, (n' < o)%nat -> not_in o t1).
    { intros o Hlt'.
      specialize (Hnotin o Hlt'). inversion Hnotin; auto. }
    assert (Hlt1: (n < lbl)%nat).
    { apply translate_bernoulli_aux_le in Ht2; lia. }
    specialize (IHt1 t lbl n' n Hnotin1 Ht1 Hlt1).
    (** Instantiate IH for t2. *)
    assert (Hnotin2: forall o, (n < o)%nat -> not_in o t2).
    { intros o Hlt'.
      assert (H: (n' < o)%nat).
      { apply translate_bernoulli_aux_le in Ht1; lia. }
      specialize (Hnotin o H). inversion Hnotin; auto. }
    assert (Hlt2: (n0 < lbl)%nat).
    { lia. }
    specialize (IHt2 t0 lbl n n0 Hnotin2 Ht2 Hlt2).
    (** lbl is not in any of the parts, so it's not in the result. *)
    apply not_in_tree_bind.
    + unfold bernoulli_tree.
      constructor. lia.
      apply label_in_not_in; intro HC.
      apply label_in_bound_or_free in HC. destruct HC.
      * revert H.
        apply bound_in_not_bound_in.
        apply not_bound_in_list_tree_aux. constructor.
      * apply free_in_list_tree_aux in H.
        destruct H; subst.
        -- inversion H; subst; lia.
        -- lia.
    + intros []; auto.
  - destruct (runState (translate_bernoulli_aux t) n') eqn: Ht.
    inversion Heq; subst; clear Heq.
    assert (lbl <> n).
    { intro HC. subst.
      assert (H: (n' < n)%nat).
      { apply translate_bernoulli_aux_le in Ht; lia. }
      specialize (Hnotin n H); inversion Hnotin; subst; congruence. }
    constructor; auto.    
    eapply IHt; eauto.
    intros o Hlt'.
    specialize (Hnotin o Hlt'). inversion Hnotin; auto.
Qed.

Lemma translate_bernoulli_aux_infer_fail {A : Type} (t : tree A) (lbl n : nat) :
  wf_tree t ->
  (lbl <= n)%nat ->
  (forall m, (n < m)%nat -> not_in m t) ->
  infer_fail lbl t == infer_fail lbl (evalState (translate_bernoulli_aux t) n).
Proof.
  revert lbl n.
  induction t; intros lbl n' Hwf Hle Hnotin; try reflexivity.
  - unfold evalState in IHt1, IHt2.
    inversion Hwf; subst.
    assert (Hnotin1: forall m, (n' < m)%nat -> not_in m t1).
    { intros m Hlt; specialize (Hnotin m Hlt); inversion Hnotin; auto. }
    specialize (IHt1 lbl n' H3 Hle Hnotin1).
    destruct (runState (translate_bernoulli_aux t1) n') eqn:Ht1.
    assert (Hnotin2: forall m, (n < m)%nat -> not_in m t2).
    { intros m Hlt.
      apply translate_bernoulli_aux_le in Ht1.
      assert (Hlt': (n' < m)%nat).
      { lia. }
      specialize (Hnotin m Hlt'); inversion Hnotin; auto. }
    assert (Hle': (lbl <= n)%nat).
    { apply translate_bernoulli_aux_le in Ht1; lia. }
    specialize (IHt2 lbl n H4 Hle' Hnotin2).
    destruct (runState (translate_bernoulli_aux t2) n) eqn:Ht2.
    rewrite unfold_translate_bernoulli_aux'; eauto.
    rewrite infer_fail_bind_choice.
    + rewrite nd_infer_f_complement.
      * rewrite bernoulli_tree_spec'; simpl in *; nra.
      * apply nd_bernoulli_tree; lia.
      * constructor; apply unbiased_list_tree_aux; constructor.
      * constructor.
        -- apply wf_list_tree_aux; constructor.
        -- apply not_bound_in_list_tree_aux; constructor.
    + intros m x Hbound.
      inversion Hwf; subst.
      apply bound_in_bernoulli_tree in Hbound; subst.
      specialize (Hnotin (S n') (Nat.lt_succ_diag_r n')).
      inversion Hnotin; subst; destruct x; auto.
      * eapply translate_bernoulli_aux_not_in.
        2: { apply Ht1. }
        -- intros o Hlt; apply Hnotin1.
           apply translate_bernoulli_aux_le in Ht1; lia.
        -- apply translate_bernoulli_aux_le in Ht2; lia.
      * eapply translate_bernoulli_aux_not_in.
        2: { apply Ht2; lia. }
        -- intros o Hlt; apply Hnotin2.
           apply translate_bernoulli_aux_le in Ht2; lia.
        -- lia.
    + assert (lbl <> S n0).
      { apply translate_bernoulli_aux_le in Ht2; lia. }
      constructor; auto; apply not_in_list_tree_aux; try constructor; auto.
  - inversion Hwf; subst.
    unfold evalState in *. simpl in *.
    pose proof (IHt n n') as IHt'.
    specialize (IHt lbl n').
    destruct (runState (translate_bernoulli_aux t) n') eqn:Ht.
    simpl in *.
    assert (forall m, (n' < m)%nat -> not_in m t).
    { intros m Hlt; specialize (Hnotin m Hlt); inversion Hnotin; auto. }
    rewrite IHt; auto.
    rewrite IHt'; auto.
    reflexivity.
    destruct (le_lt_dec n n'); auto.
    apply Hnotin in l. inversion l; subst; congruence.
Qed.

Lemma translate_bernoulli_aux_infer_f {A : Type}
      (f : A -> Q) (t : tree A) (n : nat) :
  wf_tree t ->
  (forall m, (n < m)%nat -> not_in m t) ->
  infer_f f t == infer_f f (evalState (translate_bernoulli_aux t) n).
Proof.
  revert n.
  induction t; intros n' Hwf Hnotin; try reflexivity.
  - unfold evalState in IHt1, IHt2.
    inversion Hwf; subst.
    assert (Hnotin1: forall m, (n' < m)%nat -> not_in m t1).
    { intros m Hlt; specialize (Hnotin m Hlt); inversion Hnotin; auto. }
    specialize (IHt1 n' H3 Hnotin1).
    destruct (runState (translate_bernoulli_aux t1) n') eqn:Ht1.
    assert (Hnotin2: forall m, (n < m)%nat -> not_in m t2).
    { intros m Hlt.
      apply translate_bernoulli_aux_le in Ht1.
      assert (Hlt': (n' < m)%nat).
      { lia. }
      specialize (Hnotin m Hlt'); inversion Hnotin; auto. }
    specialize (IHt2 n H4 Hnotin2).
    destruct (runState (translate_bernoulli_aux t2) n) eqn:Ht2.
    rewrite unfold_translate_bernoulli_aux; eauto.
    rewrite infer_f_bind_choice.
    + rewrite nd_infer_f_complement.
      * rewrite bernoulli_tree_spec'; simpl in *; nra.
      * apply nd_bernoulli_tree; lia.
      * constructor; apply unbiased_list_tree_aux; constructor.
      * constructor.
        -- apply wf_list_tree_aux; constructor.
        -- apply not_bound_in_list_tree_aux; constructor.
    + intros m x Hbound.
      inversion Hwf; subst.
      apply bound_in_bernoulli_tree in Hbound; subst.
      specialize (Hnotin (S n') (Nat.lt_succ_diag_r n')).
      inversion Hnotin; subst; destruct x; auto.
      * eapply translate_bernoulli_aux_not_in.
        2: { apply Ht1. }
        -- intros o Hlt; apply Hnotin1.
           apply translate_bernoulli_aux_le in Ht1; lia.
        -- apply translate_bernoulli_aux_le in Ht2; lia.
      * eapply translate_bernoulli_aux_not_in.
        2: { apply Ht2. }
        -- intros o Hlt; apply Hnotin2.
           apply translate_bernoulli_aux_le in Ht2; lia.
        -- lia.
  - inversion Hwf; subst.
    assert (Hle: (n <= n')%nat).
    { destruct (le_lt_dec n n'); auto.
      apply Hnotin in l. inversion l; subst; congruence. }
    generalize (translate_bernoulli_aux_infer_fail t n n' H1 Hle).
    intro Hfail.
    unfold evalState in *. simpl in *.
    specialize (IHt n').
    destruct (runState (translate_bernoulli_aux t) n') eqn:Ht.
    simpl in *.
    rewrite IHt; auto.
    + rewrite Hfail.
      * reflexivity.
      * intros m Hlt.
        specialize (Hnotin m Hlt); inversion Hnotin; auto.
    + intros m Hlt.
      specialize (Hnotin m Hlt).
      inversion Hnotin; subst; auto.
Qed.

(* Lemma infer_f_lib_bind_choice' {A : Type} (f : A -> Q) (t : tree bool) (t1 t2 : tree A) : *)
(*   nd t -> *)
(*   (forall (n : nat) (x : bool), bound_in n t -> not_in n (if x then t1 else t2)) -> *)
(*   infer_f_lib f (bind t (fun b => if b : bool then t1 else t2)) == *)
(*   infer_f_lib (fun b => if b : bool then 1 else 0) t * infer_f_lib f t1 + *)
(*   infer_f_lib (fun b => if b : bool then 0 else 1) t * infer_f_lib f t2. *)
(* Proof. *)
(*   intros Hnd Hnotin. *)
(*   rewrite <- infer_f_lib_bind; auto. *)
(*   unfold compose; induction t; simpl; inverson *)
(*   - destruct a; lra. *)
(*   - lra. *)
(*   - rewrite IHt1, IHt2; try lra; *)
(*       intros; apply Hnotin; solve [constructor; auto]. *)
(*   - rewrite IHt. *)
(*     + destruct (Qeq_dec (infer_fail n t) 1). *)
(*       * rewrite q, Qminus_cancel, 3!Qdiv_0_den; lra. *)
(*       * field; lra. *)
(*     + intros; apply Hnotin. *)
(*       destruct (Nat.eqb_spec n0 n); subst; constructor; auto. *)
(* Qed. *)

Lemma wf_bernoulli_tree lbl n d :
  wf_tree (bernoulli_tree lbl n d).
Proof.
  constructor.
  - apply wf_list_tree_aux; constructor.
  - apply not_bound_in_list_tree_aux; constructor.
Qed.

Lemma unbiased_bernoulli_tree lbl n d :
  unbiased (bernoulli_tree lbl n d).
Proof. constructor; apply unbiased_bernoulli_tree_open. Qed.

Lemma bernoulli_tree_spec_lib (lbl : nat) (p : Q) :
  0 <= p -> p <= 1 ->
  infer_f_lib (fun b => if b : bool then 1 else 0)
              (bernoulli_tree lbl (Z.to_nat (Qnum p)) (Pos.to_nat (Qden p))) ==
  p.
Proof.
  intros H0 H1.
  rewrite <- nd_infer_f_infer_f_lib.
  { rewrite bernoulli_tree_spec'; auto; reflexivity. }
  - eapply wf_bernoulli_tree.
  - apply unbiased_bernoulli_tree.
  - apply nd_bernoulli_tree; lia.
Qed.

Lemma infer_fail_bernoulli_tree_open (lbl n d : nat) :
  (0 < d)%nat ->
  (n <= d)%nat ->
  infer_fail lbl (bernoulli_tree_open lbl n d) < 1.
Proof.
  intros H0 H1.
  rewrite bernoulli_tree_open_infer_fail; auto.
  generalize (terminals_nonzero (bernoulli_tree_open lbl n d)).
  intro H.
  apply Qmake_lt_1; lia.
Qed.

Lemma translate_bernoulli_aux_infer_f_lib {A : Type}
      (f : A -> Q) (t : tree A) (n : nat) :
  wf_tree t ->
  (forall m, (n < m)%nat -> not_in m t) ->
  infer_f_lib f t == infer_f_lib f (evalState (translate_bernoulli_aux t) n).
Proof.
  revert n.
  induction t; intros n' Hwf Hnotin; try reflexivity.
  - unfold evalState in IHt1, IHt2.
    inversion Hwf; subst.
    assert (Hnotin1: forall m, (n' < m)%nat -> not_in m t1).
    { intros m Hlt; specialize (Hnotin m Hlt); inversion Hnotin; auto. }
    specialize (IHt1 n' H3 Hnotin1).
    destruct (runState (translate_bernoulli_aux t1) n') eqn:Ht1.
    assert (Hnotin2: forall m, (n < m)%nat -> not_in m t2).
    { intros m Hlt.
      apply translate_bernoulli_aux_le in Ht1.
      assert (Hlt': (n' < m)%nat).
      { lia. }
      specialize (Hnotin m Hlt'); inversion Hnotin; auto. }
    specialize (IHt2 n H4 Hnotin2).
    destruct (runState (translate_bernoulli_aux t2) n) eqn:Ht2.
    rewrite unfold_translate_bernoulli_aux_lib; eauto.
    rewrite infer_f_lib_bind_choice.
    + rewrite nd_infer_f_lib_complement.
      * rewrite bernoulli_tree_spec_lib; simpl in *; try lra.
        assert (infer_fail (S n0) (bernoulli_tree_open (S n0) (Z.to_nat (Qnum q))
                                                       (Pos.to_nat (Qden q))) < 1).
        { eapply infer_fail_bernoulli_tree_open; try lia.
          apply Q_num_le_den; lra. }
        destruct (Qeq_bool (infer_fail (S n0) (bernoulli_tree_open (S n0) (Z.to_nat (Qnum q))
                                                                   (Pos.to_nat (Qden q)))) 1)
        eqn:Hfail.
        { apply Qeq_bool_eq in Hfail; lra. }
        rewrite <- (no_fix_infer_f_infer_f_lib (const 0)).
        -- rewrite infer_f_const_0, Qdiv_0_num; nra.
        -- apply no_fix_list_tree_aux; constructor.
      * apply nd_bernoulli_tree; lia.
      * constructor; apply unbiased_list_tree_aux; constructor.
      * constructor.
        -- apply wf_list_tree_aux; constructor.
        -- apply not_bound_in_list_tree_aux; constructor.
    + intros m x Hbound.
      inversion Hwf; subst.
      apply bound_in_bernoulli_tree in Hbound; subst.
      specialize (Hnotin (S n') (Nat.lt_succ_diag_r n')).
      inversion Hnotin; subst; destruct x; auto.
      * eapply translate_bernoulli_aux_not_in.
        2: { apply Ht1. }
        -- intros o Hlt; apply Hnotin1.
           apply translate_bernoulli_aux_le in Ht1; lia.
        -- apply translate_bernoulli_aux_le in Ht2; lia.
      * eapply translate_bernoulli_aux_not_in.
        2: { apply Ht2. }
        -- intros o Hlt; apply Hnotin2.
           apply translate_bernoulli_aux_le in Ht2; lia.
        -- lia.
  - inversion Hwf; subst.
    assert (Hle: (n <= n')%nat).
    { destruct (le_lt_dec n n'); auto.
      apply Hnotin in l. inversion l; subst; congruence. }
    generalize (translate_bernoulli_aux_infer_fail t n n' H1 Hle).
    intro Hfail.
    unfold evalState in *. simpl in *.
    specialize (IHt n').
    destruct (runState (translate_bernoulli_aux t) n') eqn:Ht.
    simpl in *.
    assert (H: forall m : nat, (n' < m)%nat -> not_in m t).
    { intros m Hlt.
      specialize (Hnotin m Hlt); inversion Hnotin; auto. }
    rewrite Hfail; auto.
    + destruct (Qeq_bool (infer_fail n t0) 1) eqn:Ht0; try reflexivity.
      rewrite Hfail; auto.
      rewrite IHt; try reflexivity; auto.
Qed.

Lemma unbiased_translate_bernoulli_aux {A : Type} (t : tree A) (n : nat) :
  unbiased (evalState (translate_bernoulli_aux t) n).
Proof.
  unfold evalState. simpl.
  revert n.
  induction t; simpl; intro m.
  - constructor.
  - constructor.
  - specialize (IHt1 m).
    destruct (runState (translate_bernoulli_aux t1) m) eqn:Ht1.
    specialize (IHt2 n).
    destruct (runState (translate_bernoulli_aux t2) n) eqn:Ht2.
    simpl in *.
    apply unbiased_tree_bind.
    + constructor; apply unbiased_bernoulli_tree_open.
    + intros []; auto.
  - specialize (IHt m).
    destruct (runState (translate_bernoulli_aux t) m) eqn:Ht.
    constructor; auto.
Qed.

Lemma translate_bernoulli_infer_f {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  infer_f f t == infer_f f (translate_bernoulli t).
Proof.
  intro Hwf.
  apply translate_bernoulli_aux_infer_f; auto.
  apply list_max_lt_not_in.
Qed.

Lemma translate_bernoulli_infer_f_lib {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  infer_f_lib f t == infer_f_lib f (translate_bernoulli t).
Proof.
  intro Hwf.
  apply translate_bernoulli_aux_infer_f_lib; auto.
  apply list_max_lt_not_in.
Qed.

(** Soundness result: translation preserves inference semantics. *)
Theorem translate_bernoulli_infer {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  infer f t == infer f (translate_bernoulli t).
Proof.
  intro Hwf.
  unfold infer.
  rewrite translate_bernoulli_infer_f, translate_bernoulli_infer_f_lib; auto.
  reflexivity.
Qed.

(** Correctness result: translation produces unbiased trees. *)
Theorem unbiased_translate_bernoulli {A : Type} (t : tree A) :
  unbiased (translate_bernoulli t).
Proof.
  unfold translate_bernoulli.
  simpl. unfold evalState.
  apply unbiased_translate_bernoulli_aux.
Qed.
