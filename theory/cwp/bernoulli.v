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
Local Open Scope program_scope.
Import ListNotations.

Require Import compile.
Require Import cpGCL.
Require Import infer.
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.

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

Fixpoint heightb {A : Type} (t : tree A) : nat :=
  match t with
  | Choice _ t1 t2 => 1 + max (heightb t1) (heightb t2)
  | Fix _ t => 1 + heightb t
  | _ => 0
  end.

Inductive height {A : Type} : tree A -> nat -> Prop :=
| height_leaf : forall x, height (Leaf x) 0
| height_fail : forall n, height (Fail _ n) 0
| height_choice : forall p t1 t2 n m,
    height t1 n ->
    height t2 m ->
    height (Choice p t1 t2) (S (max n m))
| height_fix : forall l n t,
    height t n ->
    height (Fix l t) (S n).

Lemma heightb_spec {A : Type} (t : tree A) :
  height t (heightb t).
Proof.
  induction t; simpl; constructor; auto.
Qed.

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

Inductive congruent {A B : Type} : tree A -> tree B -> Prop :=
| congruent_leaf_leaf : forall x y, congruent (Leaf x) (Leaf y)
| congruent_leaf_fail : forall x n, congruent (Leaf x) (Fail _ n)
| congruent_fail_leaf : forall y n, congruent (Fail _ n) (Leaf y)
| congruent_fail_fail : forall n m, congruent (Fail _ n) (Fail _ m)
| congruent_choice : forall p q t1 t1' t2 t2',
    congruent t1 t1' -> congruent t2 t2' ->
    congruent (Choice p t1 t2) (Choice q t1' t2')
| congruence_fix : forall n m t1 t2,
    congruent t1 t2 ->
    congruent (Fix n t1) (Fix m t2).

Instance Reflexive_congruent {A : Type} : Reflexive (@congruent A A).
Proof. intro t. induction t; constructor; auto. Qed.

Lemma congruent_symm {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent t1 t2 -> congruent t2 t1.
Proof. intro H; induction H; constructor; auto. Qed.

Lemma congruent_trans {A B C : Type}
      (t1 : tree A) (t2 : tree B) (t3 : tree C) :
  congruent t1 t2 -> congruent t2 t3 -> congruent t1 t3.
Proof.
  revert t3 t1; induction t2; intros t1 t3 H0 H1;
    inversion H0; inversion H1; subst; constructor; auto.
Qed.

(** Stronger notion of congruence (leaves and fails not congruent) *)
Inductive congruent' {A B : Type} : tree A -> tree B -> Prop :=
| congruent'_leaf_leaf : forall x y, congruent' (Leaf x) (Leaf y)
| congruent'_fail_fail : forall n m, congruent' (Fail _ n) (Fail _ m)
| congruent'_choice : forall p q t1 t1' t2 t2',
    congruent' t1 t1' -> congruent' t2 t2' ->
    congruent' (Choice p t1 t2) (Choice q t1' t2')
| congruence'_fix : forall n m t1 t2,
    congruent' t1 t2 ->
    congruent' (Fix n t1) (Fix m t2).

Instance Reflexive_congruent' {A : Type} : Reflexive (@congruent' A A).
Proof. intro t. induction t; constructor; auto. Qed.

Lemma congruent'_symm {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent' t1 t2 -> congruent' t2 t1.
Proof. intro H; induction H; constructor; auto. Qed.

Lemma congruent'_trans {A B C : Type}
      (t1 : tree A) (t2 : tree B) (t3 : tree C) :
  congruent' t1 t2 -> congruent' t2 t3 -> congruent' t1 t3.
Proof.
  revert t3 t1; induction t2; intros t1 t3 H0 H1;
    inversion H0; inversion H1; subst; constructor; auto.
Qed.

Inductive perfect {A : Type} : tree A -> Prop :=
| perfect_leaf : forall x, perfect (Leaf x)
| perfect_fail : forall n, perfect (Fail _ n)
| perfect_choice : forall p t1 t2,
    congruent t1 t2 ->
    perfect t1 -> perfect t2 ->
    perfect (Choice p t1 t2).  

Lemma perfect_not_fix {A : Type} (t t1: tree A) (n : nat) :
  perfect t ->
  t <> Fix n t1.
Proof. induction 1; congruence. Qed.

(** infer_f and infer_f_lib coincide on "perfect" trees. Really only
  nondivergence is necessary, and "perfect" is stronger. *)
Lemma perfect_infer_f_infer_f_lib {A : Type} (f : A -> Q) (t : tree A) :
  perfect t ->
  infer_f f t == infer_f_lib f t.
Proof.
  induction 1; simpl; try lra.
  rewrite IHperfect1, IHperfect2; lra.
Qed.

Lemma congruent_perfect {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent t1 t2 -> perfect t1 -> perfect t2.
Proof.
  intro H. induction H; intros; try solve [constructor].
  - inversion H1; subst. constructor; auto.
    apply congruent_symm in H.
    eapply congruent_trans; eauto.
    eapply congruent_trans; eauto.
  - inversion H0.
Qed.

Fixpoint countb {A : Type} (f : A -> bool) (t : tree A) : nat :=
  match t with
  | Leaf x => if f x then 1 else 0
  | Fail _ _ => 0
  | Choice _ t1 t2 => countb f t1 + countb f t2
  | Fix _ t1 => countb f t1
  end.

Inductive count {A : Type} (f : A -> bool) : tree A -> nat -> Prop :=
| count_leaf0 : forall x, f x = false -> count f (Leaf x) 0
| count_leaf1 : forall x, f x = true -> count f (Leaf x) 1
| count_fail : forall n, count f (Fail _ n) 0
| count_choice : forall p t1 t2 n m,
    count f t1 n -> count f t2 m ->
    count f (Choice p t1 t2) (n + m)
| count_fix : forall l t1 n,
    count f t1 n ->
    count f (Fix l t1) n.

Lemma countb_spec {A : Type} (f : A -> bool) (t : tree A) :
  count f t (countb f t).
Proof.
  induction t; simpl; try solve [constructor; auto].
  destruct (f a) eqn:H; constructor; congruence.
Qed.

Fixpoint countb_list {A : Type} (f : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + countb_list f xs
  end.

Fixpoint count_failb {A : Type} (lbl : nat) (t : tree A) : nat :=
  match t with
  | Leaf x => 0
  | Fail _ n => if n =? lbl then 1 else 0
  | Choice _ t1 t2 => count_failb lbl t1 + count_failb lbl t2
  | Fix _ t1 => count_failb lbl t1
  end.

Fixpoint terminals {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf _ => 1
  | Fail _ _ => 1
  | Choice _ t1 t2 => terminals t1 + terminals t2
  | Fix _ t1 => terminals t1
  end.

Lemma terminals_nonzero {A : Type} (t : tree A) :
  (0 < terminals t)%nat.
Proof. induction t; simpl; lia. Qed.

Lemma perfect_congruent_terminals {A B : Type} (t1 : tree A) (t2 : tree B) :
  perfect t1 -> perfect t2 ->
  congruent t1 t2 ->
  terminals t1 = terminals t2.
Proof.
  revert t2.
  induction t1; intros t2 H0 H1 H2; inversion H2; subst; auto.
  - inversion H0; subst; inversion H1; subst; simpl; auto.
  - inversion H1.
Qed.

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

Lemma congruent_heightb {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent t1 t2 ->
  heightb t1 = heightb t2.
Proof. intro H; induction H; auto; simpl; auto. Qed.

Lemma perfect_height_congruent {A B : Type} (t1 : tree A) (t2 : tree B) :
  perfect t1 -> perfect t2 ->
  heightb t1 = heightb t2 ->
  congruent t1 t2.
Proof.
  revert t2; induction t1; intros t2 Hp1 Hp2 Hh.
  - destruct t2; try constructor; inversion Hh.
  - destruct t2; try constructor; inversion Hh.
  - destruct t2.
    + inversion Hh.
    + inversion Hh.
    + simpl in *.
      inversion Hp1. inversion Hp2. subst.
      apply congruent_heightb in H2.
      apply congruent_heightb in H8.
      rewrite H2, H8 in *.
      rewrite 2!Nat.max_id in *.
      inversion Hh.
      constructor.
      * apply IHt1_1; auto; lia.
      * apply IHt1_2; auto; lia.
    + inversion Hp2.
  - inversion Hp1.
Qed.

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

Lemma countb_list_app {A : Type} (f : A -> bool) (l1 l2 : list A) :
  countb_list f (l1 ++ l2) = (countb_list f l1 + countb_list f l2)%nat.
Proof. induction l1; auto; simpl; rewrite IHl1; lia. Qed.

Lemma count_true_n (n : nat) :
  countb_list id (repeat true n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma count_false_0 (n : nat) :
  countb_list id (repeat false n) = O.
Proof. induction n; simpl; auto. Qed.

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

Inductive all_fails {A : Type} : nat -> tree A -> Prop :=
| all_fails_leaf : forall lbl x, all_fails lbl (Leaf x)
| all_fails_fail : forall lbl m,
    lbl = m ->
    all_fails lbl (Fail _ m)
| all_fails_choice : forall lbl p t1 t2,
    all_fails lbl t1 ->
    all_fails lbl t2 ->
    all_fails lbl (Choice p t1 t2)
| all_fails_fix : forall lbl m t,
    all_fails lbl t ->
    all_fails lbl (Fix m t).

Lemma countb_le_terminals {A : Type} (f : A -> bool) (t : tree A) :
  (countb f t <= terminals t)%nat.
Proof. induction t; simpl; try destruct (f a); lia. Qed.

Lemma all_fails_count_failb {A : Type} `{EqType A} (lbl : nat) (t : tree A) :
  all_fails lbl t ->
  count_failb lbl t = (terminals t - countb (const true) t)%nat.
Proof.
  induction 1; simpl; subst; auto.
  - rewrite Nat.eqb_refl; reflexivity.
  - assert (countb (const true) t1 <= terminals t1)%nat.
    { apply countb_le_terminals. }
    assert (countb (const true) t2 <= terminals t2)%nat.
    { apply countb_le_terminals. }
    lia.
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

Lemma terminals_lt_choice {A : Type} (p : Q) (t1 t2 : tree A) :
  (terminals t1 < terminals (Choice p t1 t2))%nat.
Proof. generalize (terminals_nonzero t2); simpl; lia. Qed.

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

Lemma NoDup_app {A : Type} (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  NoDup l1.
Proof.
  induction l1; simpl; intro Hnodup.
  - constructor.
  - inversion Hnodup; subst.
    constructor.
    + intro HC. apply H1. apply in_or_app; intuition.
    + apply IHl1; auto.
Qed.

Lemma NoDup_app_comm {A : Type} (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
Proof.
  intro Hnodup.
  apply Permutation_NoDup with (l := l1 ++ l2); auto.
  apply Permutation_app_comm.
Qed.

Lemma in_tree_length_le_terminals {A : Type} (l : list A) (t : tree A) :
  (forall x, In x l -> in_tree x t) ->
  NoDup l ->
  (length l <= terminals t)%nat.
Proof.
  revert l.
  induction t; simpl; intros l Hin Hnodup.
  - destruct l; simpl; try lia.
    destruct l; simpl; try lia.
    pose proof (Hin a0 (or_introl eq_refl)) as H.
    pose proof (Hin a1 (or_intror (or_introl eq_refl))) as H'.
    inversion H; subst. inversion H'; subst.
    inversion Hnodup; subst.
    exfalso; apply H2; left; auto.
  - destruct l; simpl; try lia.
    specialize (Hin a (or_introl eq_refl)).
    inversion Hin.
  - assert (H: exists l1 l2, Permutation l (l1 ++ l2) /\
                        (forall x, In x l1 -> in_tree x t1) /\
                        (forall x, In x l2 -> in_tree x t2)).
    { clear IHt1 IHt2 Hnodup.
      induction l; simpl in *.
      - exists [], []. simpl. split.
        + constructor.
        + split; intuition.
      - assert (H: forall x, In x l -> in_tree x (Choice q t1 t2)).
        { intros x Hin'; apply Hin; right; auto. }
        specialize (IHl H).
        destruct IHl as (l1 & l2 & H0 & H1 & H2).
        assert (in_tree a t1 \/ in_tree a t2).
        { specialize (Hin a (or_introl (eq_refl))).
          inversion Hin; subst; intuition. }
        destruct H3.
        + exists (a :: l1), l2; simpl; intuition; subst; auto.
        + exists l1, (a :: l2); simpl; intuition; subst; auto.
          rewrite Permutation_app_comm; simpl.
          constructor; rewrite Permutation_app_comm; auto. }
    destruct H as (l1 & l2 & H0 & H1 & H2).
    assert (Hnodup1: NoDup l1).
    { apply Permutation_NoDup in H0; auto.
      eapply NoDup_app; eauto. }
    assert (Hnodup2: NoDup l2).
    { apply Permutation_NoDup in H0; auto.
      eapply NoDup_app; eauto.
      apply NoDup_app_comm; eauto. }
    apply Permutation_length in H0. rewrite H0; clear H0.
    rewrite app_length.
    specialize (IHt1 l1 H1 Hnodup1).
    specialize (IHt2 l2 H2 Hnodup2).
    lia.
  - apply IHt in Hnodup; auto.
    intros x Hin'; apply Hin in Hin'; inversion Hin'; auto.
Qed.

(** PLAN: use an alternative construction of the bernoulli tree that
  first builds the tree from a list containing a section of the
  natural numbers (so therapply e are no duplicates) and then maps a
  predicate over that tree to obtain the final result. We can easily
  prove length <= terminals for the section tree and then show that
  terminals is preserved by fmap. *)

Definition seq_tree (lbl n : nat) : tree nat := list_tree lbl (seq 0 n).

Definition bernoulli_tree_open' (lbl n d : nat) : tree bool :=
  fmap (fun i => i <? n) (seq_tree lbl d).

Definition bernoulli_tree' (lbl n d : nat) : tree bool :=
  Fix lbl (bernoulli_tree_open' lbl n d).

Lemma fmap_congruent' {A B : Type} (f : A -> B) (t : tree A) :
  congruent' t (fmap f t).
Proof. induction t; constructor; auto. Qed.

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

Lemma heightb_fmap {A B : Type} (f : A -> B) (t : tree A) :
  heightb (fmap f t) = heightb t.
Proof. induction t; simpl; auto. Qed.

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

Lemma congruent'_no_fail {A B : Type} (t1 : tree A) (t2 : tree B) :
  no_fail t1 ->
  congruent' t1 t2 ->
  no_fail t2.
Proof.
  intro Hnf. induction 1; simpl; inversion Hnf; subst; constructor; auto.
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

Lemma seq_cons a b :
  (0 < b)%nat ->
  seq a b = a :: seq (S a) (b-1).
Proof.
  destruct b; simpl; try lia.
  simpl; rewrite Nat.sub_0_r; reflexivity.
Qed.  

Lemma seq_S_n n :
  seq 0 (S n) = seq 0 n ++ [n].
Proof.
  assert (H: (S n = n + 1)%nat).
  { lia. }
  rewrite H.
  apply seq_app.
Qed.

Lemma app_cons_assoc {A : Type} (x : A) (l1 l2 : list A) :
  l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof. rewrite <- app_assoc; reflexivity. Qed.

Lemma seq_app_S b c :
  (0 < c)%nat ->
  seq 0 b ++ seq b c = seq 0 (S b) ++ seq (S b) (c-1).
Proof.
  intro Hlt.
  assert (H: seq b c = b :: seq (S b) (c - 1)).
  { apply seq_cons; auto. }
  rewrite H; clear H. simpl.
  rewrite app_cons_assoc.
  rewrite <- seq_S_n.
  reflexivity.
Qed.

Lemma seq_app' (a b : nat) :
  (a <= b)%nat ->
  seq 0 b = seq 0 a ++ seq a (b-a).
Proof.
  intro Hle.
  assert (H: (b = a + (b - a))%nat).
  { lia. }
  rewrite H at 1.
  apply seq_app.
Qed.
  
(*   revert b. *)
(*   induction a; simpl; intros b Hle. *)
(*   - rewrite Nat.sub_0_r; reflexivity. *)
(*   - rewrite IHa; try lia; clear IHa. *)
(*     assert (0 :: seq 1 a = seq O (S a))%nat. *)
(*     { reflexivity. } *)
(*     rewrite app_comm_cons. *)
(*     rewrite H; clear H. *)
(*     assert (b - S a = (b - a) - 1)%nat. *)
(*     { lia. } *)
(*     rewrite H; clear H. *)
(*     apply seq_app_S; lia. *)
(* Qed. *)

Lemma const_map_repeat {A B : Type} (f : A -> B) (l : list A) (y : B) :
  (forall x, In x l -> f x = y) ->
  map f l = repeat y (length l).
Proof.
  induction l; simpl; intro Hin; auto.
  rewrite Hin, IHl; auto.
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

Lemma fmap_terminals {A B : Type} (t : tree A) (f : A -> B) :
  terminals (fmap f t) = terminals t.
Proof. induction t; simpl; lia. Qed.

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

Lemma nondivergent_no_fix_infer_fail_lt_1 {A : Type} (n : nat) (t : tree A) :
  not_bound_in n t ->
  wf_tree t ->
  nondivergent t ->
  no_fix t ->
  infer_fail n t < 1.
Proof.
  induction t; intros Hnotbound Hwf Hnd Hnf; simpl;
    inversion Hwf; inversion Hnotbound; subst.
  - lra.
  - inversion Hnd.
  - inversion Hnf; inversion Hnd; subst.
    + rewrite H11; specialize (IHt2 H10 H4 H13 H6); lra.
    + rewrite H11; specialize (IHt1 H8 H3 H13 H1); lra.
    + destruct H14 as [H14 | H14].
      * specialize (IHt1 H8 H3 H14 H1).
        assert (infer_fail n t2 <= 1).
        { apply infer_fail_le_1; auto. }
        nra.
      * specialize (IHt2 H10 H4 H14 H6).
        assert (infer_fail n t1 <= 1).
        { apply infer_fail_le_1; auto. }
        nra.
  - inversion Hnf.
Qed.

Lemma no_fix_no_nested_fix {A : Type} (t : tree A) :
  no_fix t ->
  no_nested_fix t.
Proof. induction 1; constructor; auto. Qed.

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

Definition lbl_indicator {A : Type} (n : nat) (x : nat + A) : Q :=
  match x with
  | inl m => if m =? n then 1 else 0
  | inr _ => 0
  end.

Definition cotuple {A B C : Type} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with
  | inl a => f a
  | inr b => g b
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

Definition disjoint {A : Type} (f g : A -> Q) :=
  forall x, (0 < f x -> g x == 0) /\ (0 < g x -> f x == 0).

Lemma nodup_not_equal {A : Type} (x y : A) (l : list A) :
  NoDup (x :: y :: l) ->
  x <> y.
Proof.
  intro Hnodup; inversion Hnodup; subst.
  intro HC; subst; apply H1; left; auto.
Qed.

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

Lemma no_fix_in_tree_infer_fail_lt_1 {A : Type} (lbl : nat) (x : A) (t : tree A) :
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
  - inversion Hnf; subst.
    inversion Hwf; subst.
    inversion Hnotbound; subst.
    inversion Hub; subst.
    inversion Hin; subst.
    + specialize (IHt1 H5 H1 H2 H7 H10).
      assert (infer_fail lbl t2 <= 1).
      { apply infer_fail_le_1; auto. }
      rewrite H8; lra.
    + specialize (IHt2 H6 H3 H2 H9 H11).
      assert (infer_fail lbl t1 <= 1).
      { apply infer_fail_le_1; auto. }
      rewrite H8; lra.
  - inversion Hnf.
Qed.

Lemma ksdfg {A : Type} (lbl : nat) (f : A -> Q) (t : tree A) :
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
  { eapply no_fix_in_tree_infer_fail_lt_1; eauto. }
  cut (1 <= infer_f f t0 + infer_fail lbl t0).
  { intro Hle'. apply Qle_shift_div_l; lra. }
  apply ksdfg; auto.
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

Definition Qnum_nat (p : Q) : nat := Z.to_nat (Qnum p).
Definition Qden_nat (p : Q) : nat := Pos.to_nat (Qden p).

Fixpoint translate_bernoulli_aux {A : Type} (t : tree A) : state nat (tree A) :=
  match t with
  | Leaf x => ret (Leaf x)
  | Fail _ m => ret (Fail _ m)
  | Choice p t1 t2 =>
    bind freshLabel (fun lbl => ret (bind (bernoulli_tree lbl
                                                       (Z.to_nat (Qnum p))
                                                       (Pos.to_nat (Qden p)))
                                       (fun b => if b : bool then t1 else t2)))
  | Fix m t1 => bind (translate_bernoulli_aux t1) (fun t1' => ret (Fix m t1'))
  end.

Definition translate_bernoulli {A : Type} (t : tree A) : tree A :=
  evalState (translate_bernoulli_aux t) (list_max (all_labels t)).

Lemma fold_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) :
  join (fmap k t) = tree_bind t k.
Proof. reflexivity. Qed.

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

Lemma unfold_translate_bernoulli_aux {A : Type} f q (t1 t2 : tree A) n :
  infer_f f (evalState (translate_bernoulli_aux (Choice q t1 t2)) n) ==
  infer_f f (tree_bind (bernoulli_tree
                          (S n)
                          (Z.to_nat (Qnum q))
                          (Pos.to_nat (Qden q)))
                       (fun b : bool => if b then t1 else t2)).
Proof. reflexivity. Qed.

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

Lemma in_tree_tree_eq {A : Type} `{EqType A} (x : A) (t1 t2 : tree A) :
  tree_eq t1 t2 ->
  in_tree x t1 ->
  in_tree x t2.
Proof.
  induction 1; intro Heq; auto;
    inversion Heq; subst; solve [constructor; auto].
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

Lemma unfold_translate_bernoulli_aux' {A : Type} q (t1 t2 : tree A) lbl n :
  infer_fail lbl (evalState (translate_bernoulli_aux (Choice q t1 t2)) n) ==
  infer_fail lbl (tree_bind (bernoulli_tree
                               (S n)
                               (Z.to_nat (Qnum q))
                               (Pos.to_nat (Qden q)))
                            (fun b : bool => if b then t1 else t2)).
Proof. reflexivity. Qed.

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

Lemma translate_bernoulli_aux_infer_fail {A : Type} (t : tree A) (lbl n : nat) :
  wf_tree t ->
  (lbl <= n)%nat ->
  (forall m, (n < m)%nat -> not_in m t) ->
  infer_fail lbl t == infer_fail lbl (evalState (translate_bernoulli_aux t) n).
Proof.
  revert lbl.
  induction t; intros lbl Hwf Hle Hnotin; try reflexivity.
  - rewrite unfold_translate_bernoulli_aux'.
    rewrite infer_fail_bind_choice.
    + rewrite nd_infer_f_complement.
      * inversion Hwf; subst.
        rewrite bernoulli_tree_spec'; simpl; lra.
      * apply nd_bernoulli_tree; lia.
      * constructor; apply unbiased_list_tree_aux; constructor.
      * constructor.
        -- apply wf_list_tree_aux; constructor.
        -- apply not_bound_in_list_tree_aux; constructor.
    + intros m x Hbound.
      inversion Hwf; subst.
      apply bound_in_bernoulli_tree in Hbound; subst.
      specialize (Hnotin (S n) (Nat.lt_succ_diag_r n)).
      inversion Hnotin; subst; destruct x; auto.
    + constructor. lia.
      apply not_in_list_tree_aux; try constructor; lia.
  - inversion Hwf; subst.
    unfold evalState in *. simpl in *.
    destruct (runState (translate_bernoulli_aux t) n) eqn:Ht.
    simpl in *.
    assert (forall m, (n < m)%nat -> not_in m t).
    { intros m Hlt; specialize (Hnotin m Hlt); inversion Hnotin; auto. }
    rewrite 2!IHt; auto. reflexivity.
    destruct (le_lt_dec n0 n); auto.
    apply Hnotin in l. inversion l; subst; congruence.
Qed.

Lemma translate_bernoulli_aux_infer_f {A : Type}
      (f : A -> Q) (t : tree A) (n : nat) :
  wf_tree t ->
  (forall m, (n < m)%nat -> not_in m t) ->
  infer_f f t == infer_f f (evalState (translate_bernoulli_aux t) n).
Proof.
  induction t; intros Hwf Hnotin; try reflexivity.
  - rewrite unfold_translate_bernoulli_aux.
    rewrite infer_f_bind_choice.
    + rewrite nd_infer_f_complement.
      * inversion Hwf; subst.
        rewrite bernoulli_tree_spec'; simpl; lra.
      * apply nd_bernoulli_tree; lia.
      * constructor; apply unbiased_list_tree_aux; constructor.
      * constructor.
        -- apply wf_list_tree_aux; constructor.
        -- apply not_bound_in_list_tree_aux; constructor.
    + intros m x Hbound.
      inversion Hwf; subst.
      apply bound_in_bernoulli_tree in Hbound; subst.
      specialize (Hnotin (S n) (Nat.lt_succ_diag_r n)).
      inversion Hnotin; subst; destruct x; auto.
  - inversion Hwf; subst.
    assert (Hle: (n0 <= n)%nat).
    { destruct (le_lt_dec n0 n); auto.
      apply Hnotin in l. inversion l; subst; congruence. }
    generalize (translate_bernoulli_aux_infer_fail t n0 n H1 Hle).
    intro Hfail.
    unfold evalState in *. simpl in *.
    destruct (runState (translate_bernoulli_aux t) n) eqn:Ht.
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

Lemma translate_bernoulli_infer_f {A : Type} (f : A -> Q) (t : tree A) :
  wf_tree t ->
  infer_f f t == infer_f f (translate_bernoulli t).
Proof.
  intro Hwf.
  apply translate_bernoulli_aux_infer_f; auto.
  apply list_max_lt_not_in.
Qed.
