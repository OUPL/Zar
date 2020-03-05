(** Choice trees with fix (loop) nodes. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Structures.Monad.
Import ListNotations.

Require Import misc.
Require Import order.

(** Choice trees with fix (loop) nodes ("fix trees"?) *)
Inductive tree (A : Type) : Type :=
| Leaf : A -> tree A
| Fail : nat -> tree A
| Choice : Q -> tree A -> tree A -> tree A
| Fix : nat -> tree A -> tree A.

Fixpoint fmap {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf x => Leaf (f x)
  | Fail _ n => Fail _ n
  | Choice p t1 t2 => Choice p (fmap f t1) (fmap f t2)
  | Fix l t => Fix l (fmap f t)
  end.

Fixpoint join {A : Type} (t : tree (tree A)) : tree A :=
  match t with
  | Leaf t' => t'
  | Fail _ n => Fail _ n
  | Choice p t1 t2 => Choice p (join t1) (join t2)
  | Fix l t => Fix l (join t)
  end.

Definition tree_bind {A B : Type} (t : tree A) (k : A -> tree B) : tree B :=
  join (fmap k t).

Instance Monad_tree : Monad tree := { ret := Leaf; bind := @tree_bind }.

Definition kcomp {A B C : Type} (f : A -> tree B) (g : B -> tree C) : A -> tree C :=
  fun x => bind (f x) g.

(** Like bind but extending fail nodes instead of leaves. *)
Fixpoint fbind {A : Type} (n : nat) (t1 t2 : tree A) : tree A :=
  match t1 with
  | Leaf x => Leaf x
  | Fail _ m => if n =? m then t2 else Fail _ m
  | Choice p t' t'' => Choice p (fbind n t' t2) (fbind n t'' t2)
  | Fix l t => Fix l (if l =? n then t else fbind n t t2)
  end.

Fixpoint bound_labels {A : Type} (t : tree A) : list nat :=
  match t with
  | Choice _ t1 t2 => nodup Nat.eq_dec (bound_labels t1 ++ bound_labels t2)
  | Fix l t => nodup Nat.eq_dec (l :: bound_labels t)
  | _ => []
  end.

Fixpoint all_labels {A : Type} (t : tree A) : list nat :=
  match t with
  | Leaf _ => []
  | Fail _ l => [l]
  | Choice _ t1 t2 => nodup Nat.eq_dec (all_labels t1 ++ all_labels t2)
  | Fix l t => nodup Nat.eq_dec (l :: all_labels t)
  end.

Fixpoint subst_l {A : Type} (x y : nat) (t : tree A) : tree A :=
  match t with
  | Leaf x => Leaf x
  | Fail _ l => Fail _ (if l =? x then y else l)
  | Choice p t1 t2 => Choice p (subst_l x y t1) (subst_l x y t2)
  | Fix l t1 => Fix l (if l =? x then t1 else subst_l x y t1)
  end.

Fixpoint alpha_convert {A : Type} (f : nat -> nat) (t : tree A) : tree A :=
  match t with
  | Choice p t1 t2 => Choice p (alpha_convert f t1) (alpha_convert f t2)
  | Fix l t => Fix (f l) (subst_l l (f l) (alpha_convert f t))
  | _ => t
  end.

Fixpoint tree_chain {A : Type} (t : tree A) (l i : nat) : tree A :=
  match i with
  | O => t
  (* | S i' => fbind l (tree_chain t l i') (freshen_labels i t) *)
  | S i' =>
    let ti' := tree_chain t l i' in
    fbind l ti' (alpha_convert
                   (fun x => (x + list_max (all_labels ti') + 1)%nat) t)
  end.

Inductive tree_eq {A : Type} : tree A -> tree A -> Prop :=
| tree_eq_leaf : forall x, tree_eq (Leaf x) (Leaf x)
| tree_eq_fail : forall l, tree_eq (Fail _ l) (Fail _ l)
| tree_eq_choice : forall p q t1 t1' t2 t2',
    p == q ->
    tree_eq t1 t1' ->
    tree_eq t2 t2' ->
    tree_eq (Choice p t1 t2) (Choice q t1' t2')
| tree_eq_fix : forall l t1 t2,
    tree_eq t1 t2 ->
    tree_eq (Fix l t1) (Fix l t2).

Fixpoint tree_eqb {A : Type} `{EqType A} (t1 t2 : tree A) : bool :=
  match (t1, t2) with
  | (Leaf x, Leaf y) => eqb x y
  | (Fail _ n, Fail _ m) => eqb n m
  | (Choice p tl tr, Choice q tl' tr') =>
    match Qeq_dec p q with
    | left _ => tree_eqb tl tl' && tree_eqb tr tr'
    | right _ => false
    end
  | (Fix n t1', Fix m t2') => eqb n m && tree_eqb t1' t2'
  | _ => false
  end.

Lemma tree_eqb_spec {A : Type} `{EqType A} (t1 t2 : tree A)
  : reflect (tree_eq t1 t2) (tree_eqb t1 t2).
Proof.
  revert t2. induction t1; intro t2.
  - destruct t2; simpl; try solve [right; intro HC; inversion HC].
    destruct (eqb_spec a a0); subst.
    + left; constructor.
    + right; intro HC; inversion HC; subst; congruence.
  - destruct t2; simpl; try solve [right; intro HC; inversion HC].
    destruct (Nat.eqb_spec n n0); subst.
    + left; constructor.
    + right; intro HC; inversion HC; subst; congruence.
  - destruct t2; simpl; try constructor; try solve [intro HC; inversion HC].
    destruct (Qeq_dec q q0).
    + destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2); simpl;
        try (left; constructor; auto); right; intro HC;
          inversion HC; subst; congruence.
    + right; intro HC; inversion HC; subst; congruence.
  - destruct t2; simpl; try (right; intro HC; inversion HC).
    destruct (Nat.eqb_spec n n0); subst; simpl.
    + destruct (IHt1 t2); constructor.
      * constructor; auto.
      * intro HC; inversion HC; subst; congruence.
    + right; intro HC; inversion HC; subst; congruence.
Qed.

Inductive tree_leq {A : Type} : tree A -> tree A -> Prop :=
| tree_leq_leaf : forall x, tree_leq (Leaf x) (Leaf x)
| tree_leq_fail : forall l t, tree_leq (Fail _ l) t
| tree_leq_choice : forall p q t1 t1' t2 t2',
    p == q ->
    tree_leq t1 t1' ->
    tree_leq t2 t2' ->
    tree_leq (Choice p t1 t2) (Choice q t1' t2')
| tree_leq_fix : forall l t1 t2,
    tree_leq t1 t2 ->
    tree_leq (Fix l t1) (Fix l t2).

Fixpoint tree_leqb {A : Type} `{EqType A} (t1 t2 : tree A) : bool :=
  match (t1, t2) with
  | (Leaf x, Leaf y) => eqb x y
  | (Fail _ n, _) => true
  | (Choice p tl tr, Choice q tl' tr') =>
    match Qeq_dec p q with
    | left _ => tree_leqb tl tl' && tree_leqb tr tr'
    | right _ => false
    end
  | (Fix n t1', Fix m t2') => eqb n m && tree_leqb t1' t2'
  | _ => false
  end.

Lemma tree_leqb_spec {A : Type} `{EqType A} (t1 t2 : tree A)
  : reflect (tree_leq t1 t2) (tree_leqb t1 t2).
Proof.
  revert t2. induction t1; intro t2.
  - destruct t2; simpl; try solve [right; intro HC; inversion HC].
    destruct (eqb_spec a a0); subst.
    + left; constructor.
    + right; intro HC; inversion HC; subst; congruence.
  - destruct t2; simpl; left; constructor.
  - destruct t2; simpl; try constructor; try solve [intro HC; inversion HC].
    destruct (Qeq_dec q q0).
    + destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2); simpl;
        try (left; constructor; auto); right; intro HC;
          inversion HC; subst; congruence.
    + right; intro HC; inversion HC; subst; congruence.
  - destruct t2; simpl; try (right; intro HC; inversion HC).
    destruct (Nat.eqb_spec n n0); subst; simpl.
    + destruct (IHt1 t2); constructor.
      * constructor; auto.
      * intro HC; inversion HC; subst; congruence.
    + right; intro HC; inversion HC; subst; congruence.
Qed.

(** Not true unless we change tree_leq to be slightly less permissive
    in the fail case. *)
(* Lemma tree_eq_leq {A : Type} (t1 t2 : tree A) : *)
(*   tree_eq t1 t2 <-> tree_leq t1 t2 /\ tree_leq t2 t1. *)
(* Proof. *)
(*   split. *)
(*   - intro Heq. induction Heq; split; constructor; intuition. *)
(*   - intros [Hleq0 Hleq1]. *)
(*     + inversion Hleq0; subst; inversion Hleq1; subst. *)
(*       * constructor. *)
(*       *  *)
(* Admitted. *)

Lemma tree_leq_tree_leqb {A : Type} `{eq: EqType A} (t1 t2 : tree A) :
  tree_leq t1 t2 <-> tree_leqb t1 t2 = true.
Proof. destruct (tree_leqb_spec t1 t2); split; congruence. Qed.

Lemma tree_leq_refl {A : Type} (t : tree A) :
  tree_leq t t.
Proof. induction t; constructor; auto; reflexivity. Qed.

Lemma tree_leq_trans {A : Type} (t1 t2 t3 : tree A) :
  tree_leq t1 t2 -> tree_leq t2 t3 -> tree_leq t1 t3.
Proof.
  revert t1 t3; induction t2; intros t1 t3 H0 H1;
    inversion H0; inversion H1; subst; constructor; auto; lra.
Qed.

Program Instance OType_tree {A : Type} : OType (tree A) :=
  {| leq := tree_leq |}.
Next Obligation.
  split.
  - intro; apply tree_leq_refl.
  - intros ?; eapply tree_leq_trans; eauto.
Qed.

Inductive free_in {A : Type} : nat -> tree A -> Prop :=
| free_in_fail : forall n, free_in n (Fail _ n)
| free_in_choice1 : forall n p t1 t2,
    free_in n t1 ->
    free_in n (Choice p t1 t2)
| free_in_choice2 : forall n p t1 t2,
    free_in n t2 ->
    free_in n (Choice p t1 t2)
| free_in_fix : forall n m t,
    n <> m ->
    free_in n t ->
    free_in n (Fix m t).

Inductive not_free_in {A : Type} : nat -> tree A -> Prop :=
| not_free_in_leaf : forall n x, not_free_in n (Leaf x)
| not_free_in_fail : forall n m, n <> m -> not_free_in n (Fail _ m)
| not_free_in_choice : forall n p t1 t2,
    not_free_in n t1 ->
    not_free_in n t2 ->
    not_free_in n (Choice p t1 t2)
| not_free_in_fix0 : forall n t,
    not_free_in n (Fix n t)
| not_free_in_fix1 : forall n m t,
    n <> m ->
    not_free_in n t ->
    not_free_in n (Fix m t).

Inductive label_in {A : Type} : nat -> tree A -> Prop :=
| label_in_fail : forall l, label_in l (Fail _ l)
| label_in_choice1 : forall l p t1 t2,
    label_in l t1 ->
    label_in l (Choice p t1 t2)
| label_in_choice2 : forall l p t1 t2,
    label_in l t2 ->
    label_in l (Choice p t1 t2)
| label_in_fix1 : forall l t,
    label_in l (Fix l t)
| label_in_fix2 : forall l m t,
    l <> m ->
    label_in l t ->
    label_in l (Fix m t).

Inductive not_in {A : Type} : nat -> tree A -> Prop :=
| not_in_leaf : forall n x, not_in n (Leaf x)
| not_in_fail : forall n m, n <> m -> not_in n (Fail _ m)
| not_in_choice : forall n p t1 t2,
    not_in n t1 ->
    not_in n t2 ->
    not_in n (Choice p t1 t2)
| not_in_fix : forall n m t,
    n <> m ->
    not_in n t ->
    not_in n (Fix m t).

Inductive bound_in {A : Type} : nat -> tree A -> Prop :=
| bound_in_choice1 : forall n p t1 t2,
    bound_in n t1 ->
    bound_in n (Choice p t1 t2)
| bound_in_choice2 : forall n p t1 t2,
    bound_in n t2 ->
    bound_in n (Choice p t1 t2)
| bound_in_fix1 : forall n t,
    bound_in n (Fix n t)
| bound_in_fix2 : forall n m t,
    n <> m ->
    bound_in n t ->
    bound_in n (Fix m t).

Inductive not_bound_in {A : Type} : nat -> tree A -> Prop :=
| not_bound_in_leaf : forall n x, not_bound_in n (Leaf x)
| not_bound_in_fail : forall n m, not_bound_in n (Fail _ m)
| not_bound_in_choice : forall n p t1 t2,
    not_bound_in n t1 ->
    not_bound_in n t2 ->
    not_bound_in n (Choice p t1 t2)
| not_bound_in_fix : forall n m t,
    n <> m ->
    not_bound_in n t ->
    not_bound_in n (Fix m t).

Lemma bound_in_dec {A : Type} (l : nat) (t : tree A) :
  bound_in l t \/ not_bound_in l t.
Proof.
  induction t.
  - right; constructor.
  - right; constructor.
  - destruct IHt1, IHt2.
    + left; constructor; auto.
    + left; constructor; auto.
    + left; apply bound_in_choice2; auto.
    + right; constructor; auto.
  - destruct IHt.
    + left; destruct (Nat.eqb_spec l n); subst; constructor; auto.
    + destruct (Nat.eqb_spec l n); subst.
      * left; constructor; auto.
      * right; constructor; auto.
Qed.

Lemma free_in_dec {A : Type} (n : nat) (t : tree A) :
  free_in n t \/ not_free_in n t.
Proof.
  induction t.
  - right; constructor.
  - destruct (Nat.eqb_spec n n0); subst.
    + left; constructor.
    + right; constructor; auto.
  - destruct IHt1; destruct IHt2.
    + left; constructor; auto.
    + left; constructor; auto.
    + left; apply free_in_choice2; auto.
    + right; constructor; auto.
  - destruct IHt.
    + destruct (Nat.eqb_spec n n0); subst.
      * right; constructor.
      * left; constructor; auto.
    + destruct (Nat.eqb_spec n n0); subst.
      * right; constructor.
      * right; constructor; auto.
Qed.

Lemma label_in_bound_or_free {A : Type} (l : nat) (t : tree A) :
  label_in l t <-> bound_in l t \/ free_in l t.
Proof.
  split.
  - induction t; intro Hin; inversion Hin; subst.
    + right; constructor.
    + destruct (IHt1 H1).
      * left; constructor; auto.
      * right; constructor; auto.
    + destruct (IHt2 H1).
      * left; apply bound_in_choice2; auto.
      * right; apply free_in_choice2; auto.
    + left; constructor.
    + destruct (IHt H3).
      * left; constructor; auto.
      * right; constructor; auto.
  - induction t; intros [Hbound|Hfree]; try inversion Hbound;
      try inversion Hfree; subst; try solve [constructor; auto].
Qed.

Lemma bound_in_label_in {A : Type} (l : nat) (t : tree A) :
  bound_in l t -> label_in l t.
Proof. intro; apply label_in_bound_or_free; auto. Qed.

Lemma free_in_label_in {A : Type} (l : nat) (t : tree A) :
  free_in l t -> label_in l t.
Proof. intro; apply label_in_bound_or_free; auto. Qed.

Lemma free_in_not_free_in {A : Type} (n : nat) (t : tree A) :
  ~ free_in n t <-> not_free_in n t.
Proof.
  split.
  - induction t; intro H.
    + constructor.
    + destruct (Nat.eqb_spec n n0); subst.
      * exfalso; apply H; constructor.
      * constructor; auto.
    + constructor.
      * apply IHt1; intro HC; apply H; constructor; auto.
      * apply IHt2; intro HC; apply H; apply free_in_choice2; auto.
    + destruct (Nat.eqb_spec n n0); subst; constructor; auto;
        apply IHt; intro HC; apply H; constructor; auto.
  - intro H; induction H; intro HC; inversion HC; subst; congruence.
Qed.

Lemma free_in_not_free_in' {A : Type} (n : nat) (t : tree A) :
  free_in n t <-> ~ not_free_in n t.
Proof.
  split; intro H.
  - induction H; intro HC; inversion HC; subst; congruence.
  - revert H. revert n. induction t; intros m H.
    + exfalso. apply H. constructor.
    + destruct (Nat.eqb_spec m n); subst.
      * constructor.
      * exfalso; apply H; constructor; auto.
    + destruct (free_in_dec m t1).
      * constructor; auto.
      * apply free_in_choice2. apply IHt2.
        intro HC. apply H. constructor; auto.
    + destruct (Nat.eqb_spec m n); subst.
      * exfalso. apply H. constructor.
      * constructor; auto. apply IHt.
        intro HC. apply H. constructor; auto.
Qed.

Lemma bound_in_not_bound_in {A : Type} (n : nat) (t : tree A) :
  ~ bound_in n t <-> not_bound_in n t.
Proof.
  split.
  - induction t; intro H; try solve [constructor].
    + constructor.
      * apply IHt1. intro HC. apply H. constructor; auto.
      * apply IHt2. intro HC. apply H. apply bound_in_choice2; auto.
    + destruct (Nat.eqb_spec n n0); subst.
      * exfalso. apply H. constructor.
      * constructor; auto. apply IHt.
        intro HC. apply H. constructor; auto.
  - intro H. induction H.
    + intro HC; inversion HC.
    + intro HC; inversion HC.
    + intro HC.
      inversion HC; subst; intuition.
    + intro HC. inversion HC; subst; congruence.
Qed.

Lemma not_in_not_bound_in {A : Type} (n : nat) (t : tree A) :
  not_in n t -> not_bound_in n t.
Proof.
  induction t; intro Hnotin; try solve [constructor];
    inversion Hnotin; subst; constructor; auto.
Qed.

Lemma not_in_not_free_in {A : Type} (n : nat) (t : tree A) :
  not_in n t -> not_free_in n t.
Proof.
  induction t; intro Hnotin; try solve [constructor];
    inversion Hnotin; subst; constructor; auto.
Qed.

Lemma not_in_not_bound_or_free {A : Type} (n : nat) (t : tree A) :
  not_in n t <-> ~ (free_in n t \/ bound_in n t).
Proof.
  split; intro H.
  - intro HC; induction H; destruct HC as [HC | HC];
      inversion HC; subst; intuition.
  - induction t.
    + constructor.
    + destruct (Nat.eqb_spec n n0); subst.
      * exfalso; apply H; left; constructor.
      * constructor; auto.
    + constructor.
      * apply IHt1. intros [HC | HC]; apply H.
        ** left; constructor; auto.
        ** right; constructor; auto.
      * apply IHt2. intros [HC | HC]; apply H.
        ** left; apply free_in_choice2; auto.
        ** right; apply bound_in_choice2; auto.
    + destruct (Nat.eqb_spec n n0); subst.
      * exfalso. apply H. right; constructor.
      * constructor; auto. apply IHt. intros [HC | HC]; apply H.
        ** left; constructor; auto.
        ** right; constructor; auto.
Qed.

Lemma not_in_not_bound_and_not_free {A : Type} (n : nat) (t : tree A) :
  not_in n t <-> not_free_in n t /\ not_bound_in n t.
Proof.
  split.
  - intro Hnotin; apply not_in_not_bound_or_free in Hnotin; split.
    + apply free_in_not_free_in; intro HC; apply Hnotin; auto.
    + apply bound_in_not_bound_in; intro HC; apply Hnotin; auto.
  - intros [Hnotfree Hnotbound].
    apply not_in_not_bound_or_free; intros [HC|HC].
    + apply free_in_not_free_in in Hnotfree; auto.
    + apply bound_in_not_bound_in in Hnotbound; auto.
Qed.

Lemma label_in_dec {A : Type} (l : nat) (t : tree A) :
  label_in l t \/ not_in l t.
Proof.
  destruct (bound_in_dec l t); destruct (free_in_dec l t);
    try solve [left; apply label_in_bound_or_free; auto];
    right; auto; apply not_in_not_bound_and_not_free; auto.
Qed.

Lemma label_in_not_in {A : Type} (l : nat) (t : tree A) :
  ~ label_in l t <-> not_in l t.
Proof.
  split.
  - induction t; simpl; intro Hin.
    + constructor.
    + constructor; intro HC; subst; apply Hin; constructor.
    + constructor; try apply IHt1; try apply IHt2;
        intro HC; apply Hin; solve [constructor; auto].
    + destruct (Nat.eqb_spec l n); subst.
      * exfalso; apply Hin; constructor.
      * constructor; auto; apply IHt;
          intro HC; apply Hin; constructor; auto.
  - induction t; intros Hnotin HC;
      inversion HC; inversion Hnotin; subst; auto.
    + apply IHt1; auto.
    + apply IHt2; auto.
    + apply IHt; auto.
Qed.

Lemma not_in_label_in {A : Type} (l : nat) (t : tree A) :
  label_in l t <-> ~ not_in l t.
Proof.
  split.
  - intros Hin Hnotin; apply label_in_not_in in Hnotin; congruence.
  - intro; apply Decidable.not_not.
    + destruct (label_in_dec l t); left; auto; congruence.
    + intro HC. apply label_in_not_in in HC; congruence.
Qed.

Inductive wf_tree {A : Type} : tree A -> Prop :=
| wf_leaf : forall x, wf_tree (Leaf x)
| wf_fail : forall n, wf_tree (Fail _ n)
| wf_choice : forall p t1 t2,
    0 <= p <= 1 ->
    wf_tree t1 -> wf_tree t2 ->
    wf_tree (Choice p t1 t2)
| wf_fix : forall n t,
    wf_tree t ->
    (* n is not bound by another fix inside t. *)
    not_bound_in n t ->
    (* TODO: maybe also any label that is free in t is not also bound
       in t. *)
    wf_tree (Fix n t).

(** A strengthened wf predicate.  *)
Inductive wf_tree' {A : Type} : tree A -> Prop :=
| wf_leaf' : forall x, wf_tree' (Leaf x)
| wf_fail' : forall n, wf_tree' (Fail _ n)
| wf_choice' : forall p t1 t2,
    0 <= p <= 1 ->
    wf_tree' t1 -> wf_tree' t2 ->
    wf_tree' (Choice p t1 t2)
| wf_fix' : forall n t,
    wf_tree' t ->
    (* n is not bound by another fix inside t. *)
    (forall m, bound_in m t -> (n < m)%nat) ->
    (forall m, free_in m t -> (m <= n)%nat) ->
    (* TODO: maybe also any label that is free in t is not also bound
       in t. *)
    wf_tree' (Fix n t).

Lemma wf_tree'_wf_tree {A : Type} (t : tree A) :
  wf_tree' t -> wf_tree t.
Proof.
  induction t; simpl; intro Hwf; constructor; inversion Hwf; subst; auto.
  apply bound_in_not_bound_in; intro HC.
  apply H2 in HC; lia.
Qed.

Lemma bound_in_bind {A B : Type} (t : tree A) (k : A -> tree B) (m : nat) :
  bound_in m (bind t k) ->
  bound_in m t \/ exists x, bound_in m (k x).
Proof.
  simpl; unfold tree_bind; revert m k.
  induction t; intros m k Hbound; simpl in Hbound.
  - right. exists a. apply Hbound.
  - inversion Hbound; subst.
  - inversion Hbound; subst.
    + apply IHt1 in H1. destruct H1; intuition.
      left; constructor; auto.
    + apply IHt2 in H1. destruct H1; intuition.
      left. apply bound_in_choice2; auto.
  - inversion Hbound; subst.
    left; constructor; auto.
    apply IHt in H3. destruct H3; intuition.
    left. constructor; auto.
Qed.

Lemma bound_in_bind' {A B : Type} (l : nat) (t : tree A) (k : A -> tree B) :
  bound_in l (bind t k) ->
  (forall x, not_bound_in l (k x)) ->
  bound_in l t.
Proof.
  intros Hbound Hnotin.
  apply bound_in_bind in Hbound. destruct Hbound; auto.
  destruct H. specialize (Hnotin x). apply bound_in_not_bound_in in Hnotin. congruence.
Qed.

Lemma free_in_bind {A B : Type} (t : tree A) (k : A -> tree B) (m : nat) :
  free_in m (bind t k) ->
  free_in m t \/ exists x, free_in m (k x).
Proof.
  simpl; unfold tree_bind; revert m k.
  induction t; intros m k Hfree; simpl in Hfree.
  - right. exists a. apply Hfree.
  - inversion Hfree; subst. left; constructor.
  - inversion Hfree; subst.
    + apply IHt1 in H1. destruct H1; intuition.
      left; constructor; auto.
    + apply IHt2 in H1. destruct H1; intuition.
      left. apply free_in_choice2; auto.
  - inversion Hfree; subst. apply IHt in H3. destruct H3; intuition.
    left. constructor; auto.
Qed.

Lemma free_in_bind' {A B : Type} (l : nat) (t : tree A) (k : A -> tree B) :
  free_in l (bind t k) ->
  (forall x, not_free_in l (k x)) ->
  free_in l t.
Proof.
  intros Hfree Hnotin.
  apply free_in_bind in Hfree. destruct Hfree; auto.
  destruct H. specialize (Hnotin x).
  apply free_in_not_free_in in Hnotin. congruence.
Qed.

Lemma wf_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) :
  (forall n x, bound_in n t -> not_bound_in n (k x)) ->
  wf_tree t ->
  (forall x, wf_tree (k x)) ->
  wf_tree (tree_bind t k).
Proof.
  unfold tree_bind. revert k.
  induction t; intros k Hnotbound Hwf_t Hwf_k; simpl; auto.
  - constructor.
  - inversion Hwf_t; subst.
    constructor; auto.
    + apply IHt1; auto; intros n x Hbound.
      apply Hnotbound; constructor; auto.
    + apply IHt2; auto; intros n x Hbound.
      apply Hnotbound; apply bound_in_choice2; auto.
  - inversion Hwf_t; subst.
    eapply IHt in Hwf_k; auto.
    + constructor; auto.
      apply bound_in_not_bound_in.
      intro HC. apply bound_in_bind in HC. destruct HC.
      * apply bound_in_not_bound_in in H2; congruence.
      * assert (H0: bound_in n (Fix n t)).
        { constructor; auto. }
        destruct H as [x H]. specialize (Hnotbound n x H0).
        apply bound_in_not_bound_in in Hnotbound. apply Hnotbound; auto.
    + intros n0 x Hbound. apply Hnotbound.
      destruct (Nat.eqb_spec n0 n); subst; constructor; auto.
Qed.

Lemma wf_tree'_bind {A B : Type} (t : tree A) (k : A -> tree B) :
  (forall n m x, bound_in n t -> bound_in m (k x) -> (n < m)%nat) ->
  (forall n m x, bound_in n t -> free_in m (k x) -> (m <= n)%nat) ->
  wf_tree' t ->
  (forall x, wf_tree' (k x)) ->
  wf_tree' (tree_bind t k).
Proof.
  unfold tree_bind. revert k.
  induction t; intros k Hbound_lt Hfree_le Hwf_t Hwf_k; simpl; auto.
  - constructor.
  - inversion Hwf_t; subst.
    constructor; auto.
    + apply IHt1; auto; intros n x Hbound.
      * intros; eapply Hbound_lt; eauto; constructor; auto.
      * intros; eapply Hfree_le; eauto; constructor; auto.
    + apply IHt2; auto; intros n x Hbound.
      * intros; eapply Hbound_lt; eauto; solve [constructor; auto].
      * intros; eapply Hfree_le; eauto; solve [constructor; auto].
  - inversion Hwf_t; subst.
    eapply IHt in Hwf_k; auto.
    + constructor; auto.
      * intros m Hbound.
        apply bound_in_bind in Hbound. destruct Hbound as [Hbound|Hbound].
        ++ apply H2; auto.
        ++ destruct Hbound as [x Hbound].
           eapply Hbound_lt; eauto; constructor.
      * intros m Hfree.
        apply free_in_bind in Hfree. destruct Hfree as [Hfree|Hfree].
        apply H3; auto.
        destruct Hfree as [x Hfree].
        eapply Hfree_le; eauto; constructor.
    + intros n0 m x Hboundt Hboundk.
      eapply Hbound_lt; eauto.
      destruct (Nat.eqb_spec n0 n); subst; constructor; auto.
    + intros n0 m x Hbound Hfree.
      eapply Hfree_le; eauto.
      destruct (Nat.eqb_spec n0 n); subst; constructor; auto.
Qed.

Lemma not_bound_in_fbind {A : Type} (t1 t2 : tree A) (l m : nat) :
  not_bound_in m t1 ->
  not_bound_in m t2 ->
  not_bound_in m (fbind l t1 t2).
Proof.
  revert t2 l m; induction t1; intros t2 l m H0 H1; simpl; auto.
  - destruct (l =? n); auto.
  - inversion H0; subst; constructor.
    + apply IHt1_1; auto.
    + apply IHt1_2; auto.
  - inversion H0; subst; constructor; auto.
    destruct (Nat.eqb_spec n l); subst; auto.
Qed.

Lemma wf_fbind {A : Type} (t1 t2 : tree A) (l : nat) :
  wf_tree t1 ->
  wf_tree t2 ->
  (forall n, bound_in n t1 -> not_bound_in n t2) ->
  wf_tree (fbind l t1 t2).
Proof.
  revert t2 l. induction t1; intros t2 l Hwf1 Hwf2 Hnotbound; simpl; auto.
  - destruct (l =? n); auto.
  - inversion Hwf1; subst. constructor; auto.
    + apply IHt1_1; auto; intros; apply Hnotbound; constructor; auto.
    + apply IHt1_2; auto; intros; apply Hnotbound; apply bound_in_choice2; auto.
  - inversion Hwf1; subst.
    destruct (Nat.eqb_spec n l); subst; auto.
    constructor.
    + apply IHt1; auto; intros; apply Hnotbound.
      destruct (Nat.eqb_spec n1 n); subst; constructor; auto.
    + apply not_bound_in_fbind; auto; apply Hnotbound; constructor.
Qed.

Lemma bound_in_subst_l {A : Type} (t : tree A) (l n m : nat) :
  bound_in l t <-> bound_in l (subst_l n m t).
Proof.
  split; intro Hbound; induction t; inversion Hbound; subst;
    try solve [apply bound_in_choice2; auto];
    constructor; auto; destruct (Nat.eqb_spec n0 n); subst; auto.
Qed.

Lemma not_bound_in_subst_l {A : Type} (t : tree A) (l n m : nat) :
  not_bound_in l t ->
  not_bound_in l (subst_l n m t).
Proof.
  intros Hnotbound.
  apply bound_in_not_bound_in.
  apply bound_in_not_bound_in in Hnotbound.
  intro HC; apply bound_in_subst_l in HC; auto.
Qed.

Lemma wf_subst_l {A : Type} (t : tree A) (n m : nat) :
  wf_tree t ->
  wf_tree (subst_l n m t).
Proof.
  induction t; intro Hwf; simpl; auto.
  - constructor.
  - inversion Hwf; subst.
    constructor; auto.
  - inversion Hwf; subst.
    constructor.
    + destruct (Nat.eqb_spec n0 n); subst; auto.
    + destruct (Nat.eqb_spec n0 n); subst; auto.
      apply not_bound_in_subst_l; auto.
Qed.

Lemma not_bound_in_alpha_convert {A : Type} (t : tree A) (g : nat -> nat) (m : nat) :
  (forall x y, g x = g y -> x = y) ->
  not_bound_in m t ->
  not_bound_in (g m) (alpha_convert g t).
Proof.
  revert m.
  induction t; intros m Hinj Hnotbound; simpl; try solve [constructor].
  - inversion Hnotbound; subst; constructor; auto.
  - inversion Hnotbound; subst.
    constructor. intro HC. apply H2. apply Hinj; auto.
    apply not_bound_in_subst_l, IHt; auto.
Qed.

Lemma wf_tree_alpha_convert {A : Type} (t : tree A) (n m : nat) :
  wf_tree t ->
  wf_tree (alpha_convert (fun x : nat => (x + n + m)%nat) t).
Proof.
  induction t; intro Hwf; simpl; auto.
  - inversion Hwf; subst; constructor; auto.
  - inversion Hwf; subst.
    constructor.
    + apply wf_subst_l. apply IHt; auto.
    + apply not_bound_in_subst_l.
      set (g := fun x => (x + n + m)%nat).
      assert ((n0 + n + m)%nat = g n0); auto.
      rewrite H.
      apply not_bound_in_alpha_convert; auto.
      unfold g; intuition.
Qed.

Lemma bound_in_alpha_convert_lt {A : Type} (t : tree A) (l m : nat) :
  bound_in l (alpha_convert (fun x : nat => (x + m + 1)%nat) t) ->
  (m < l)%nat.
Proof.
  revert l m; induction t; intros l m Hbound;
    simpl in Hbound; try solve [inversion Hbound].
  - inversion Hbound; subst.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - inversion Hbound; subst; try lia.
    apply IHt. apply bound_in_subst_l in H3; auto.
Qed.

Lemma all_labels_spec {A : Type} (t : tree A) (l : nat) :
  label_in l t <-> In l (all_labels t).
Proof.
  split.
  - induction t; intro Hbound; inversion Hbound; subst; simpl; auto.
    + apply nodup_In; apply in_or_app; auto.
    + apply nodup_In; apply in_or_app; auto.
    + destruct (in_dec Nat.eq_dec n (all_labels t)).
      * apply nodup_In; auto.
      * constructor; auto.
    + destruct (in_dec Nat.eq_dec n (all_labels t)).
      * apply nodup_In; auto.
      * right. apply nodup_In; auto.
  - induction t; intro Hin.
    + inversion Hin.
    + inversion Hin; subst. constructor. inversion H.
    + simpl in Hin; apply nodup_In, in_app_or in Hin;
        destruct Hin; try solve [constructor; auto].
    + destruct (Nat.eqb_spec l n); subst.
      * constructor.
      * constructor; auto. apply IHt.
        simpl in Hin.
        destruct (in_dec Nat.eq_dec n (all_labels t)).
        ++ eapply nodup_In; eauto.
        ++ destruct Hin; subst. congruence.
           eapply nodup_In; eauto.
Qed.

Lemma bound_labels_spec {A : Type} (t : tree A) (l : nat) :
  bound_in l t <-> In l (bound_labels t).
Proof.
  split.
  - induction t; intro Hbound; inversion Hbound; subst; simpl.
    + apply nodup_In; apply in_or_app; auto.
    + apply nodup_In; apply in_or_app; auto.
    + destruct (in_dec Nat.eq_dec n (bound_labels t)).
      * apply nodup_In; auto.
      * constructor; auto.
    + destruct (in_dec Nat.eq_dec n (bound_labels t)).
      * apply nodup_In; auto.
      * right. apply nodup_In; auto.
  - induction t; intro Hin.
    + inversion Hin.
    + inversion Hin.
    + simpl in Hin; apply nodup_In, in_app_or in Hin;
        destruct Hin; try solve [constructor; auto].
    + destruct (Nat.eqb_spec l n); subst.
      * constructor.
      * constructor; auto. apply IHt.
        simpl in Hin.
        destruct (in_dec Nat.eq_dec n (bound_labels t)).
        ++ eapply nodup_In; eauto.
        ++ destruct Hin; subst. congruence.
           eapply nodup_In; eauto.
Qed.

Lemma bound_labels_leq_all_labels {A : Type} :
  leq (@bound_labels A) all_labels.
Proof.
  intros t n H; apply bound_labels_spec in H;
    apply all_labels_spec; apply bound_in_label_in; auto.
Qed.

Lemma wf_tree_fbind_alpha_convert {A : Type} (t1 t2 : tree A) (l : nat) :
  wf_tree t1 ->
  wf_tree t2 ->
  (forall m, bound_in m t2 -> bound_in m t1) ->
  wf_tree
    (fbind l t1
           (alpha_convert
              (fun x : nat => (x + list_max (all_labels t1) + 1)%nat) t2)).
Proof.
  intros. apply wf_fbind; auto.
  - apply wf_tree_alpha_convert; auto.
  - intros n Hbound; apply bound_in_not_bound_in.
    intro HC; apply bound_in_alpha_convert_lt in HC.
    apply bound_in_label_in in Hbound.
    apply all_labels_spec in Hbound.
    apply list_max_spec in Hbound. lia.
Qed.

Lemma bound_in_fbind {A : Type} (t1 t2 : tree A) (l m : nat) :
  bound_in m t1 ->
  bound_in m (fbind l t1 t2).
Proof.
  induction t1; intros Hbound; inversion Hbound; subst;
    try solve [apply bound_in_choice2; auto];
    constructor; auto; destruct (Nat.eqb_spec n l); subst; auto.
Qed.

Lemma tree_chain_wf {A : Type} (t : tree A) (l i : nat) :
  wf_tree t ->
  wf_tree (tree_chain t l i).
Proof.
  revert l t.
  induction i; intros l t Hwf; auto.
  simpl.
  apply wf_tree_fbind_alpha_convert; auto.
  intros m Hbound. clear IHi.
  induction i; auto; simpl.
  apply bound_in_fbind; auto.
Qed.

Lemma fbind_assoc {A : Type} (t1 t2 t3 : tree A) (n : nat) :
  fbind n t1 (fbind n t2 t3) = fbind n (fbind n t1 t2) t3.
Proof.
  revert t2 t3 n. induction t1; intros t2 t3 m; simpl.
  - reflexivity.
  - destruct (Nat.eqb_spec m n); subst; simpl.
    + reflexivity.
    + destruct (Nat.eqb_spec m n); subst; congruence; reflexivity.
  - rewrite IHt1_1, IHt1_2; reflexivity.
  - destruct (Nat.eqb_spec n m); subst.
    + reflexivity.
    + rewrite IHt1; reflexivity.
Qed.

Lemma not_in_subst_l {A : Type} (t : tree A) (l m n : nat) :
  n <> m ->
  not_in m t ->
  not_in m (subst_l l n t).
Proof.
  induction t; intros Hneq Hnotin; simpl; auto; inversion Hnotin; subst.
  - destruct (Nat.eqb_spec n0 l); subst; constructor; auto.
  - constructor; auto.
  - constructor; auto.
    destruct (Nat.eqb_spec n0 l); subst; auto.
Qed.

Lemma not_free_in_subst_l {A : Type} (t : tree A) (l m : nat) :
  l <> m ->
  not_free_in l (subst_l l m t).
Proof.
  induction t; intro Hneq; simpl.
  - constructor.
  - constructor; destruct (Nat.eqb_spec n l); subst; auto.
  - constructor; auto.
  - destruct (Nat.eqb_spec n l); subst; constructor; auto.
Qed.

(** Subtlety here: what happens when (g m) is bound somewhere? Then it
   may appear free under that binder without violating (not_free_in (g
   m) t). However, when we alpha convert that bound occurrence of (g
   m) we also replace all free occurrences underneath it so that it
   doesn't become free in the overall tree. *)
Lemma not_in_alpha_convert {A : Type} (t : tree A) (g : nat -> nat) (m : nat) :
  (forall x, x <> g x) ->
  (forall x y, g x = g y -> x = y) ->
  not_bound_in m t ->
  not_free_in (g m) t ->
  not_in (g m) (alpha_convert g t).
Proof.
  induction t; intros Hneq Hinj Hnotbound Hnotin; simpl.
  - constructor.
  - inversion Hnotin; subst. constructor; auto.
  - inversion Hnotbound; inversion Hnotin; subst. constructor.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - 
    destruct (Nat.eqb_spec (g m) n); subst.
    + constructor; auto.
      apply not_in_not_bound_and_not_free. split.
      * apply not_free_in_subst_l; auto.
      * inversion Hnotbound; subst.
        apply not_bound_in_subst_l.
        apply not_bound_in_alpha_convert; auto.
    + inversion Hnotbound; subst. constructor; auto.
      apply not_in_subst_l ; auto.
      apply IHt; auto.
      inversion Hnotin; subst; auto; congruence.
Qed.

Lemma not_in_alpha_convert' {A : Type} (t : tree A) (g : nat -> nat) (m : nat) :
  (forall x y, g x = g y -> x = y) ->
  not_bound_in m t ->
  not_in (g m) t ->
  not_in (g m) (alpha_convert g t).
Proof.
  induction t; intros Hinj Hnotbound Hnotin; simpl.
  - constructor.
  - inversion Hnotin; subst. constructor; auto.
  - inversion Hnotbound; inversion Hnotin; subst. constructor.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - inversion Hnotbound; subst.
    constructor. intuition.
    apply not_in_subst_l; auto.
    apply IHt; auto.
    inversion Hnotin; subst; auto.    
Qed.

Lemma bound_in_lt_not_bound_in {A : Type} (t : tree A) (m : nat) :
  (forall x, bound_in x t -> (m < x)%nat) ->
  not_bound_in m t.
Proof.
  induction t; intro Hlt; simpl.
  - constructor.
  - constructor.
  - constructor.
    + apply IHt1; intros x Hbound; apply Hlt; constructor; auto.
    + apply IHt2; intros x Hbound; apply Hlt; apply bound_in_choice2; auto.
  - destruct (Nat.eqb_spec m n); subst.
    + specialize (Hlt n (bound_in_fix1 _ _)); lia.
    + constructor; auto. apply IHt. intros x Hbound; apply Hlt.
      destruct (Nat.eqb_spec x n); subst; constructor; auto.
Qed.

Lemma bound_in_alpha_convert_exists {A : Type} (t : tree A) (f : nat -> nat) (l : nat) :
  bound_in l (alpha_convert f t) ->
  exists m, bound_in m t /\ f m = l.
Proof.
  induction t; intro Hbound; inversion Hbound; subst.
  - apply IHt1 in H1; destruct H1 as [m [H1 H2]]; subst.
    exists m; split; auto; constructor; auto.
  - apply IHt2 in H1; destruct H1 as [m [H1 H2]]; subst.
    exists m; split; auto; apply bound_in_choice2; auto.
  - exists n; split; auto; constructor.
  - apply bound_in_subst_l in H3. apply IHt in H3.
    destruct H3 as [m [H3 H4]]; subst.
    exists m. split; auto.
    destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.  
Lemma bound_in_tree_chain {A : Type} (t : tree A) (l m n : nat) :
  bound_in l t ->
  bound_in l (tree_chain t m n).
Proof.
  induction n; simpl; auto; intros; apply bound_in_fbind; auto.
Qed.

Lemma list_max_lt_not_in {A : Type} (t : tree A) (m : nat) :
  (list_max (all_labels t) < m)%nat ->
  not_in m t.
Proof.
  intro Hlt.
  apply label_in_not_in; intro HC.
  apply all_labels_spec in HC.
  apply list_max_spec in HC. lia.
Qed.

Lemma list_max_subset (l1 l2 : list nat) :
  (forall x, In x l1 -> In x l2) -> (* l1 ⊆ l2 *)
  (list_max l1 <= list_max l2)%nat.
Proof.
  induction l1; intro Hsubset; simpl.
  - lia.
  - destruct (Nat.leb_spec0 a (list_max l1)).
    + rewrite Nat.max_r; auto. apply IHl1.
      intros x Hin. apply Hsubset. right; auto.
    + rewrite Nat.max_l; try lia.
      apply list_max_spec; apply Hsubset; constructor; reflexivity.
Qed.

Lemma tree_leq_fbind {A : Type} (t1 t2 : tree A) (l : nat) :
  tree_leq t1 (fbind l t1 t2).
Proof.
  induction t1; simpl.
  - constructor.
  - destruct (Nat.eqb_spec l n); subst; constructor.
  - constructor; auto; reflexivity.
  - constructor.
    destruct (Nat.eqb_spec n l); subst; auto; apply tree_leq_refl.
Qed.

Lemma tree_leq_tree_chain {A : Type} (t : tree A) (l n : nat) :
  tree_leq t (tree_chain t l n).
Proof.
  induction n; simpl.
  - apply tree_leq_refl.
  - eapply tree_leq_trans; eauto. apply tree_leq_fbind.
Qed.

Lemma in_bound_labels_choice1 {A : Type} (t1 t2 : tree A) (p : Q) (x : nat) :
  In x (bound_labels t1) ->
  In x (bound_labels (Choice p t1 t2)).
Proof.
  intro Hin; apply bound_labels_spec in Hin.
  apply bound_labels_spec; constructor; auto.
Qed.

Lemma in_bound_labels_choice2 {A : Type} (t1 t2 : tree A) (p : Q) (x : nat) :
  In x (bound_labels t2) ->
  In x (bound_labels (Choice p t1 t2)).
Proof.
  intro Hin; apply bound_labels_spec in Hin.
  apply bound_labels_spec; solve [constructor; auto].
Qed.

Lemma in_bound_labels_fix1 {A : Type} (t : tree A) (x : nat) :
  In x (bound_labels (Fix x t)).
Proof. apply bound_labels_spec; constructor. Qed.

Lemma in_bound_labels_fix2 {A : Type} (t : tree A) (l x : nat) :
  In x (bound_labels t) ->
  In x (bound_labels (Fix l t)).
Proof.
  intro Hin; apply bound_labels_spec in Hin.
  apply bound_labels_spec.
  destruct (Nat.eqb_spec x l); subst; constructor; auto.
Qed.

Lemma bound_in_monotone {A : Type} (t1 t2 : tree A) (x : nat) :
  tree_leq t1 t2 -> bound_in x t1 -> bound_in x t2.
Proof.
  intros Hleq; induction Hleq; intro Hbound; auto;
    inversion Hbound; subst; solve [constructor; auto].
Qed.

Lemma bound_labels_monotone {A : Type} : monotone (@bound_labels A).
  intros t1 t2 Hleq x Hin.
  apply bound_labels_spec.
  eapply bound_in_monotone; eauto.
  apply bound_labels_spec; auto.
Qed.

(** free_labels isn't monotone in general. Considering the following
    case: t1 = Fail 0, t2 = Leaf x. We have t1 <= t2 with label 0
    appearing free in t1 but not in t2. However, we can prove this
    specifically for fbind l t1 t2 if we know that l appears free in
    t2. *)
Lemma free_in_fbind {A : Type} (t1 t2 : tree A) (l x : nat) :
  free_in l t2 -> free_in x t1 -> free_in x (fbind l t1 t2).
Proof.
  induction t1; intros H0 H1; simpl; auto;
    inversion H1; subst; try solve [constructor; auto].
  - destruct (Nat.eqb_spec l n); subst; auto.
  - constructor; auto; destruct (Nat.eqb_spec n l); subst; auto.
Qed.

Lemma free_in_subst_l {A : Type} (t : tree A) (l x y : nat) :
  l <> x ->
  free_in l t -> free_in l (subst_l x y t).
Proof.
  induction t; intros Hneq Hfree; simpl; auto; inversion Hfree; subst.
  - destruct (Nat.eqb_spec n x); subst; auto; congruence.
  - constructor; auto.
  - solve [constructor; auto].
  - constructor; auto.
    destruct (Nat.eqb_spec n x); subst; auto.
Qed.

Lemma free_in_subst_l' {A : Type} (t : tree A) (l x y : nat) :
  l <> y ->
  free_in l (subst_l x y t) -> free_in l t.
Proof.
  induction t; intros Hneq Hfree; simpl; auto; inversion Hfree; subst.
  - destruct (Nat.eqb_spec n x); subst; try constructor; congruence.
  - constructor; auto.
  - solve [constructor; auto].
  - constructor; auto.
    destruct (Nat.eqb_spec n x); subst; auto.
Qed.

(** In general, x can get captured and become not free if there is
    some bound variable l such that g l = x. The two preconditions
    here are sufficient to know that won't happen. *)
Lemma free_in_alpha_convert {A : Type} (g : nat -> nat) (t : tree A) (x : nat) :
  wf_tree' t ->
  (forall y, (y < g y)%nat) ->
  free_in x t <-> free_in x (alpha_convert g t).
Proof.
  intros Hwf Hlt; split.
  - induction t; intro Hfree; simpl; auto; inversion Hwf; subst.
    + inversion Hfree; subst; solve [constructor; auto].
    + inversion Hfree; subst.
      apply IHt in H1; auto.
      apply H3 in H6.
      destruct (Nat.eqb_spec x (g n)); subst.
      * specialize (Hlt n); lia.
      * constructor; auto.
        apply free_in_subst_l; auto.
  - induction t; intro Hfree; simpl in *; auto;
      inversion Hfree; subst; inversion Hwf; subst.
    + constructor; auto.
    + solve [constructor; auto].
    + destruct (Nat.eqb_spec x n); subst.
      * apply free_in_not_free_in' in H3; exfalso; apply H3.
        apply not_free_in_subst_l; auto.
      * constructor; auto.
        apply IHt; auto.
        apply free_in_subst_l' in H3; auto.
Qed.

Lemma not_free_fbind {A : Type} (t1 t2 : tree A) (l : nat) :
  not_free_in l t1 ->
  fbind l t1 t2 = t1.
Proof.
  induction t1; intro Hnotfree; simpl; auto.
  - destruct (Nat.eqb_spec l n); subst; auto.
    inversion Hnotfree; congruence.
  - inversion Hnotfree; subst.
    rewrite IHt1_1; auto; rewrite IHt1_2; auto.
  - inversion Hnotfree; subst.
    + rewrite Nat.eqb_refl; reflexivity.
    + destruct (Nat.eqb_spec n l); subst.
      * congruence.
      * rewrite IHt1; auto.
Qed.

Lemma not_free_tree_chain {A : Type} (t : tree A) (l n : nat) :
  not_free_in l t ->
  not_free_in l (tree_chain t l n).
Proof.
  induction n; simpl; auto; intro Hnotfree.
  rewrite not_free_fbind; auto.
Qed.

Lemma tree_chain_const {A : Type} (t : tree A) (l n : nat) :
  not_free_in l t -> tree_chain t l n = t.
Proof.
  induction n; simpl; auto.
  intro Hnotfree.
  rewrite not_free_fbind; auto.
  rewrite IHn; auto.
Qed.

(** If x is free in t, then x is free along the entire chain generated
    from t. When the generating label l doesn't appear in t, the chain
    is constant so the result is trivial. Otherwise it follows from
    relatively straightforward induction on t. *)
Lemma free_in_tree_chain {A : Type} (t : tree A) (l n x : nat) :
  wf_tree' t ->
  free_in x t -> free_in x (tree_chain t l n).
Proof.
  intro Hwf.
  destruct (free_in_dec l t) eqn:H0.
  - induction n; simpl; auto; intro H1.
    apply free_in_fbind; auto.
    apply free_in_alpha_convert; auto.
    intro y; lia.
  - intro Hfree.
    rewrite tree_chain_const; auto.
Qed.

Lemma all_labels_tree_chain_subset {A : Type} (t : tree A) (l n x : nat) :
  wf_tree' t ->
  In x (all_labels t) -> In x (all_labels (tree_chain t l n)).
Proof.
  intros Hwf Hin.
  apply all_labels_spec in Hin.
  apply label_in_bound_or_free in Hin.
  apply all_labels_spec.
  apply label_in_bound_or_free.
  destruct Hin as [Hbound|Hfree].
  - left; eapply bound_in_monotone; eauto; apply tree_leq_tree_chain.
  - right; apply free_in_tree_chain; auto.
Qed.

(** The other direction is true as long as renaming via g doesn't
    capture any free variables (forall m, bound_in m t -> not_free_in
    (g m) t). *)
Lemma not_free_in_alpha_convert {A : Type} (t : tree A) (g : nat -> nat) (l : nat) :
  not_free_in l t -> not_free_in l (alpha_convert g t).
Proof.
  induction t; intro Hnotfree; simpl; auto; inversion Hnotfree; subst.
  - constructor; auto.
  - destruct (Nat.eqb_spec n (g n)).
    + rewrite <- e; constructor.
    + constructor; auto.
      apply not_free_in_subst_l; auto.
  - destruct (Nat.eqb_spec l (g n)); subst.
    + constructor.
    + constructor; auto.
      apply free_in_not_free_in; intro HC.
      apply free_in_subst_l' in HC; auto.
      apply IHt in H3; apply free_in_not_free_in in H3.
      congruence.
Qed.

Lemma bound_in_fbind_or {A : Type} (t1 t2 : tree A) (l m : nat) :
  bound_in m (fbind l t1 t2) ->
  bound_in m t1 \/ bound_in m t2.
Proof.
  induction t1; simpl; intro Hbound.
  - left; auto.
  - destruct (Nat.eqb_spec l n); subst.
    + right; auto.
    + inversion Hbound.
  - inversion Hbound; subst.
    + apply IHt1_1 in H1; destruct H1.
      * left; constructor; auto.
      * right; auto.
    + apply IHt1_2 in H1; destruct H1.
      * left; solve [constructor; auto].
      * right; auto.
  - destruct (Nat.eqb_spec n l); subst.
    + left; auto.
    + inversion Hbound; subst.
      * left; constructor.
      * apply IHt1 in H3; destruct H3.
        ++ left; constructor; auto.
        ++ right; auto.
Qed.

(** If something is bound in the chain generated from t, then
    something must be bound in t. This is useful in conjunction with
    the following lemma [bound_in_tree_chain_lt]. *)
Lemma bound_in_tree_chain_exists {A : Type} (t : tree A) (l i m : nat) :
  bound_in m (tree_chain t l i) ->
  exists n, bound_in n t.
Proof.
  induction i; simpl; intro Hbound.
  - exists m; auto.
  - apply bound_in_fbind_or in Hbound.
    destruct Hbound as [Hbound|Hbound]; auto.
    apply bound_in_alpha_convert_exists in Hbound; firstorder.
Qed.

(** If m is bound in a chain generated from t, then either m is bound
    in t or it's strictly larger than anything bound in t. *)
Lemma bound_in_tree_chain_lt {A : Type} (t : tree A) (l m i : nat) :
  wf_tree' t ->
  bound_in m (tree_chain t l i) ->
  bound_in m t \/ (forall y, bound_in y t -> (y < m)%nat).
Proof.
  induction i; simpl; intros Hwf Hbound; auto.
  apply bound_in_fbind_or in Hbound; destruct Hbound as [Hbound|Hbound].
  apply IHi in Hbound; auto.
  right. intros y Hboundy.
  apply bound_in_alpha_convert_lt in Hbound.
  apply bound_in_label_in in Hboundy.
  apply all_labels_spec in Hboundy.
  apply list_max_spec in Hboundy.
  assert (Hle: (list_max (all_labels t) <=
                list_max (all_labels (tree_chain t l i)))%nat).
  { apply list_max_monotone; intro x;
      apply all_labels_tree_chain_subset; auto. }
  lia.
Qed.

Lemma free_in_bound_in_chain_lt {A : Type} (t : tree A) (i : nat) :
  wf_tree' t ->
  (forall n m, free_in n t -> bound_in m t -> (n < m)%nat) ->
  forall n m l, free_in n t -> bound_in m (tree_chain t l i) -> (n < m)%nat.
Proof.
  intros Hwf Hlt n m l Hfree Hbound; pose proof Hbound as Hbound'.
  apply bound_in_tree_chain_exists in Hbound; destruct Hbound as [o Hbound].
  apply bound_in_tree_chain_lt in Hbound'; destruct Hbound'; auto.
  specialize (H _ Hbound); transitivity o; auto.
Qed.

Lemma not_bound_in_alpha_convert_lt {A : Type} (t : tree A) (g : nat -> nat) (m : nat) :
  (forall x, (m < g x)%nat) ->
  not_bound_in m (alpha_convert g t).
Proof.
  induction t; intro Hlt; simpl; try solve [constructor; auto].
  - destruct (Nat.eqb_spec m (g n)); subst.
    + specialize (Hlt n); lia.
    + constructor; auto; apply not_bound_in_subst_l; auto.
Qed.

Lemma not_free_in_tree_chain {A : Type} (t : tree A) (l n : nat) :
  not_free_in l t ->
  tree_chain t l n = t.
Proof.
  induction n; simpl; auto; intro Hnotfree.
  rewrite IHn; auto.
  apply not_free_fbind; auto.
Qed.

(* Lemma in_bound_labels_fbind1 {A : Type} (t1 t2 : tree A) (l x : nat) : *)
(*   In x (bound_labels t1) -> *)
(*   In x (bound_labels (fbind l t1 t2)). *)
(* Proof. *)
(*   induction t1; intro Hin; simpl. *)
(*   - inversion Hin. *)
(*   - inversion Hin. *)
(*   - apply nodup_In. *)
(*     apply bound_labels_spec in Hin. *)
(*     apply in_or_app. *)
(*     inversion Hin; subst. *)
(*     + left; apply IHt1_1; apply bound_labels_spec; auto. *)
(*     + right; apply IHt1_2; apply bound_labels_spec; auto. *)
(*   - apply bound_labels_spec in Hin. *)
(*     inversion Hin; subst. *)
(*     + destruct (Nat.eqb_spec n l); subst. *)
(*       * destruct (in_dec Nat.eq_dec l (bound_labels t1)). *)
(*         ++ apply nodup_In; auto. *)
(*         ++ left; auto. *)
(*       * destruct (in_dec Nat.eq_dec n (bound_labels (fbind l t1 t2))). *)
(*         ++ apply nodup_In; auto. *)
(*         ++ left; auto. *)
(*     + destruct (Nat.eqb_spec n l); subst. *)
(*       * destruct (in_dec Nat.eq_dec l (bound_labels t1)). *)
(*         ++ apply nodup_In; auto; apply bound_labels_spec; auto. *)
(*         ++ right; apply nodup_In; apply bound_labels_spec; auto. *)
(*       * destruct (in_dec Nat.eq_dec n (bound_labels (fbind l t1 t2))). *)
(*         ++ apply nodup_In; apply IHt1; apply bound_labels_spec; auto. *)
(*         ++ right; apply nodup_In; apply IHt1; apply bound_labels_spec; auto. *)
(* Qed. *)

Lemma in_not_bound_choice1 {A : Type} (t1 t2 : tree A) (p : Q) (l : list nat) :
  (forall x : nat, In x l -> not_bound_in x (Choice p t1 t2)) ->
  forall x : nat, In x l -> not_bound_in x t1.
Proof.
  intros H x Hin. specialize (H x Hin); inversion H; subst; auto.
Qed.

Lemma in_not_bound_choice2 {A : Type} (t1 t2 : tree A) (p : Q) (l : list nat) :
  (forall x : nat, In x l -> not_bound_in x (Choice p t1 t2)) ->
  forall x : nat, In x l -> not_bound_in x t2.
Proof.
  intros H x Hin. specialize (H x Hin); inversion H; subst; auto.
Qed.

Lemma bound_in_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) (l : nat) :
  bound_in l t -> 
  bound_in l (tree_bind t k).
Proof.
  unfold tree_bind; induction t; simpl; intro Hbound;
    inversion Hbound; subst; try solve [constructor; auto].
Qed.

Lemma wf_tree_bind' {A B : Type} (t : tree A) (k : A -> tree B) :
  wf_tree (tree_bind t k) ->
  wf_tree t.
Proof.
  unfold tree_bind; induction t; simpl; intro Hwf;
    inversion Hwf; subst; try solve [constructor; auto].
  - constructor; auto.
    apply bound_in_not_bound_in; intro HC.
    apply bound_in_not_bound_in in H2; apply H2.
    apply bound_in_tree_bind; auto.
Qed.
