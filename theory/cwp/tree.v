(** Choice trees with fix (loop) nodes. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Arith.PeanoNat.
Require Import Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Structures.Monad.
Require Import Permutation.
Import ListNotations.

Require Import misc.
Require Import order.
Require Import Q.
  

(** Choice trees with fix (loop) nodes ("choice-fix trees"). *)
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

Instance Reflexive_tree_eq {A : Type} `{EqType A} : Reflexive (@tree_eq A).
Proof. intro t; induction t; constructor; auto; reflexivity. Qed.

Instance Symmetric_tree_eq {A : Type} `{EqType A} : Symmetric (@tree_eq A).
Proof. induction 1; constructor; auto; lra. Qed.

Lemma tree_eqb_refl {A : Type} `{EqType A} (t : tree A) :
  tree_eqb t t = true.
Proof.
  destruct (tree_eqb_spec t t); auto.
  exfalso; apply n; reflexivity.
Qed.

Lemma tree_eqb_symm {A : Type} `{EqType A} (t1 t2 : tree A) :
  tree_eqb t1 t2 = tree_eqb t2 t1.
Proof.
  destruct (tree_eqb_spec t1 t2); destruct (tree_eqb_spec t2 t1);
    auto; exfalso; apply n; symmetry; auto.
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

Definition tree_lt {A : Type} (t1 t2 : tree A) : Prop :=
  tree_leq t1 t2 /\ not (tree_eq t1 t2).

Definition tree_ltb {A : Type} `{EqType A} (t1 t2 : tree A) : bool :=
  tree_leqb t1 t2 && negb (tree_eqb t1 t2).

Lemma tree_ltb_spec {A : Type} `{EqType A} (t1 t2 : tree A)
  : reflect (tree_lt t1 t2) (tree_ltb t1 t2).
Proof.
  unfold tree_lt, tree_ltb.
  destruct (tree_leqb_spec t1 t2); destruct (tree_eqb_spec t1 t2);
    simpl; constructor;intuition.
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

Fixpoint free_inb {A : Type} (n : nat) (t : tree A) : bool :=
  match t with
  | Leaf _ => false
  | Fail _ m => n =? m
  | Choice _ t1 t2 => free_inb n t1 || free_inb n t2
  | Fix m t1 => negb (n =? m) && free_inb n t1
  end.

Lemma free_inb_spec {A : Type} (n : nat) (t : tree A)
  : reflect (free_in n t) (free_inb n t).
Proof.
  induction t; simpl.
  - constructor; intro HC; inversion HC.
  - destruct (Nat.eqb_spec n n0); subst; constructor.
    + constructor.
    + intro HC; inversion HC; subst; congruence.
  - destruct IHt1; destruct IHt2; simpl; constructor;
      try solve[constructor; auto];
      intro HC; inversion HC; subst; congruence.
  - destruct (Nat.eqb_spec n n0); subst; simpl.
    + constructor; intro HC; inversion HC; subst; congruence.
    + destruct IHt; constructor.
      * constructor; auto.
      * intro HC; inversion HC; subst; congruence.
Qed.

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
  { free_in n t } + { not_free_in n t }.
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

Instance Proper_bound_in {A : Type} `{EqType A}
  : Proper (eq ==> @tree_eq A ==> iff) bound_in.
Proof.
  intros n m ? t1 t2 Heq; subst.
  split; induction Heq; auto; intro Hbound;
    inversion Hbound; subst; solve [constructor; auto].
Qed.

Instance Proper_free_in {A : Type} `{EqType A}
  : Proper (eq ==> @tree_eq A ==> iff) free_in.
Proof.
  intros n m ? t1 t2 Heq; subst.
  split; induction Heq; auto; intro Hfree;
    inversion Hfree; subst; solve [constructor; auto].
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

Inductive wf_tree'' {A : Type} : tree A -> Prop :=
| wf_leaf'' : forall x, wf_tree'' (Leaf x)
| wf_fail'' : forall n, wf_tree'' (Fail _ n)
| wf_choice'' : forall p t1 t2,
    0 < p -> p < 1 ->
    wf_tree'' t1 -> wf_tree'' t2 ->
    wf_tree'' (Choice p t1 t2)
| wf_fix'' : forall n t,
    wf_tree'' t ->
    (* n is not bound by another fix inside t. *)
    not_bound_in n t ->
    wf_tree'' (Fix n t).

Lemma wf_tree'_wf_tree {A : Type} (t : tree A) :
  wf_tree' t -> wf_tree t.
Proof.
  induction t; simpl; intro Hwf; constructor; inversion Hwf; subst; auto.
  apply bound_in_not_bound_in; intro HC.
  apply H2 in HC; lia.
Qed.

Lemma wf_tree''_wf_tree {A : Type} (t : tree A) :
  wf_tree'' t -> wf_tree t.
Proof.
  induction t; simpl; intro Hwf; constructor; inversion Hwf; subst; auto; lra.
Qed.

Lemma wf_tree_inv_choice1 {A : Type} p (t1 t2 : tree A) :
  wf_tree (Choice p t1 t2) ->
  wf_tree t1.
Proof. intro Hwf; inversion Hwf; auto. Qed.

Lemma wf_tree_inv_choice2 {A : Type} p (t1 t2 : tree A) :
  wf_tree (Choice p t1 t2) ->
  wf_tree t2.
Proof. intro Hwf; inversion Hwf; auto. Qed.

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

(** A structural property of a tree that underapproximates the
    semantic property of nondivergence (it's a bit stronger than
    necessary). *)
Inductive nondivergent {A : Type} : tree A -> Prop :=
| nondivergent_leaf : forall x, nondivergent (Leaf x)
| nondivergent_choice1 : forall p t1 t2,
    p == 0 ->
    nondivergent t2 ->
    nondivergent (Choice p t1 t2)
| nondivergent_choice2 : forall p t1 t2,
    p == 1 ->
    nondivergent t1 ->
    nondivergent (Choice p t1 t2)
| nondivergent_choice3 : forall p t1 t2,
    0 < p -> p < 1 ->
    nondivergent t1 \/ nondivergent t2 ->
    nondivergent (Choice p t1 t2)
| nondivergent_fix : forall n t,
    nondivergent t ->
    nondivergent (Fix n t).

Lemma Qle_bool_false (a b : Q)  :
  Qle_bool a b = false <-> b < a.
Proof.
  split; intro H.
  - destruct (Qlt_le_dec b a); try lra.
    apply Qle_bool_iff in q; congruence.
  - destruct (Qle_bool a b) eqn:Hq; auto.
    apply Qle_bool_iff in Hq; lra.
Qed.

Inductive in_tree {A : Type} : A -> tree A -> Prop :=
| in_tree_leaf : forall x, in_tree x (Leaf x)
| in_tree_choice1 : forall x p t1 t2,
    in_tree x t1 ->
    in_tree x (Choice p t1 t2)
| in_tree_choice2 : forall x p t1 t2,
    in_tree x t2 ->
    in_tree x (Choice p t1 t2)
| in_tree_fix : forall x n t,
    in_tree x t ->
    in_tree x (Fix n t).

Fixpoint in_treeb {A : Type} `{EqType A} (x : A) (t : tree A) : bool :=
  match t with
  | Leaf y => eqb x y
  | Fail _ _ => false
  | Choice _ t1 t2 => in_treeb x t1 || in_treeb x t1
  | Fix _ t1 => in_treeb x t1
  end.

Inductive leaf_reachable {A : Type} : tree A -> Prop :=
| leaf_reachable_leaf : forall x, leaf_reachable (Leaf x)
| leaf_reachable_choice1 : forall p t1 t2,
    p == 0 ->
    leaf_reachable t2 ->
    leaf_reachable (Choice p t1 t2)
| leaf_reachable_choice2 : forall p t1 t2,
    p == 1 ->
    leaf_reachable t1 ->
    leaf_reachable (Choice p t1 t2)
| leaf_reachable_choice3 : forall p t1 t2,
    ~ p == 0 -> ~ p == 1 ->
    (leaf_reachable t1 \/ leaf_reachable t2) ->
    leaf_reachable (Choice p t1 t2)
| leaf_reachable_fix : forall n t,
    leaf_reachable t ->
    leaf_reachable (Fix n t).

Inductive leaf_reachable' {A : Type} : tree A -> Prop :=
| leaf_reachable'_leaf : forall x, leaf_reachable' (Leaf x)
| leaf_reachable'_choice1 : forall p t1 t2,
    leaf_reachable' t1 ->
    leaf_reachable' (Choice p t1 t2)
| leaf_reachable'_choice2 : forall p t1 t2,
    leaf_reachable' t2 ->
    leaf_reachable' (Choice p t1 t2)
| leaf_reachable'_fix : forall n t,
    leaf_reachable' t ->
    leaf_reachable' (Fix n t).

Lemma leaf_reachable_leaf_reachable' {A : Type} (t : tree A) :
  leaf_reachable t -> leaf_reachable' t.
Proof.
  induction t; simpl; intro H.
  - constructor.
  - inversion H.
  - inversion H; subst.
    + solve [constructor; auto].
    + solve [constructor; auto].
    + destruct H5; solve [constructor; auto].
  - inversion H; subst; constructor; auto.
Qed.

Inductive no_leaf_reachable {A : Type} : tree A -> Prop :=
| no_leaf_reachable_fail : forall n, no_leaf_reachable (Fail _ n)
| no_leaf_reachable_choice1 : forall p t1 t2,
    p == 0 ->
    no_leaf_reachable t2 ->
    no_leaf_reachable (Choice p t1 t2)
| no_leaf_reachable_choice2 : forall p t1 t2,
    p == 1 ->
    no_leaf_reachable t1 ->
    no_leaf_reachable (Choice p t1 t2)
| no_leaf_reachable_choice3 : forall p t1 t2,
    ~ p == 0 -> ~ p == 1 ->
    no_leaf_reachable t1 ->
    no_leaf_reachable t2 ->
    no_leaf_reachable (Choice p t1 t2)
| no_leaf_reachable_fix : forall n t,
    no_leaf_reachable t ->
    no_leaf_reachable (Fix n t).

Fixpoint leaf_reachableb {A : Type} (t : tree A) : bool :=
  match t with
  | Leaf _ => true
  | Fail _ _ => false
  | Choice p t1 t2 => if Qeq_bool p 0 then
                       leaf_reachableb t2 else
                       if Qeq_bool p 1 then
                         leaf_reachableb t1 else
                         leaf_reachableb t1 || leaf_reachableb t2
  | Fix _ t1 => leaf_reachableb t1
  end.

Lemma leaf_reachableb_spec {A : Type} (t : tree A)
  : reflect (leaf_reachable t) (leaf_reachableb t).
Proof.
  induction t; simpl.
  - repeat constructor.
  - constructor; intro HC; inversion HC.
  - destruct (Qeq_bool q 0) eqn:Hq0; simpl.
    + apply Qeq_bool_eq in Hq0.
      destruct IHt2 as [H | H]; constructor.
      * apply leaf_reachable_choice1; auto.
      * intro HC; inversion HC; subst; try congruence; lra.
    + apply Qeq_bool_neq in Hq0.
      destruct (Qeq_bool q 1) eqn:Hq1; simpl.
      * apply Qeq_bool_eq in Hq1.
        destruct IHt1 as [H | H]; constructor.
        -- apply leaf_reachable_choice2; auto.
        -- intro HC; inversion HC; subst; try congruence; lra.
      * apply Qeq_bool_neq in Hq1.
        destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2]; simpl; constructor.
        -- apply leaf_reachable_choice3; auto.
        -- apply leaf_reachable_choice3; auto.
        -- apply leaf_reachable_choice3; auto.
        -- intro HC; inversion HC; subst; try congruence.
           destruct H6; congruence.
  - destruct IHt as [H | H]; constructor.
    + constructor; auto.
    + intro HC; inversion HC; congruence.
Qed.

Lemma not_leaf_reachable_no_leaf_reachable {A : Type} (t : tree A) :
  ~ leaf_reachable t <-> no_leaf_reachable t.
Proof.
  split; induction t; simpl; intro H0.
  - exfalso; apply H0; constructor.
  - constructor.
  - destruct (Qeq_bool q 0) eqn:Hq0.
    + apply Qeq_bool_eq in Hq0; constructor; auto.
      apply IHt2; intro HC; apply H0; constructor; auto.
    + apply Qeq_bool_neq in Hq0.
      destruct (Qeq_bool q 1) eqn:Hq1.
      * apply Qeq_bool_eq in Hq1; apply no_leaf_reachable_choice2; auto.
        apply IHt1; intro HC; apply H0; solve [constructor; auto].
      * apply Qeq_bool_neq in Hq1.
        apply no_leaf_reachable_choice3; auto.
        -- apply IHt1; intro HC; apply H0; solve [constructor; auto].
        -- apply IHt2; intro HC; apply H0; solve [constructor; auto].
  - constructor; apply IHt; intro HC; apply H0; constructor; auto.
  - inversion H0.
  - intro HC; inversion HC.
  - inversion H0; intro HC; inversion HC; subst; try lra.
    + apply IHt2; auto.
    + apply IHt1; auto.
    + destruct H12.
      * apply IHt1; auto.
      * apply IHt2; auto.
  - inversion H0; intro HC; inversion HC; subst; apply IHt; auto.
Qed.

Lemma leaf_reachable_dec {A : Type} (t : tree A)
  : {leaf_reachable t} + {no_leaf_reachable t}.
Proof.
  destruct (leaf_reachableb_spec t); auto.
  right; apply not_leaf_reachable_no_leaf_reachable; auto.
Qed.

Inductive fail_reachable {A : Type} (lbl : nat) : tree A -> Prop :=
| fail_reachable_fail : fail_reachable lbl (Fail _ lbl)
| fail_reachable_choice : forall p t1 t2,
    (fail_reachable lbl t1 \/ fail_reachable lbl t2) ->
    fail_reachable lbl (Choice p t1 t2)
| fail_reachable_fix : forall n t,
    fail_reachable lbl t ->
    fail_reachable lbl (Fix n t).

Inductive fail_reachable' {A : Type} (lbl : nat) : tree A -> Prop :=
| fail_reachable'_fail : fail_reachable' lbl (Fail _ lbl)
| fail_reachable'_choice1 : forall p t1 t2,
    fail_reachable' lbl t1 ->
    fail_reachable' lbl (Choice p t1 t2)
| fail_reachable'_choice2 : forall p t1 t2,
    fail_reachable' lbl t2 ->
    fail_reachable' lbl (Choice p t1 t2)
| fail_reachable'_fix : forall n t,
    fail_reachable' lbl t ->
    fail_reachable' lbl (Fix n t).

Lemma fail_reachable_fail_reachable' {A : Type} (lbl : nat) (t : tree A) :
  fail_reachable lbl t ->
  fail_reachable' lbl t.
Proof.
  induction t; simpl; intro H; inversion H; subst; try solve[constructor; auto].
  destruct H1; solve[constructor; auto].
Qed.

Inductive fail_not_reachable {A : Type} (lbl : nat) : tree A -> Prop :=
| fail_not_reachable_leaf : forall x, fail_not_reachable lbl (Leaf x)
| fail_not_reachable_fail : forall n, n <> lbl -> fail_not_reachable lbl (Fail _ n)
| fail_not_reachable_choice : forall p t1 t2,
    fail_not_reachable lbl t1 ->
    fail_not_reachable lbl t2 ->
    fail_not_reachable lbl (Choice p t1 t2)
| fail_not_reachable_fix : forall n t,
    fail_not_reachable lbl t ->
    fail_not_reachable lbl (Fix n t).

Fixpoint fail_reachableb {A : Type} (lbl : nat) (t : tree A) : bool :=
  match t with
  | Leaf _ => false
  | Fail _ n => n =? lbl
  | Choice p t1 t2 => fail_reachableb lbl t1 || fail_reachableb lbl t2
  | Fix _ t1 => fail_reachableb lbl t1
  end.

Lemma fail_reachableb_spec {A : Type} (lbl : nat) (t : tree A)
  : reflect (fail_reachable lbl t) (fail_reachableb lbl t).
Proof.
  induction t; simpl.
  - constructor; intro HC; inversion HC.
  - destruct (Nat.eqb_spec n lbl); subst; constructor.
    + constructor.
    + intro HC; inversion HC; subst; congruence.
  - destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2]; simpl; constructor.
    + apply fail_reachable_choice; auto.
    + apply fail_reachable_choice; auto.
    + apply fail_reachable_choice; auto.
    + intro HC; inversion HC; subst; try congruence.
      destruct H0; congruence.
  - destruct IHt as [H | H]; constructor.
    + constructor; auto.
    + intro HC; inversion HC; congruence.
Qed.

Lemma not_fail_reachable_fail_not_reachable {A : Type} (lbl : nat) (t : tree A) :
  ~ fail_reachable lbl t <-> fail_not_reachable lbl t.
Proof.
  split; induction t; simpl; intro H0.
  - constructor.
  - destruct (Nat.eqb_spec lbl n); subst.
    + exfalso; apply H0; constructor.
    + constructor; auto.
  - apply fail_not_reachable_choice; auto.
    + apply IHt1; intro HC; apply H0; solve [constructor; auto].
    + apply IHt2; intro HC; apply H0; solve [constructor; auto].
  - constructor; apply IHt; intro HC; apply H0; constructor; auto.
  - intro HC; inversion HC.
  - destruct (Nat.eqb_spec lbl n); subst.
    + inversion H0; congruence.
    + intro HC; inversion HC; congruence.
  - inversion H0; intro HC; inversion HC; subst; try lra.
    destruct H6.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - inversion H0; intro HC; inversion HC; subst; apply IHt; auto.
Qed.

Lemma fail_reachable_dec {A : Type} (lbl : nat) (t : tree A)
  : {fail_reachable lbl t} + {fail_not_reachable lbl t}.
Proof.
  destruct (fail_reachableb_spec lbl t); auto.
  right; apply not_fail_reachable_fail_not_reachable; auto.
Qed.

Lemma free_in'_fail_not_reachable {A : Type} (lbl : nat) (t : tree A) :
  free_in lbl t -> fail_reachable lbl t.
Proof.
  induction t; simpl; intro H0; inversion H0; subst.
  - constructor.
  - constructor; auto.
  - solve [constructor; auto].
  - constructor; auto.
Qed.

(* Assumes wf_tree'' (p is strictly between 0 and 1 at all choices). *)
Inductive nondivergent' {A : Type} : list nat -> tree A -> Prop :=
| nondivergent'_leaf : forall ls x, nondivergent' ls (Leaf x)
| nondivergent'_fail : forall ls n, In n ls -> nondivergent' ls (Fail _ n)
| nondivergent'_choice : forall ls p t1 t2,
    nondivergent' ls t1 ->
    nondivergent' ls t2 ->
    nondivergent' ls (Choice p t1 t2)
| nondivergent'_fix : forall ls n t,
    (leaf_reachable t \/ exists m, In m ls /\ fail_reachable m t) ->
    nondivergent' (n :: ls) t ->
    nondivergent' ls (Fix n t).

Definition nondivergent'' {A : Type} (n : nat) (t : tree A) : Prop :=
  nondivergent' [] (Fix n t).

Inductive divergent {A : Type} : list nat -> tree A -> Prop :=
| divergent_fail : forall ls n, ~ In n ls -> divergent ls (Fail _ n)
| divergent_choice : forall ls p t1 t2,
    (divergent ls t1 \/ divergent ls t2) ->
    divergent ls (Choice p t1 t2)
| divergent_fix : forall ls n t,
    (no_leaf_reachable t /\ forall m, In m ls -> fail_not_reachable m t) \/
    divergent (n :: ls) t ->
    divergent ls (Fix n t).

Definition divergent' {A : Type} (n : nat) (t : tree A) : Prop :=
  divergent [] (Fix n t).

Fixpoint nondivergentb {A : Type} (ls : list nat) (t : tree A) : bool :=
  match t with
  | Leaf _ => true
  | Fail _ n => existsb (Nat.eqb n) ls
  | Choice p t1 t2 => nondivergentb ls t1 && nondivergentb ls t2
  | Fix n t1 => (leaf_reachableb t1 ||
                existsb (fun l => fail_reachableb l t1) ls) &&
               nondivergentb (n :: ls) t1
  end.

Lemma nondivergentb_spec {A : Type} (ls : list nat) (t : tree A) :
  reflect (nondivergent' ls t) (nondivergentb ls t).
Proof.
  revert ls.
  induction t; intro ls; simpl.
  - repeat constructor.
  - destruct (existsb (Nat.eqb n) ls) eqn:Hexists; constructor.
    + constructor; apply existsb_in; auto.
    + intros HC; inversion HC; subst.
      apply existsb_not_in in Hexists; contradiction.
  - destruct (IHt1 ls) as [H1 | H1];
      destruct (IHt2 ls) as [H2 | H2]; simpl; constructor.
    + apply nondivergent'_choice; auto.
    + intro HC; inversion HC; subst; congruence; lra.
    + intro HC; inversion HC; subst; congruence; lra.
    + intro HC; inversion HC; subst; congruence; lra.
  - destruct (leaf_reachableb_spec t); subst; simpl.
    + destruct (IHt (n :: ls)) as [H | H]; simpl; constructor.
      * constructor; auto.
      * intro HC; inversion HC; subst.
        destruct H3 as [Hleaf | [m [Hin Hfail]]]; congruence.
    + destruct (existsb (fun l => fail_reachableb l t) ls) eqn:Hexists; simpl.
      * destruct (IHt (n :: ls)) as [H | H]; simpl; constructor.
        -- constructor; auto.
           right.
           apply existsb_exists in Hexists.
           destruct Hexists as [m [Hin Hfail]].
           exists m; split; auto.
           destruct (fail_reachableb_spec m t); subst; auto; congruence.
        -- intro HC; inversion HC; subst.
           destruct H3 as [Hleaf | [m [Hin Hfail]]]; congruence.
      * constructor.
        intros HC; inversion HC; subst.
        destruct H2 as [Hleaf | [m [Hin Hfail]]].
        -- congruence.
        -- eapply existsb_false_forall in Hexists; eauto.
           destruct (fail_reachableb_spec m t); subst; congruence.
Qed.

Lemma not_nondivergent'_divergent {A : Type} (ls : list nat) (t : tree A) :
  ~ nondivergent' ls t <-> divergent ls t.
Proof.
  split; revert ls; induction t; simpl; intros ls H0.
  - exfalso; apply H0; constructor.
  - destruct (existsb (Nat.eqb n) ls) eqn:Hexists.
    + apply existsb_in in Hexists.
      exfalso; apply H0; constructor; auto.
    + apply existsb_not_in in Hexists.
      constructor; auto.
  - apply divergent_choice; auto.
    destruct (nondivergentb_spec ls t1).
    + destruct (nondivergentb_spec ls t2).
      * exfalso; apply H0; apply nondivergent'_choice; auto.
      * right; apply IHt2; auto.
    + left; apply IHt1; auto.
  - constructor.
    + destruct (nondivergentb_spec (n :: ls) t).
      * left.
        destruct (leaf_reachableb_spec t).
        -- exfalso; apply H0; constructor; auto.
        -- destruct (existsb (fun l => fail_reachableb l t) ls) eqn:Hexists.
           ++ apply existsb_exists in Hexists.
              destruct Hexists as [m [Hin Hfail]].
              destruct (fail_reachableb_spec m t); try congruence.
              exfalso; apply H0; constructor; auto.
              right; exists m; auto.
           ++ split.
              ** apply not_leaf_reachable_no_leaf_reachable; auto.
              ** intros m Hin.
                 eapply existsb_false_forall in Hexists; eauto.
                 destruct (fail_reachableb_spec m t); try congruence.
                 apply not_fail_reachable_fail_not_reachable; auto.
      * right; apply IHt; auto.
  - inversion H0.
  - destruct (existsb (Nat.eqb n) ls) eqn:Hexists.
    + apply existsb_in in Hexists.
      inversion H0; congruence.
    + apply existsb_not_in in Hexists.
      intro HC; inversion HC; congruence.
  - inversion H0; intro HC; inversion HC; try congruence; try lra; subst.
    + destruct H2 as [H | H].
      * eapply IHt1; eauto.
      * eapply IHt2; eauto.
  - inversion H0; intro HC; inversion HC; subst.
    destruct H2 as [[Hnoleaf Hnofail] | Hdiv].
    + destruct H7 as [Hleaf | [m [Hin Hfail]]].
      * apply not_leaf_reachable_no_leaf_reachable in Hnoleaf; congruence.
      * apply Hnofail in Hin.
        apply not_fail_reachable_fail_not_reachable in Hin; congruence.
    + eapply IHt; eauto.
Qed.

Lemma nondivergent'_dec {A : Type} (ls : list nat) (t : tree A) :
  {nondivergent' ls t} + {divergent ls t}.
Proof.
  destruct (nondivergentb_spec ls t); auto.
  right; apply not_nondivergent'_divergent; auto.
Qed.

Lemma nondivergent''_dec {A : Type} (n : nat) (t : tree A) :
  {nondivergent'' n t} + {divergent' n t}.
Proof. apply nondivergent'_dec. Qed.

Inductive unbiased {A : Type} : tree A -> Prop :=
| unbiased_leaf : forall x, unbiased (Leaf x)
| unbiased_fail : forall n, unbiased (Fail _ n)
| unbiased_choice : forall p t1 t2,
    p == (1#2) ->
    unbiased t1 -> unbiased t2 ->
    unbiased (Choice p t1 t2)
| unbiased_fix : forall n t,
    unbiased t ->
    unbiased (Fix n t).

Lemma unbiased_in_tree_leaf_reachable {A : Type} (t : tree A) (x : A) :
  in_tree x t ->
  unbiased t ->
  leaf_reachable t.
Proof.
  induction 1; intro Hub; inversion Hub; subst;
    solve[constructor; try lra; auto].
Qed.

Inductive no_fix {A : Type} : tree A -> Prop :=
| no_fix_leaf : forall x, no_fix (Leaf x)
| no_fix_fail : forall lbl, no_fix (Fail _ lbl)
| no_fix_choice : forall p t1 t2,
    no_fix t1 ->
    no_fix t2 ->
    no_fix (Choice p t1 t2).

Inductive no_nested_fix {A : Type} : tree A -> Prop :=
| no_nested_fix_leaf : forall x, no_nested_fix (Leaf x)
| no_nested_fix_fail : forall lbl, no_nested_fix (Fail _ lbl)
| no_nested_fix_choice : forall p t1 t2,
    no_nested_fix t1 ->
    no_nested_fix t2 ->
    no_nested_fix (Choice p t1 t2)
| no_nested_fix_fix : forall lbl t,
    no_fix t ->
    no_nested_fix (Fix lbl t).

Inductive has_fail {A : Type} : tree A -> Prop :=
| has_fail_fail : forall n, has_fail (Fail _ n)
| has_fail_choice1 : forall p t1 t2,
    has_fail t1 ->
    has_fail (Choice p t1 t2)
| has_fail_choice2 : forall p t1 t2,
    has_fail t2 ->
    has_fail (Choice p t1 t2)
| has_fail_fix : forall n t,
    has_fail t ->
    has_fail (Fix n t).

Inductive all_fail {A : Type} : tree A -> Prop :=
| all_fail_fail : forall lbl, all_fail (Fail _ lbl)
| all_fail_choice : forall p t1 t2,
    all_fail t1 ->
    all_fail t2 ->
    all_fail (Choice p t1 t2)
| all_fail_fix : forall m t,
    all_fail t ->
    all_fail (Fix m t).

Inductive only_fail {A : Type} : nat -> tree A -> Prop :=
| only_fail_leaf : forall lbl x, only_fail lbl (Leaf x)
| only_fail_fail : forall lbl, only_fail lbl (Fail _ lbl)
| only_fail_choice : forall lbl p t1 t2,
    only_fail lbl t1 ->
    only_fail lbl t2 ->
    only_fail lbl (Choice p t1 t2)
| only_fail_fix : forall lbl m t,
    only_fail lbl t ->
    only_fail lbl (Fix m t).

Inductive no_fail {A : Type} : tree A -> Prop :=
| no_fail_leaf : forall x, no_fail (Leaf x)
| no_fail_choice : forall p t1 t2,
    no_fail t1 ->
    no_fail t2 ->
    no_fail (Choice p t1 t2)
| no_fail_fix : forall n t,
    no_fail t ->
    no_fail (Fix n t).

Inductive has_fix {A : Type} : tree A -> Prop :=
| has_fix_choice1 : forall p t1 t2,
    p == 0 ->
    has_fix t2 ->
    has_fix (Choice p t1 t2)
| has_fix_choice2 : forall p t1 t2,
    p == 1 ->
    has_fix t1 ->
    has_fix (Choice p t1 t2)
| has_fix_choice3 : forall p t1 t2,
    ~ p == 0 -> ~ p == 1 ->
    has_fix t1 ->
    has_fix t2 ->
    has_fix (Choice p t1 t2)
| has_fix_fix : forall n t,
    has_fix (Fix n t).

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

Lemma countb_list_app {A : Type} (f : A -> bool) (l1 l2 : list A) :
  countb_list f (l1 ++ l2) = (countb_list f l1 + countb_list f l2)%nat.
Proof. induction l1; auto; simpl; rewrite IHl1; lia. Qed.

Lemma count_true_n (n : nat) :
  countb_list id (repeat true n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma count_false_0 (n : nat) :
  countb_list id (repeat false n) = O.
Proof. induction n; simpl; auto. Qed.

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

Lemma terminals_lt_choice {A : Type} (p : Q) (t1 t2 : tree A) :
  (terminals t1 < terminals (Choice p t1 t2))%nat.
Proof. generalize (terminals_nonzero t2); simpl; lia. Qed.

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

Lemma fmap_congruent' {A B : Type} (f : A -> B) (t : tree A) :
  congruent' t (fmap f t).
Proof. induction t; constructor; auto. Qed.

Lemma heightb_fmap {A B : Type} (f : A -> B) (t : tree A) :
  heightb (fmap f t) = heightb t.
Proof. induction t; simpl; auto. Qed.

Lemma congruent'_no_fail {A B : Type} (t1 : tree A) (t2 : tree B) :
  no_fail t1 ->
  congruent' t1 t2 ->
  no_fail t2.
Proof.
  intro Hnf. induction 1; simpl; inversion Hnf; subst; constructor; auto.
Qed.

Lemma fmap_terminals {A B : Type} (t : tree A) (f : A -> B) :
  terminals (fmap f t) = terminals t.
Proof. induction t; simpl; lia. Qed.

Lemma no_fix_no_nested_fix {A : Type} (t : tree A) :
  no_fix t ->
  no_nested_fix t.
Proof. induction 1; constructor; auto. Qed.

Lemma in_tree_tree_eq {A : Type} `{EqType A} (x : A) (t1 t2 : tree A) :
  tree_eq t1 t2 ->
  in_tree x t1 ->
  in_tree x t2.
Proof.
  induction 1; intro Heq; auto;
    inversion Heq; subst; solve [constructor; auto].
Qed.

Lemma not_in_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) (lbl : nat) :
  not_in lbl t ->
  (forall x, not_in lbl (k x)) ->
  not_in lbl (tree_bind t k).
Proof.
  unfold tree_bind; induction t; simpl; intros Ht Hk; auto;
    inversion Ht; subst; constructor; auto.
Qed.

Lemma unbiased_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) :
  unbiased t ->
  (forall x, unbiased (k x)) ->
  unbiased (tree_bind t k).
Proof.
  unfold tree_bind; induction t; simpl; intros Ht Hk;
    auto; inversion Ht; subst; constructor; auto.
Qed.

Lemma fold_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) :
  join (fmap k t) = tree_bind t k.
Proof. reflexivity. Qed.

Inductive all_p {A : Type} : (Q -> Prop) -> tree A -> Prop :=
| all_p_leaf : forall P x, all_p P (Leaf x)
| all_p_fail : forall P n, all_p P (Fail _ n)
| all_p_choice : forall (P : Q -> Prop) q t1 t2,
    P q -> all_p P t1 -> all_p P t2 -> all_p P (Choice q t1 t2)
| all_p_fix : forall P n t1, all_p P t1 -> all_p P (Fix n t1).

Inductive some_p {A : Type} : (Q -> Prop) -> tree A -> Prop :=
| some_p_choice_l : forall P q t1 t2, ~ P q -> some_p P t1 -> some_p P (Choice q t1 t2)
| some_p_choice_r : forall P q t1 t2, ~ P q -> some_p P t2 -> some_p P (Choice q t1 t2)
| some_p_choice_p : forall (P : Q -> Prop) q t1 t2, P q -> some_p P (Choice q t1 t2)
| some_p_fix : forall P n t1, some_p P t1 -> some_p P (Fix n t1).

Definition p_in {A : Type} (p : Q) (t : tree A) : Prop := some_p (fun q => q = p) t.

Definition path : Type := list bool.

Fixpoint path_subtree {A} (p : path) (t : tree A) : tree A :=
  match (p, t) with
  | (false :: p', Choice _ l _) => path_subtree p' l
  | (true :: p', Choice _ _ r) => path_subtree p' r
  | (_, Fix _ t') => path_subtree p t'
  | _ => t
  end.

(* Definition upd {A} (f : nat -> option (tree A)) (m : nat) (t : tree A) (n : nat) : option (tree A) := *)
(*   if n =? m then Some t else f n. *)

(* Fixpoint sample_tree {A} (t : tree A) (f : nat -> option (tree A)) (bs : list bool) (n : nat) *)
(*   : option A := *)
(*   match n with *)
(*   | O => None *)
(*   | S n' => match t with *)
(*            | Leaf x => Some x *)
(*            | Fail _ m => match f m with *)
(*                         | Some t' => sample_tree t' f bs n' *)
(*                         | None => None *)
(*                         end *)
(*            | Choice p l r => match bs with *)
(*                             | nil => None *)
(*                             | false :: bs' => sample_tree l f bs' n' *)
(*                             | true :: bs' => sample_tree r f bs' n' *)
(*                             end *)
(*            | Fix m t' => sample_tree t' (upd f m t') bs n' *)
(*            end *)
(*   end. *)

(* Lemma divergent_subtree {A} (t : tree A) (lbl : nat) : *)
(*   divergent' lbl t -> *)
(*   exists p t', t' = path_subtree p t /\ *)
(*           wf_tree t' /\ *)
(*           no_leaf_reachable t' /\ *)
(*           (forall m, not_free_in m t). *)
(* Proof. *)
(*   intro Hdiv. *)
(*   unfold divergent' in Hdiv. *)
(*   inversion Hdiv; subst. *)
          
