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
Require Import ExtLib.Structures.Monoid.
Require Import Permutation.
Import ListNotations.

(* From Equations Require Import Equations. *)

Require Import axioms.
Require Import borel.
Require Import measure.
Require Import misc.
Require Import order.
Require Import Q.

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

(* Instance Transitive_tree_eq {A : Type} `{EqType A} : Transitive (@tree_eq A). *)

Lemma tree_eqb_refl {A : Type} `{EqType A} (t : tree A) :
  tree_eqb t t = true.
Proof.
  destruct (tree_eqb_spec t t); auto.
  exfalso; apply n; reflexivity.
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

(* Inductive all_support {A : Type} (pred : A -> Prop) : tree A -> Prop := *)
(* | all_support_leaf : forall x, pred x -> all_support pred (Leaf x) *)
(* | all_support_fail : forall n, all_support pred (Fail _ n) *)
(* | all_support_choice1 : forall p t1 t2, *)
(*     p == 0 -> *)
(*     all_support pred t2 -> *)
(*     all_support pred (Choice p t1 t2) *)
(* | all_support_choice2 : forall p t1 t2, *)
(*     p == 1 -> *)
(*     all_support pred t1 -> *)
(*     all_support pred (Choice p t1 t2) *)
(* | all_support_choice3 : forall p t1 t2, *)
(*     0 < p -> p < 1 -> *)
(*     all_support pred t1 -> *)
(*     all_support pred t2 -> *)
(*     all_support pred (Choice p t1 t2) *)
(* | all_support_fix : forall l t, *)
(*     all_support pred t -> *)
(*     all_support pred (Fix l t). *)

(* Fixpoint all_supportb {A : Type} (f : A -> bool) (t : tree A) : bool := *)
(*   match t with *)
(*   | Leaf x => f x *)
(*   | Fail _ _ => true *)
(*   | Choice p t1 t2 => *)
(*     if Qeq_bool p 0 *)
(*     then all_supportb f t2 *)
(*     else if Qeq_bool p 1 *)
(*          then all_supportb f t1 *)
(*          else all_supportb f t1 && all_supportb f t2 *)
(*   | Fix n t1 => all_supportb f t1 *)
(*   end. *)

Lemma wf_tree_inv_choice1 {A : Type} p (t1 t2 : tree A) :
  wf_tree (Choice p t1 t2) ->
  wf_tree t1.
Proof. intro Hwf; inversion Hwf; auto. Qed.

Lemma wf_tree_inv_choice2 {A : Type} p (t1 t2 : tree A) :
  wf_tree (Choice p t1 t2) ->
  wf_tree t2.
Proof. intro Hwf; inversion Hwf; auto. Qed.

(* Lemma all_supportb_spec {A : Type} (f : A -> bool) (t : tree A) : *)
(*   wf_tree t -> *)
(*   reflect (all_support (fun x => f x = true) t) (all_supportb f t). *)
(* Proof. *)
(*   induction t; intro Hwf; simpl. *)
(*   - destruct (f a) eqn:Hf; constructor. *)
(*     + constructor; auto. *)
(*     + intro HC; inversion HC; subst; congruence. *)
(*   - repeat constructor. *)
(*   - destruct (Qeq_dec q 0). *)
(*     + rewrite Qeq_eq_bool; auto. *)
(*       destruct IHt2. *)
(*       * eapply wf_tree_inv_choice2; eauto. *)
(*       * repeat constructor; auto. *)
(*       * constructor; intro HC; inversion HC; subst; try congruence; lra. *)
(*     + rewrite Qeq_bool_false; auto. *)
(*       destruct (Qeq_dec q 1). *)
(*       * rewrite Qeq_eq_bool; auto. *)
(*         destruct IHt1. *)
(*         ++ eapply wf_tree_inv_choice1; eauto. *)
(*         ++ constructor; apply all_support_choice2; auto. *)
(*         ++ constructor; intro HC; inversion HC; subst; congruence; try lra. *)
(*       * rewrite Qeq_bool_false; auto. *)
(*         destruct IHt1, IHt2; simpl; *)
(*           try solve [eapply wf_tree_inv_choice1; eauto]; *)
(*           try solve [eapply wf_tree_inv_choice2; eauto]; constructor. *)
(*         ++ inversion Hwf; subst. *)
(*            apply all_support_choice3; auto; lra. *)
(*         ++ intro HC; inversion HC; subst; congruence. *)
(*         ++ intro HC; inversion HC; subst; congruence. *)
(*         ++ intro HC; inversion HC; subst; congruence. *)
(*   - destruct IHt. *)
(*     + inversion Hwf; auto. *)
(*     + repeat constructor; auto. *)
(*     + constructor. intro HC; inversion HC; congruence. *)
(* Qed. *)

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

(* Inductive nondivergent' {A : Type} : list nat -> tree A -> Prop := *)
(* | nondivergent'_leaf : forall l x, nondivergent' l (Leaf x) *)
(* | nondivergent'_fail : forall l n, In n l -> nondivergent' l (Fail _ n) *)
(* | nondivergent'_choice1 : forall l p t1 t2, *)
(*     p == 0 -> *)
(*     nondivergent' l t2 -> *)
(*     nondivergent' l (Choice p t1 t2) *)
(* | nondivergent'_choice2 : forall l p t1 t2, *)
(*     p == 1 -> *)
(*     nondivergent' l t1 -> *)
(*     nondivergent' l (Choice p t1 t2) *)
(* | nondivergent'_choice3 : forall l p t1 t2, *)
(*     0 < p -> p < 1 -> *)
(*     nondivergent' l t1 -> nondivergent' l t2 -> *)
(*     nondivergent' l (Choice p t1 t2) *)
(* | nondivergent'_fix : forall l n t x, *)
(*     nondivergent' (n :: l) t -> *)
(*     in_tree x t -> *)
(*     nondivergent' l (Fix n t). *)

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


(** Tree preimage. *)

Definition singleton_seq {A : Type} (x : A) (i : nat) : option A :=
  match i with
  | O => Some x
  | _ => None
  end.

(** Interleave two infinite sequences together. *)
Definition seq_union {A : Type} (f g : nat -> A) (i : nat) : A :=
  match modulo i 2 with
  | O => f (div i 2)
  | _ => g (div i 2)%nat
  end.

(** seq_union is correct. *)
Lemma seq_union_spec {A : Type} (f g : nat -> A) (x : A) :
  ((exists i, f i = x) \/ (exists j, g j = x)) <-> exists i, seq_union f g i = x.
Proof.
  split.
  - unfold seq_union; intros [[i Hf] | [i Hg]].
    + exists (2*i)%nat.
      rewrite mult_comm, Nat.mod_mul; try lia.
      rewrite Nat.div_mul; try lia; auto.
    + exists (2*i + 1)%nat.
      rewrite Nat.add_mod; try lia.
      rewrite mult_comm; rewrite Nat.mod_mul; try lia.
      rewrite plus_0_l.
      assert (H: ((i * 2 + 1) / 2 = i)%nat).
      { rewrite plus_comm.
        rewrite Nat.div_add; auto. }
      rewrite H; auto.
  - intros [i Hunion].
    unfold seq_union in Hunion.
    destruct (i mod 2); firstorder.
Qed.

(** Flatten a sequence of sequences via the bijection from nat to nat*nat. *)
Definition seq_flatten {A : Type} (f : nat -> nat -> A) (n : nat) : A :=
  let (i, j) := nat_f n in f i j.

(** Split a sequence into a sequence of sequences.*)
Definition seq_split {A : Type} (f : nat -> A) (i j : nat) : A :=
  let n := nat_g (i, j) in f n.

(* Definition sequence_union {A : Type} (f g : countable_sequence A) : countable_sequence A := *)
(*   match (f, g) with *)
(*   | (finite_seq l1, finite_seq l2) => finite_seq (l1 ++ l2) *)
(*   | (finite_seq l, infinite_seq s) => infinite_seq (prepend_list_seq l s) *)
(*   | (infinite_seq s, finite_seq l) => infinite_seq (prepend_list_seq l s) *)
(*   | (infinite_seq s1, infinite_seq s2) => infinite_seq (seq_union s1 s2) *)
(*   end. *)

(** Pointwise concatenation of monoid sequences. *)
Definition seq_concat {A : Type} (M : Monoid A) (f g : nat -> A) (i : nat) : A :=
  monoid_plus M (f i) (g i).

Definition seq_concat_n {A : Type} (M : Monoid A) (f g : nat -> A) (i n : nat) : A :=
  Nat.iter n (fun f' => seq_concat M f' g) f i.

(** Cartesian product of two monoid sequences. *)
Definition seq_product {A : Type} (M : Monoid A) (f g : nat -> A) (n : nat) : A :=
  let (i, j) := nat_f n in
  monoid_plus M (f i) (g j).

Definition seq_product' {A : Type} (M : Monoid A) (f g : nat -> A) : nat -> A :=
  seq_flatten (fun i j => seq_concat M (const (f i)) g j).

(** It's nice that the two definitions coincide perfectly. *)
Lemma seq_product_equiv {A : Type} (M : Monoid A) (f g : nat -> A) (n : nat) :
  seq_product M f g n = seq_product' M f g n.
Proof. reflexivity. Qed.  

(** Sequence containing all finite repetitions of elements of the
    argument sequence. *)
Definition seq_reps {A : Type} (M : Monoid A) (f : nat -> A) : nat -> A :=
  seq_flatten (fun i n => seq_concat_n M f f n i).

(** TODO: convert tree into partial function from reals to A. Then we
    can prove that it's a measurable function. *) 
(* Definition tree_partial_fun {A : Type} (t : tree A) : partial_fun real A := *)
(*   fun r => None. *)

Inductive RE (A : Type) : Type :=
| RE_empty : RE A
| RE_epsilon : RE A
| RE_lit : A -> RE A
| RE_seq : RE A -> RE A -> RE A
| RE_choice : RE A -> RE A -> RE A
| RE_plus : RE A -> RE A.

Definition RE_star {A : Type} (re : RE A) := RE_choice (@RE_epsilon A) (RE_plus re).

Fixpoint RE_of_tree_fail {A : Type} (t : tree A) (n : nat) : RE bool :=
  match t with
  | Leaf x => @RE_empty bool
  | Fail _ m => if m =? n then @RE_epsilon bool else @RE_empty bool
  | Choice _ t1 t2 => RE_choice (RE_seq (RE_lit true) (RE_of_tree_fail t1 n))
                               (RE_seq (RE_lit false) (RE_of_tree_fail t2 n))
  | Fix lbl t1 => @RE_empty bool
  end.

Fixpoint RE_of_tree {A : Type} (t : tree A) (P : A -> bool) : RE bool :=
  match t with
  | Leaf x => if P x then @RE_epsilon bool else @RE_empty bool
  | Fail _ _ => @RE_empty bool
  | Choice _ t1 t2 => RE_choice (RE_seq (RE_lit true) (RE_of_tree t1 P))
                               (RE_seq (RE_lit false) (RE_of_tree t2 P))
  | Fix lbl t1 => RE_seq (RE_star (RE_of_tree_fail t1 lbl)) (RE_of_tree t1 P)
  end.

(** TODO: need to account for observation failures. *)
(* Definition RE_of_tree' {A : Type} (t : tree A) (P : A -> bool) : RE bool := *)
(*   RE_seq (RE_of_tree_fail t *)

Definition MonoidOptionList {A : Type} : Monoid (option (list A)) :=
  {| monoid_plus := fun x y =>
                      match (x, y) with
                      | (None, _) => y
                      | (_, None) => x
                      | (Some l, Some r) => Some (l ++ r)
                      end
   ; monoid_unit := None |}.

Program Instance MonoidLawsOptionList {A : Type} : MonoidLaws (@MonoidOptionList A).
Next Obligation. intros [] [] []; auto; f_equal; rewrite app_assoc; auto. Qed.
Next Obligation. intro; auto. Qed.
Next Obligation. intros []; auto. Qed.

Inductive RE_sequence {A : Type} : RE A -> (nat -> option (list A)) -> Prop :=
| RE_sequence_empty : RE_sequence (@RE_empty A) (const None)
| RE_sequence_epsilon : RE_sequence (@RE_epsilon A) (singleton_seq [])
| RE_sequence_lit : forall x, RE_sequence (RE_lit x) (singleton_seq [x])
| RE_sequence_seq : forall r1 r2 s1 s2,
    RE_sequence r1 s1 ->
    RE_sequence r2 s2 ->
    RE_sequence (RE_seq r1 r2) (seq_product MonoidOptionList s1 s2)
| RE_sequence_choice : forall r1 r2 s1 s2,
    RE_sequence r1 s1 ->
    RE_sequence r2 s2 ->
    RE_sequence (RE_choice r1 r2) (seq_union s1 s2)
| RE_sequence_plus : forall r s,
    RE_sequence r s ->
    RE_sequence (RE_plus r) (seq_reps MonoidOptionList s).

(** A proposition asserting that the sequence [f] is generated by the
    tree [t] wrt predicate [P]. *)
Definition tree_sequence {A : Type}
           (t : tree A) (P : A -> bool) (f : nat -> option (list bool)) : Prop :=
  RE_sequence (RE_of_tree t P) f.

(* Inductive recognizes {A : Type} : RE A -> list A -> Prop := *)
(* | recognizes_epsilon : recognizes (@RE_epsilon A) [] *)
(* | recognizes_lit : forall x, recognizes (RE_lit x) [x] *)
(* | recognizes_seq : forall r1 r2 l1 l2, *)
(*     recognizes r1 l1 -> *)
(*     recognizes r2 l2 -> *)
(*     recognizes (RE_seq r1 r2) (l1 ++ l2) *)
(* | recognizes_choice_l : forall r1 r2 l, *)
(*     recognizes r1 l -> *)
(*     recognizes (RE_choice r1 r2) l *)
(* | recognizes_choice_r : forall r1 r2 l, *)
(*     recognizes r2 l -> *)
(*     recognizes (RE_choice r1 r2) l *)
(* | recognizes_plus : forall r l1 l2, *)
(*     recognizes r l1 -> *)
(*     recognizes (RE_star r) l2 -> *)
(*     recognizes (RE_plus r) (l1 ++ l2). *)
