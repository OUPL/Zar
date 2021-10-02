Require Import Coq.Arith.PeanoNat.
Require Import Nat.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Structures.Monoid.

Require Import axioms.
Require Import misc.

Inductive ix_tree : Type :=
| ix_leaf : nat -> ix_tree
| ix_node : ix_tree -> ix_tree -> ix_tree.

Fixpoint ix_tree_depth (t : ix_tree) : nat :=
  match t with
  | ix_leaf _ => O
  | ix_node l r => S (max (ix_tree_depth l) (ix_tree_depth r))
  end.

Fixpoint collapse_ix_tree (t : ix_tree) : nat :=
  match t with
  | ix_leaf i => i
  | ix_node l r => nat_g (collapse_ix_tree l, collapse_ix_tree r)
  end.

Inductive left_associated : ix_tree -> Prop :=
| left_associated_leaf : forall n, left_associated (ix_leaf n)
| left_associated_node : forall l n,
    left_associated l ->
    left_associated (ix_node l (ix_leaf n)).

Inductive right_associated : ix_tree -> Prop :=
| right_associated_leaf : forall n, right_associated (ix_leaf n)
| right_associated_node : forall r n,
    right_associated r ->
    right_associated (ix_node (ix_leaf n) r).
  
Fixpoint mk_ix_tree (n i : nat) : ix_tree :=
  match n with
  | O => ix_leaf i
  | S n' => let (l, r) := nat_f i in
           ix_node (mk_ix_tree n' l) (ix_leaf r)
  end.
  
Fixpoint mk_ix_tree' (n i : nat) : ix_tree :=
  match n with
  | O => ix_leaf i
  | S n' => let (l, r) := nat_f i in
           ix_node (ix_leaf l) (mk_ix_tree' n' r)
  end.

Lemma mk_ix_tree_left_associated (n i : nat) :
  left_associated (mk_ix_tree n i).
Proof.
  revert i; induction n; intro i; simpl.
  - constructor.
  - destruct (nat_f i); constructor; auto.
Qed.

Lemma mk_ix_tree'_right_associated (n i : nat) :
  right_associated (mk_ix_tree' n i).
Proof.
  revert i; induction n; intro i; simpl.
  - constructor.
  - destruct (nat_f i); constructor; auto.
Qed.

Lemma collapse_mk_ix_tree (n i : nat) :
  collapse_ix_tree (mk_ix_tree n i) = i.
Proof.
  revert i; induction n; intro i; simpl; auto.
  destruct (nat_f i) eqn:Hi; simpl.
  rewrite IHn, <- Hi, nat_g_f; reflexivity.
Qed.

Lemma collapse_mk_ix_tree' (n i : nat) :
  collapse_ix_tree (mk_ix_tree' n i) = i.
Proof.
  revert i; induction n; intro i; simpl; auto.
  destruct (nat_f i) eqn:Hi; simpl.
  rewrite IHn, <- Hi, nat_g_f; reflexivity.
Qed.

Fixpoint left_add (i : ix_tree) (t : ix_tree) : ix_tree :=
  match t with
  | ix_leaf n => ix_node i (ix_leaf n)
  | ix_node l r => ix_node (left_add i l) r
  end.

Fixpoint left_associate (t : ix_tree) : ix_tree :=
  match t with
  | ix_leaf n => ix_leaf n
  | ix_node l r => left_add l (left_associate r)
  end.

Lemma left_add_spec (t1 t2 : ix_tree) :
  left_associated t1 ->
  left_associated t2 ->
  left_associated (left_add t1 t2).
Proof.
  intros Ht1 Ht2.
  revert Ht1. revert t1.
  induction Ht2; simpl; intros t1 Ht1.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma left_associate_spec (t : ix_tree) :
  right_associated t ->
  left_associated (left_associate t).
Proof.
  induction t; simpl; intro H.
  - constructor.
  - inversion H; subst.
    apply left_add_spec; auto; constructor.
Qed.

Fixpoint right_add (t i : ix_tree) : ix_tree :=
  match t with
  | ix_leaf n => ix_node (ix_leaf n) i
  | ix_node l r => ix_node l (right_add r i)
  end.

Fixpoint right_associate (t : ix_tree) : ix_tree :=
  match t with
  | ix_leaf n => ix_leaf n
  | ix_node l r => right_add (right_associate l) r
  end.

Lemma right_add_spec (t1 t2 : ix_tree) :
  right_associated t1 ->
  right_associated t2 ->
  right_associated (right_add t1 t2).
Proof.
  intros Ht1; revert t2.
  induction Ht1; simpl; intros t2 Ht2.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma right_associate_spec (t : ix_tree) :
  left_associated t ->
  right_associated (right_associate t).
Proof.
  induction t; simpl; intro H.
  - constructor.
  - inversion H; subst.
    apply right_add_spec; auto; constructor.
Qed.

Lemma left_associate_right_add n l :
  left_associate (right_add l (ix_leaf n)) =
  ix_node (left_associate l) (ix_leaf n).
Proof.
  revert n; induction l; intro m; simpl; auto.
  rewrite IHl2; reflexivity.
Qed.

Lemma left_right_associate (t : ix_tree) :
  left_associated t ->
  left_associate (right_associate t) = t.
Proof.
  induction 1; simpl; auto.
  rewrite left_associate_right_add, IHleft_associated; auto.
Qed.

Lemma right_associate_left_add n r :
  right_associate (left_add (ix_leaf n) r) =
  ix_node (ix_leaf n) (right_associate r).
Proof.
  revert n; induction r; intro m; simpl; auto.
  rewrite IHr1; reflexivity.
Qed.

Lemma right_left_associate (t : ix_tree) :
  right_associated t ->
  right_associate (left_associate t) = t.
Proof.
  induction 1; simpl; auto.
  rewrite right_associate_left_add, IHright_associated; auto.
Qed.

(* For left-associated trees. *)
Fixpoint ix_tree_product {A : Type} (M : Monoid A)
         (f g : nat -> option A) (t : ix_tree) : option A :=
  match t with
  | ix_leaf i => f i
  | ix_node l r => option_mult M (ix_tree_product M f g l) (ix_tree_product M g g r)
  end.

(* For right-associated trees. *)
Fixpoint ix_tree_product' {A : Type} (M : Monoid A)
         (f g : nat -> option A) (t : ix_tree) : option A :=
  match t with
  | ix_leaf i => f i
  | ix_node l r => option_mult M (ix_tree_product' M g g l) (ix_tree_product' M f g r)
  end.

Lemma ix_tree_product'_right_add {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (t : ix_tree) (i : nat) :
  right_associated t ->
  option_mult M (ix_tree_product' M f f t) (f i) =
  ix_tree_product' M f f (right_add t (ix_leaf i)).
Proof.
  induction 1; simpl; auto.
  rewrite option_mult_assoc; auto.
  rewrite IHright_associated; reflexivity.
Qed.

Lemma ix_tree_product_left_add {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (t : ix_tree) (i : nat) :
  left_associated t ->
  option_mult M (f i) (ix_tree_product M f f t) =
  ix_tree_product M f f (left_add (ix_leaf i) t).
Proof.
  induction 1; simpl; auto.
  rewrite <- option_mult_assoc; auto.
  rewrite IHleft_associated; reflexivity.
Qed.

Lemma ix_tree_product_right_associate {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (t : ix_tree) :
  left_associated t ->
  ix_tree_product M f f t = ix_tree_product' M f f (right_associate t).
Proof.
  induction 1; simpl; auto.
  rewrite IHleft_associated.
  rewrite ix_tree_product'_right_add; auto.
  apply right_associate_spec; auto.
Qed.

Lemma ix_tree_product_left_associate {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (t : ix_tree) :
  right_associated t ->
  ix_tree_product' M f f t = ix_tree_product M f f (left_associate t).
Proof.
  induction 1; simpl; auto.
  rewrite IHright_associated.
  rewrite ix_tree_product_left_add; auto.
  apply left_associate_spec; auto.
Qed.

Lemma mk_ix_tree_collapse t :
  left_associated t ->
  mk_ix_tree (ix_tree_depth t) (collapse_ix_tree t) = t.
Proof.
  induction 1; simpl; auto.
  rewrite Nat.max_0_r, nat_f_g, IHleft_associated; reflexivity.
Qed.

Lemma mk_ix_tree'_collapse t :
  right_associated t ->
  mk_ix_tree' (ix_tree_depth t) (collapse_ix_tree t) = t.
Proof.
  induction 1; simpl; auto.
  rewrite nat_f_g, IHright_associated; reflexivity.
Qed.

Lemma mk_ix_tree_collapse' n t :
  n = ix_tree_depth t ->
  left_associated t ->
  mk_ix_tree n (collapse_ix_tree t) = t.
Proof. intro; subst; apply mk_ix_tree_collapse. Qed.

Lemma mk_ix_tree'_collapse' n t :
  n = ix_tree_depth t ->
  right_associated t ->
  mk_ix_tree' n (collapse_ix_tree t) = t.
Proof. intro; subst; apply mk_ix_tree'_collapse. Qed.

Lemma mk_ix_tree_depth n i :
  ix_tree_depth (mk_ix_tree n i) = n.
Proof.
  revert i; induction n; intro i; simpl; auto.
  destruct (nat_f i); simpl; rewrite Nat.max_0_r, IHn; reflexivity.
Qed.

Lemma mk_ix_tree'_depth n i :
  ix_tree_depth (mk_ix_tree' n i) = n.
Proof.
  revert i; induction n; intro i; simpl; auto.
  destruct (nat_f i); simpl; rewrite IHn; reflexivity.
Qed.

Lemma left_add_depth (l r : ix_tree) :
  left_associated l ->
  left_associated r ->
  ix_tree_depth (left_add l r) = S (ix_tree_depth l + ix_tree_depth r)%nat.
Proof.
  revert l; induction r; simpl; intros l Hl Hr; auto; try lia.
  inversion Hr; subst.
  rewrite IHr1; auto; simpl; lia.
Qed.

Lemma right_add_depth (l r : ix_tree) :
  right_associated l ->
  right_associated r ->
  ix_tree_depth (right_add l r) = S (ix_tree_depth l + ix_tree_depth r)%nat.
Proof.
  revert r; induction l; simpl; intros r Hl Hr; auto.
  inversion Hl; subst.
  rewrite IHl2; auto.
Qed.

Lemma left_associate_depth (t : ix_tree) :
  right_associated t ->
  ix_tree_depth (left_associate t) = ix_tree_depth t.
Proof.
  induction 1; simpl; auto.
  rewrite left_add_depth.
  - rewrite IHright_associated; simpl; lia.
  - constructor.
  - apply left_associate_spec; auto.
Qed.

Lemma right_associate_depth (t : ix_tree) :
  left_associated t ->
  ix_tree_depth (right_associate t) = ix_tree_depth t.
Proof.
  induction 1; simpl; auto.
  rewrite right_add_depth.
  - rewrite IHleft_associated; simpl; lia.
  - apply right_associate_spec; auto.
  - constructor.
Qed.

Lemma ix_tree_depth_mk_mk' (n i j : nat) :
  ix_tree_depth (mk_ix_tree n i) = ix_tree_depth (mk_ix_tree' n j).
Proof.
  revert i j; induction n; intros i j; simpl; auto.
  destruct (nat_f i); destruct (nat_f j); simpl.
  rewrite Nat.max_0_r.
  erewrite IHn; eauto.
Qed.

Fixpoint cut_left (t : ix_tree) : ix_tree :=
  match t with
  | ix_leaf n => ix_leaf n
  | ix_node l r => match l with
                  | ix_leaf _ => r
                  | _ => ix_node (cut_left l) r
                  end
  end.

Fixpoint cut_right (t : ix_tree) : ix_tree :=
  match t with
  | ix_leaf n => ix_leaf n
  | ix_node l r => match r with
                  | ix_leaf _ => l
                  | _ => ix_node l (cut_right r)
                  end
  end.

Lemma cut_left_right_associate_leaf t i :
  left_associated t ->
  cut_left (right_associate (ix_node (ix_leaf i) t)) = t.
Proof. induction 1; simpl; auto. Qed.

Lemma cut_right_left_associate_leaf t i :
  right_associated t ->
  cut_right (left_associate (ix_node t (ix_leaf i))) = t.
Proof. induction 1; simpl; auto. Qed.

Lemma ix_tree_depth_cut_left (t : ix_tree) :
  right_associated t ->
  ix_tree_depth (cut_left t) = pred (ix_tree_depth t).
Proof. induction 1; simpl; auto. Qed.

Lemma ix_tree_depth_cut_right (t : ix_tree) :
  left_associated t ->
  ix_tree_depth (cut_right t) = pred (ix_tree_depth t).
Proof. induction 1; simpl; auto; rewrite Nat.max_0_r; auto. Qed.

Lemma right_associated_cut_left (t : ix_tree) :
  right_associated t ->
  right_associated (cut_left t).
Proof. induction 1; simpl; auto; constructor. Qed.

Lemma left_associated_cut_right (t : ix_tree) :
  left_associated t ->
  left_associated (cut_right t).
Proof. induction 1; simpl; auto; constructor. Qed.

Lemma cut_left_left_add (i : nat) (t : ix_tree) :
  left_associated t ->
  cut_left (left_add (ix_leaf i) t) = t.
Proof.
  induction 1; simpl; auto.
  rewrite IHleft_associated.
  destruct l; simpl; auto.
Qed.

Lemma cut_right_right_add (i : nat) (t : ix_tree) :
  right_associated t ->
  cut_right (right_add t (ix_leaf i)) = t.
Proof.
  induction 1; simpl; auto.
  rewrite IHright_associated.
  destruct r; simpl; auto.
Qed.

Inductive leftmost : nat -> ix_tree -> Prop :=
| leftmost_leaf : forall i, leftmost i (ix_leaf i)
| leftmost_node : forall i l r,
    leftmost i l ->
    leftmost i (ix_node l r).

Inductive rightmost : nat -> ix_tree -> Prop :=
| rightmost_leaf : forall i, rightmost i (ix_leaf i)
| rightmost_node : forall i l r,
    rightmost i r ->
    rightmost i (ix_node l r).

Lemma left_add_cut_left (i : nat) (t : ix_tree) :
  leftmost i t ->
  (O < ix_tree_depth t)%nat ->
  left_associated t ->
  left_add (ix_leaf i) (cut_left t) = t.
Proof.
  intros H0 H1 H2.
  revert H0 H1. revert i.
  induction H2; simpl; intros i H0 Hlt; try lia.
  inversion H0; subst.
  destruct l.
  - inversion H3; subst; reflexivity.
  - simpl; rewrite IHleft_associated; auto.
    simpl; lia.
Qed.

Lemma right_add_cut_right (i : nat) (t : ix_tree) :
  rightmost i t ->
  (O < ix_tree_depth t)%nat ->
  right_associated t ->
  right_add  (cut_right t) (ix_leaf i) = t.
Proof.
  intros H0 H1 H2.
  revert H0 H1. revert i.
  induction H2; simpl; intros i H0 Hlt; try lia.
  inversion H0; subst.
  destruct r.
  - inversion H3; subst; reflexivity.
  - simpl; rewrite IHright_associated; auto.
    simpl; lia.
Qed.

Lemma left_associate_cut_left (t : ix_tree) :
  right_associated t ->
  left_associate (cut_left t) = cut_left (left_associate t).
Proof.
  induction 1; simpl; auto.
  rewrite cut_left_left_add; auto.
  apply left_associate_spec; auto.
Qed.

Lemma right_associate_cut_right (t : ix_tree) :
  left_associated t ->
  right_associate (cut_right t) = cut_right (right_associate t).
Proof.
  induction 1; simpl; auto.
  rewrite cut_right_right_add; auto.
  apply right_associate_spec; auto.
Qed.

Lemma leftmost_left_add i l r :
  leftmost i l ->
  leftmost i (left_add l r).
Proof. revert l; induction r; simpl; intros l H; constructor; auto. Qed.

Lemma rightmost_right_add i l r :
  rightmost i r ->
  rightmost i (right_add l r).
Proof. revert r; induction l; simpl; intros r H; constructor; auto. Qed.

Lemma leftmost_right_add i l r :
  leftmost i l ->
  leftmost i (right_add l r).
Proof.
  revert r; induction l; simpl; intros r H;
    inversion H; subst; constructor; auto.
Qed.

Lemma rightmost_left_add i l r :
  rightmost i r ->
  rightmost i (left_add l r).
Proof.
  revert l; induction r; simpl; intros l H;
    inversion H; subst; constructor; auto.
Qed.

Lemma leftmost_left_associate i t :
  leftmost i t ->
  leftmost i (left_associate t).
Proof.
  revert i; induction t; simpl; intros i H0; inversion H0; subst.
  - constructor.
  - apply leftmost_left_add; auto.
Qed.

Lemma rightmost_right_associate i t :
  rightmost i t ->
  rightmost i (right_associate t).
Proof.
  revert i; induction t; simpl; intros i H0; inversion H0; subst.
  - constructor.
  - apply rightmost_right_add; auto.
Qed.

Lemma leftmost_right_associate i t :
  leftmost i t ->
  leftmost i (right_associate t).
Proof.
  revert i; induction t; simpl; intros i H0; inversion H0; subst.
  - constructor.
  - apply leftmost_right_add; auto.
Qed.

Lemma rightmost_left_associate i t :
  rightmost i t ->
  rightmost i (left_associate t).
Proof.
  revert i; induction t; simpl; intros i H0; inversion H0; subst.
  - constructor.
  - apply rightmost_left_add; auto.
Qed.

Lemma cut_right_cut_left (t : ix_tree) :
  (1 < ix_tree_depth t)%nat ->
  cut_right (cut_left t) = cut_left (cut_right t).
Proof.
  induction t; simpl; intro Hlt; auto.
  destruct t1, t2; simpl in *; auto; lia.
Qed.

Lemma cut_left_right_add (l r : ix_tree) :
  (O < ix_tree_depth l)%nat ->
  cut_left (right_add l r) = right_add (cut_left l) r.
Proof.
  revert r; induction l; simpl; intros r Hlt; try lia.
  clear Hlt; destruct l1; auto.
Qed.

Lemma cut_right_left_add (l r : ix_tree) :
  (O < ix_tree_depth r)%nat ->
  cut_right (left_add l r) = left_add l (cut_right r).
Proof.
  revert l; induction r; simpl; intros l Hlt; try lia.
  clear Hlt; destruct r2; auto.
Qed.

Lemma cut_right_left_associate t :
  (1 < ix_tree_depth t)%nat ->
  right_associated t ->
  cut_right (left_associate t) = left_associate (cut_right t).
Proof.
  intros Hlt H; revert Hlt; induction H; simpl; intro Hlt; auto.
  rewrite cut_right_left_add.
  2: { rewrite left_associate_depth; auto; lia. }
  destruct r; simpl in Hlt; try lia; simpl.
  destruct r2; simpl in *.
  - destruct r1; simpl in *; auto.
    rewrite <- IHright_associated; try lia.
    reflexivity.
  - destruct r1; simpl in *; auto;
      rewrite <- IHright_associated; try lia; reflexivity.
Qed.

Lemma cut_left_right_associate t :
  (1 < ix_tree_depth t)%nat ->
  left_associated t ->
  cut_left (right_associate t) = right_associate (cut_left t).
Proof.
  intros Hlt H; revert Hlt; induction H; simpl; intro Hlt; auto.
  rewrite Nat.max_0_r in Hlt.
  rewrite cut_left_right_add.
  2: { rewrite right_associate_depth; auto; lia. }
  destruct l; simpl in Hlt; try lia; simpl.
  destruct l1; simpl in *.
  - destruct l2; simpl in *; auto.
    rewrite <- IHleft_associated; try lia.
    reflexivity.
  - destruct l2; simpl in *; auto;
      rewrite <- IHleft_associated; try lia; reflexivity.
Qed.

Lemma left_associated_cut_left (t : ix_tree) :
  left_associated t ->
  left_associated (cut_left t).
Proof.
  induction 1; simpl; try constructor.
  destruct l; try constructor; auto.
Qed.

Lemma right_associated_cut_right (t : ix_tree) :
  right_associated t ->
  right_associated (cut_right t).
Proof.
  induction 1; simpl; try constructor.
  destruct r; try constructor; auto.
Qed.

Lemma rightmost_cut_left i t :
  rightmost i t ->
  rightmost i (cut_left t).
Proof.
  induction 1; simpl; try constructor.
  destruct l; auto; simpl; constructor; auto.
Qed.

Lemma leftmost_cut_right i t :
  leftmost i t ->
  leftmost i (cut_right t).
Proof.
  induction 1; simpl; try constructor.
  destruct r; auto; simpl; constructor; auto.
Qed.
