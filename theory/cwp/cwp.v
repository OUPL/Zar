Set Implicit Arguments.

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
Local Open Scope program_scope.
Import ListNotations.

Require Import order.

(** The cpGCL language *)

Definition val := bool.
Definition St : Type := nat -> val.
Definition empty : St := fun _ => false.
Definition upd (x : nat) (v : val) (st : St) : St :=
  fun y => if Nat.eqb y x then v else st y.
Definition exp := St -> val.

Inductive cpGCL : Type :=
| CSkip : cpGCL
| CAbort : cpGCL
| CAssign : nat -> exp -> cpGCL
| CSeq : cpGCL -> cpGCL -> cpGCL
| CIte : exp -> cpGCL -> cpGCL -> cpGCL
| CChoice : Q -> cpGCL -> cpGCL -> cpGCL
| CWhile : exp -> cpGCL -> cpGCL
| CObserve : exp -> cpGCL.

Record prog :=
  { prog_com : cpGCL
  ; prog_query : exp }.

Notation "a ';;' b" := (CSeq a b) (at level 100, right associativity) : cpGCL_scope.
Open Scope cpGCL_scope.
Open Scope order_scope.


(** Choice trees with fix (loop) nodes *)
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
    + destruct (Nat.eqb_spec n n0); subst.
      * constructor.
      * constructor; auto; apply IHt; intro HC; apply H; constructor; auto.
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

(* Lemma not_bound_or_free_not_in {A : Type} (n : nat) (t : tree A) : *)
(*   not_bound_in n t -> not_free_in n t -> not_in n t. *)
(* Proof. *)
(* Admitted. *)

(* Lemma not_in_not_bound_and_not_free {A : Type} (n : nat) (t : tree A) : *)
(*   not_in n t -> not_free_in n t /\ not_bound_in n t. *)
(* Proof. *)
(* Admitted. *)

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


Definition mkFix {A : Type} (f : nat -> St -> tree A) : state nat (St -> tree A) :=
  bind get (fun l => bind (put (S l)) (const (ret (Fix (S l) ∘ (f (S l)))))).

Fixpoint compile (c : cpGCL) : state nat (St -> tree St) :=
  match c with
  | CSkip => ret (@Leaf _)
  | CAbort => mkFix (fun n => const (Fail _ n))
  | CSeq c1 c2 =>
    bind (compile c1) (fun k1 => bind (compile c2) (fun k2 => ret (kcomp k1 k2)))
  | CAssign x e => ret (fun st => Leaf (upd x (e st) st))
  | CIte e c1 c2 =>
    bind (compile c1)
         (fun k1 => bind (compile c2)
                      (fun k2 => ret (fun st => if e st
                                          then k1 st
                                          else k2 st)))
  | CChoice p c1 c2 =>
    bind (compile c1)
         (fun k1 => bind (compile c2)
                      (fun k2 => ret (fun st => Choice p (k1 st) (k2 st))))
  | CWhile e body =>
    bind (compile body)
         (fun k => mkFix (fun n st => bind (k st)
                                     (fun st' => if e st'
                                              then Fail _ n
                                              else Leaf st')))
  | CObserve e =>
    ret (fun st => if e st then Leaf st else Fail _ O)
  end.

Definition runCompile (c : cpGCL) (n : nat) : (St -> tree St) * nat :=
  runState (compile c) n.

Definition evalCompile (c : cpGCL) (n : nat) : St -> tree St :=
  evalState (compile c) n.

Definition evalCompile' (c : cpGCL) : St -> tree St :=
  evalCompile c O.

Lemma compile_bound_n_m (c : cpGCL) (n m : nat) (k : St -> tree St) :
  runState (compile c) n = (k, m) ->
  (n <= m)%nat.
Proof.
  revert n m k.
  induction c; intros m m' k Hc; try solve [inversion Hc; subst; omega].
  - inversion Hc; subst.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion H0; subst; clear H0.
    etransitivity.
    eapply IHc1; eauto.
    eapply IHc2; eauto.
  - inversion Hc; subst.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion H0; subst; clear H0.
    etransitivity.
    eapply IHc1; eauto.
    eapply IHc2; eauto.
  - inversion Hc; subst.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion H0; subst; clear H0.
    etransitivity.
    eapply IHc1; eauto.
    eapply IHc2; eauto.
  - inversion Hc; subst.
    destruct (runState (compile c) m) eqn:Hc1.
    inversion H0; subst; clear H0.
    etransitivity. eapply IHc; eauto. omega.
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

Lemma compile_bound_labels (c : cpGCL) (n m : nat) (k : St -> tree St) :
  runState (compile c) n = (k, m) ->
  forall l st, bound_in l (k st) -> n < l <= m.
Proof.
  revert n m k. induction c; intros m m' k Hc l st Hbound; simpl in Hc.
  - inversion Hc; subst.
    inversion Hbound.
  - inversion Hc; subst.
    unfold compose, const in Hbound.
    inversion Hbound; subst. omega. inversion H3.
  - inversion Hc; subst.
    inversion Hbound.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    apply bound_in_bind in Hbound. destruct Hbound.
    + eapply IHc1 in Hc1; eauto.
      apply compile_bound_n_m in Hc2; omega.
    + destruct H. eapply IHc2 in Hc2; eauto.
      apply compile_bound_n_m in Hc1; omega.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    destruct (e st).
    + eapply IHc1 in Hc1; eauto.
      apply compile_bound_n_m in Hc2; omega.
    + eapply IHc2 in Hc2; eauto.
      apply compile_bound_n_m in Hc1; omega.
  - destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    inversion Hbound; subst.
    + eapply IHc1 in Hc1; eauto.
      apply compile_bound_n_m in Hc2; omega.
    + eapply IHc2 in Hc2; eauto.
      apply compile_bound_n_m in Hc1; omega.
  - destruct (runState (compile c) m) eqn:Hc1.
    inversion Hc; subst; clear Hc.
    unfold compose in Hbound.
    inversion Hbound; subst.
    + apply compile_bound_n_m in Hc1; omega.
    + apply bound_in_bind' in H3.
      * eapply IHc in Hc1; eauto; omega.
      * intro x; destruct (e x); constructor.
  - inversion Hc; subst; clear Hc.
    destruct (e st); inversion Hbound.
Qed.


(** Inference on trees *)

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
  | Choice p t1 t2 => p * infer_fail n t1 + (1-p) * infer_fail n t2
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
    let b := infer_fail_lib m t in
    if Qeq_bool b 1 then 1 else a / (1 - b)
  end.

Definition infer {A : Type} (f : A -> Q) (t : tree A) : Q :=
  let a := infer_f f t in
  let b := infer_f_lib (const 1) t in
  a / b.
  (* let b := infer_fail O t in *)
  (* a / (1 - b). *)


(** Testing inference on example programs *)

Definition sample (x : nat) (p : Q) : cpGCL :=
  CChoice p (CAssign x (const true)) (CAssign x (const false)).

Definition goldfish_piranha : cpGCL :=
  sample 0%nat (1#2) ;;
  CAssign 1%nat (const true) ;;
  CChoice (1#2) (CAssign 2%nat (fun st => st 0%nat))
                (CAssign 2%nat (fun st => st 1%nat)) ;;
  CObserve (fun st => eqb (st 2%nat) true).

Definition goldfish_piranha_tree : tree St :=
  evalCompile' goldfish_piranha empty.

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             goldfish_piranha_tree)).

Definition test_abort : cpGCL :=
  CChoice (1#3) (CAssign 0%nat (const true)) CAbort.

Definition test_abort_tree : tree St := evalCompile' test_abort empty.

(* Eval compute in (evalCompile' test_abort empty). *)

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             test_abort_tree)).
Eval compute in (Qred (infer (fun st => if negb (st O) then 1 else 0)
                             test_abort_tree)).
Eval compute in (Qred (infer (const 1) test_abort_tree)).

Eval compute in (Qred (infer_f (fun st => if st O : bool then 1 else 0) test_abort_tree)).
Eval compute in (Qred (infer_f (const 1) (evalCompile' (CChoice (1#2) CSkip CAbort) empty))).

Definition fair_coin : cpGCL :=
  CAssign 0 (const false) ;;
  CAssign 1 (const false) ;;
  CWhile (fun st => eqb (st 0%nat) (st 1%nat))
         (sample 0%nat (1#3) ;; sample 1%nat (1#3)).

Definition fair_coin_tree : tree St := evalCompile' fair_coin empty.

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             fair_coin_tree)).

Definition two_thirds_loop (x : nat) (z : nat) : cpGCL :=
  CAssign z (const true) ;;
    CWhile (fun st => st z)
           (CChoice (1#2)
                    (CAssign x (const true) ;;
                     CAssign z (const false))
                    (CChoice (1#2)
                             CSkip
                             (CAssign x (const false) ;;
                              CAssign z (const false)))).

Definition fair_coin_loop : cpGCL :=
  CAssign 0 (const false) ;;
  CAssign 1 (const false) ;;
  CWhile (fun st => eqb (st 0%nat) (st 1%nat))
         (two_thirds_loop 0%nat 2%nat ;;
          two_thirds_loop 1%nat 2%nat).

Definition fair_coin_loop_tree : tree St := evalCompile' fair_coin_loop empty.

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             fair_coin_loop_tree)).


(** Relational specification of weakest pre-expectation semantics *)
Inductive wp : cpGCL -> (St -> Q) -> (St -> Q) -> Prop :=
| wp_skip : forall f g, f ==f g -> wp CSkip f g
| wp_abort : forall f g, g ==f const 0 -> wp CAbort f g
| wp_assign : forall x e f f',
    f' ==f (fun st => f (upd x (e st) st)) ->
    wp (CAssign x e) f f'
| wp_seq : forall c1 c2 f f' g g',
    wp c2 f g ->
    wp c1 g g' ->
    f' ==f g' ->
    wp (CSeq c1 c2) f f'
| wp_ite : forall e c1 c2 f f' g h,
    wp c1 f g ->
    wp c2 f h ->
    f' ==f (fun st => if e st : bool then g st else h st) ->
    wp (CIte e c1 c2) f f'
| wp_choice : forall p c1 c2 f f' g h,
    wp c1 f g ->
    wp c2 f h ->
    f' ==f (fun st => p * g st + (1-p) * h st) ->
    wp (CChoice p c1 c2) f f'
| wp_while : forall e body f f' ch,
    ch O = const 0 ->
    (forall n, exists g, wp body (ch n) g /\
               ch (S n) = fun st => if e st : bool then g st else f st) ->
    supremum f' ch ->
    wp (CWhile e body) f f'
| wp_observe : forall e f f',
    f' ==f (fun st => if e st : bool then f st else 0) ->
    wp (CObserve e) f f'.

(* Lemma wp_proper (c : cpGCL) (f g g': St -> Q) : *)
(*   wp c f g -> *)
(*   g ==f g' -> *)
(*   wp c f g'. *)
(* Proof. *)
(*   induction c; intros H0 H1; inversion H0; subst; clear H0. *)
(*   - constructor; auto; eapply f_Qeq_trans; eauto. *)
(*   - constructor; auto; eapply f_Qeq_trans; eauto; apply f_Qeq_symm; auto. *)
(*   - constructor; intro x; rewrite <- H1, H5; reflexivity. *)
(*   - eapply wp_seq; eauto; eapply f_Qeq_trans; eauto; apply f_Qeq_symm; auto. *)
(*   - econstructor; eauto; intro x; rewrite <- H1, H8; reflexivity. *)
(*   - econstructor; eauto; intro x; rewrite <- H1, H8; reflexivity. *)
(*   - econstructor; eauto; eapply equ_supremum; eauto; apply f_Qeq_equ; auto. *)
(*   - constructor; intro x; rewrite <- H1, H2; reflexivity. *)
(* Qed. *)


(** Relational specification of weakest liberal pre-expectation
    semantics *)
Inductive wlp : cpGCL -> (St -> Q) -> (St -> Q) -> Prop :=
| wlp_skip : forall f, wlp CSkip f f
| wlp_abort : forall f, wlp CAbort f (const 1)
| wlp_assign : forall x e f,
    wlp (CAssign x e) f (fun st => f (upd x (e st) st))
| wlp_seq : forall c1 c2 f f' f'',
    wlp c2 f f' ->
    wlp c1 f' f'' ->
    wlp (CSeq c1 c2) f f''
| wlp_ite : forall e c1 c2 f g h,
    wlp c1 f g ->
    wlp c2 f h ->
    wlp (CIte e c1 c2) f (fun st => if e st then g st else h st)
| wlp_choice : forall p c1 c2 f f' g h,
    wlp c1 f g ->
    wlp c2 f h ->
    f' ==f (fun st => p * g st + (1-p) * h st) ->
    wlp (CChoice p c1 c2) f f'
| wlp_while : forall e body f f' ch,
    ch O = const 1 ->
    (forall n, exists g, wlp body (ch n) g /\
               ch (S n) ==f fun st => if e st : bool then g st else f st) ->
    infimum f' ch ->
    wlp (CWhile e body) f f'
| wlp_observe : forall e f,
    wlp (CObserve e) f (fun st => if e st then f st else 0).

(** cwp_ is decomposed into wp and wlp *)
Definition cwp_ (c : cpGCL) (f f' g g' : St -> Q) :=
  wp c f f' /\ wlp c g g'.

(** cwp is the ratio of the pair given by cwp_ *)
Definition cwp (c : cpGCL) (f f'' : St -> Q) :=
  exists f' g', cwp_ c f f' (const 1) g' /\ f'' ==f fun st => f' st / g' st.


(* TODO: restrictions on reading/writing to variables within
   while-loops to ensure correctness of tree inference. *)
Inductive wf_cpGCL : cpGCL -> Prop :=
| wf_skip : wf_cpGCL CSkip
| wf_abort : wf_cpGCL CAbort
| wf_assign : forall x e, wf_cpGCL (CAssign x e)
| wf_seq : forall c1 c2,
    wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CSeq c1 c2)
| wf_ite : forall e c1 c2,
    wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CIte e c1 c2)
| wf_cchoice : forall p c1 c2,
    0 <= p <= 1 -> wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CChoice p c1 c2)
| wf_while : forall e body, wf_cpGCL body -> wf_cpGCL (CWhile e body)
| wf_observe : forall e, wf_cpGCL (CObserve e).

(** f is an expectation *)
Definition expectation {A : Type} (f : A -> Q) := forall x, 0 <= f x.

Lemma Qle_Qdiv_1 (x : Q) : x / 1 == x.
Proof. field. Qed.

Lemma Qdiv_0_num (a : Q) : 0 / a == 0.
Proof. destruct a; destruct Qnum; compute; reflexivity. Qed.

Lemma Qdiv_0_den (a : Q) : a / 0 == 0.
Proof. destruct a; destruct Qnum; compute; reflexivity. Qed.

Definition sum_Q_list (l : list Q) : Q :=
  fold_right Qplus 0 l.


Lemma not_in_sum_Q_list a l:
  ~ In a l ->
  sum_Q_list (map (fun n : nat => if a =? n then 1 else 0) l) = 0.  
Proof.
  induction l; auto; intro Hnotin.
  simpl.
  destruct (Nat.eqb_spec a a0); subst.
  - exfalso; apply Hnotin; constructor; auto.
  - rewrite IHl; auto.
    intro HC; apply Hnotin; right; auto.
Qed.

Lemma sum_Q_list_map_plus {A : Type} (f g : A -> Q) (l : list A) :
  sum_Q_list (map (fun x => f x + g x) l) ==
  sum_Q_list (map f l) + sum_Q_list (map g l).
Proof. induction l; simpl; lra. Qed.

Lemma sum_Q_list_map_mult_scalar {A : Type} (a : Q) (f : A -> Q) (l : list A) :
  sum_Q_list (map (fun x => a * f x) l) ==
  a * sum_Q_list (map f l).
Proof. induction l; simpl; lra. Qed.

Lemma sum_Q_list_map_div_scalar {A : Type} (a : Q) (f : A -> Q) (l : list A) :
  0 < a ->
  sum_Q_list (map (fun x => f x / a) l) ==
  sum_Q_list (map f l) / a.
Proof.
  intro H0; induction l; simpl. field. lra.
  rewrite IHl. field. lra.
Qed.

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
      assert (1-1==0). lra.
      rewrite H3. rewrite Qdiv_0_den.
      rewrite Qplus_0_l.
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

Lemma infer_f_expectation {A : Type} (f : A -> Q) (t : tree A) :
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

Lemma not_in_infer_fail {A : Type} (n : nat) (t : tree A) :
  not_in n t ->
  infer_fail n t == 0.
Proof.
  revert n. induction t; intros m Hnotin; simpl; try reflexivity.
  - inversion Hnotin; subst.
    destruct (Nat.eqb_spec n m). congruence. reflexivity.
  - inversion Hnotin; subst.
    rewrite IHt1, IHt2; auto. field.
  - inversion Hnotin; subst.
    apply IHt in H3.
    rewrite H3. apply Qdiv_0_num.
Qed.

Lemma Qeq_Qdiv (a b c d : Q) :
  a == c -> b == d -> a / b == c / d.
Proof. intros H0 H1; rewrite H0, H1; reflexivity. Qed.

Lemma Qeq_Qminus (a b c d : Q) :
  a == c -> b == d -> a - b == c - d.
Proof. intros; lra. Qed.

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

Lemma compile_bound_in_0_lt (c : cpGCL) (n n' m : nat) (k : St -> tree St) (x : St) :
  runState (compile c) n = (k, n') ->
  bound_in m (k x) ->
  (0 < m)%nat.
Proof.
  revert n n' m k x.
  induction c; intros n' n'' m k x Hc Hbound; simpl in Hc; inversion Hc; subst.
  - inversion Hbound.
  - inversion Hbound; subst. omega. inversion H3.
  - inversion Hbound.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc H0.
    apply bound_in_bind in Hbound. destruct Hbound.
    + eapply IHc1; eauto.
    + destruct H; eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc H0.
    destruct (e x).
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc H0.
    inversion Hbound; subst.
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c) n') eqn:Hc1.
    inversion Hc; subst; clear Hc H0.
    inversion Hbound; subst. omega.
    apply bound_in_bind' in H3.
    + eapply IHc; eauto.
    + intro y; destruct (e y); constructor; auto.
  - destruct (e x); inversion Hbound.
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

Lemma compile_free_in_0 (c : cpGCL) (n n' m : nat) (k : St -> tree St) (x : St) :
  runState (compile c) n = (k, n') ->
  free_in m (k x) ->
  m = O.
Proof.
  revert n n' m k x.
  induction c; intros n' n'' m k x Hc Hfree; simpl in Hc.
  - inversion Hc; subst. inversion Hfree.
  - inversion Hc; subst. unfold compose, const in Hfree.
    inversion Hfree; subst.
    inversion H3; subst. congruence.
  - inversion Hc; subst. inversion Hfree.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    apply free_in_bind in Hfree.
    destruct Hfree.
    + eapply IHc1; eauto.
    + destruct H; eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    destruct (e x).
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c1) n') eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hc; subst; clear Hc.
    inversion Hfree; subst.
    + eapply IHc1; eauto.
    + eapply IHc2; eauto.
  - destruct (runState (compile c) n') eqn:Hc1.
    inversion Hc; subst; clear Hc.
    inversion Hfree; subst.
    apply free_in_bind' in H3.
    + eapply IHc; eauto.
    + intro y; destruct (e y); constructor; auto.
  - inversion Hc; subst.
    destruct (e x); inversion Hfree; reflexivity.
Qed.

Lemma compile_not_in (c : cpGCL) (n n' m : nat) (k : St -> tree St) :
  runState (compile c) n = (k, n') ->
  (S m <= n)%nat ->
  forall x, not_in (S m) (k x).
Proof.
  intros Hc Hle x.
  apply not_in_not_bound_or_free. intro H.
  destruct H.
  + eapply compile_free_in_0 in H; eauto. omega.
  + eapply compile_bound_labels in H; eauto. omega.
Qed.

Lemma compile_bound_in_not_in (c1 c2 : cpGCL) (n n' m m' : nat) (k1 : St -> tree St) (k2 : St -> tree St) :
  runState (compile c1) n = (k1, n') ->
  runState (compile c2) m = (k2, m') ->
  (n' <= m)%nat ->
  forall n0 x y, bound_in n0 (k1 x) ->
            not_in n0 (k2 y).
Proof.
  revert k1 k2 c2 n n' m m'.
  induction c1; intros k1 k2 c2 n' n'' m m' H0 H1 Hle n0 x y Hbound.
  - inversion H0; subst. inversion Hbound.
  - inversion H0; subst.
    unfold compose, const in Hbound.
    inversion Hbound; subst; clear H0.
    + eapply compile_not_in; eauto.
    + inversion H5.
  - inversion H0; subst. inversion Hbound.
  - inversion H0.
    destruct (runState (compile c1_1) n') eqn:Hc1_1.
    destruct (runState (compile c1_2) n) eqn:Hc1_2.
    inversion H2; subst; clear H2.
    unfold kcomp in Hbound. simpl in Hbound.
    generalize (@compile_bound_labels (c1_1;;c1_2) n' n'' (kcomp t t0) H0 n0 x Hbound).
    intros [Hlt Hle'].
    assert (n0 <= m)%nat. omega.
    destruct n0.
    + eapply compile_bound_in_0_lt in H0; eauto. omega.
    + eapply compile_not_in; eauto.
  - inversion H0; subst.
    destruct (runState (compile c1_1) n') eqn:Hc1_1.
    destruct (runState (compile c1_2) n) eqn:Hc1_2.
    inversion H2; subst; clear H2.
    destruct (e x).
    + eapply IHc1_1; eauto.
      apply compile_bound_n_m in Hc1_2; omega.
    + eapply IHc1_2; eauto.
  - inversion H0; subst.
    destruct (runState (compile c1_1) n') eqn:Hc1_1.
    destruct (runState (compile c1_2) n) eqn:Hc1_2.
    inversion H2; subst; clear H2.
    inversion Hbound; subst.
    + eapply IHc1_1; eauto.
      apply compile_bound_n_m in Hc1_2; omega.
    + eapply IHc1_2; eauto.
  - inversion H0; subst.
    destruct (runState (compile c1) n') eqn:Hc1_1.
    inversion H2; subst; clear H2.
    unfold compose in Hbound.
    inversion Hbound; subst.
    + eapply compile_not_in; eauto.
    + apply bound_in_bind' in H5.
      eapply IHc1; eauto. omega.
      intro z. destruct (e z); constructor; auto.
  - inversion H0; subst.
    destruct (e x); inversion Hbound.
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

Lemma compile_wf (c : cpGCL) (n : nat) :
  wf_cpGCL c ->
  (forall st, wf_tree (evalCompile c n st)).
Proof.
  revert n.
  induction c; intros m Hwf st;
    unfold evalCompile, evalState; simpl;
      try solve [repeat constructor].
  - inversion Hwf; subst. apply (IHc1 m) with (st:=st) in H1.
    unfold evalCompile, evalState in H1.
    destruct (runState (compile c1) m) eqn:Hc1.
    unfold evalCompile, evalState in IHc2.
    specialize (IHc2 n H2).
    destruct (runState (compile c2) n) eqn:Hc2.
    unfold kcomp. simpl in *.
    apply wf_tree_bind; auto.
    intros l x Hbound.
    apply bound_in_not_bound_in. intro HC.
    eapply compile_bound_labels in Hc1; eauto.
    eapply compile_bound_labels in Hc2; eauto.
    omega.
  - inversion Hwf; subst.
    specialize (IHc1 m H1).
    unfold evalCompile, evalState in IHc1.
    destruct (runState (compile c1) m).
    specialize (IHc2 n H3).
    unfold evalCompile, evalState in IHc2.
    destruct (runState (compile c2) n).
    simpl in *.
    destruct (e st); auto.
  - inversion Hwf; subst.
    specialize (IHc1 m H3).
    unfold evalCompile, evalState in IHc1.
    destruct (runState (compile c1) m).
    specialize (IHc2 n H4).
    unfold evalCompile, evalState in IHc2.
    destruct (runState (compile c2) n).
    simpl in *.
    constructor; auto.
  - unfold evalCompile, evalState in IHc.
    inversion Hwf; subst.
    specialize (IHc m H0).
    destruct (runState (compile c) m) eqn:Hc.
    simpl in *.
    unfold compose.
    constructor.
    + apply wf_tree_bind; auto.
      * intros; destruct (e x); constructor.
      * intro x; destruct (e x); constructor.
    + apply bound_in_not_bound_in. intro HC.
      apply bound_in_bind in HC. destruct HC.
      * eapply compile_bound_labels in Hc; eauto. omega.
      * destruct H. destruct (e x); inversion H.
  - destruct (e st); constructor.
Qed.

Theorem wp_infer (c : cpGCL) (f : St -> Q) (n : nat) :
  wf_cpGCL c ->
  expectation f ->
  wp c f (infer_f f ∘ evalCompile c n).
Proof.
  revert f n. induction c; intros f m Hwf Hexp; try solve [constructor; reflexivity].
  (* sequence *)
  - unfold compose. unfold evalCompile, evalState in *. simpl.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2.
    inversion Hwf; subst.

    econstructor. apply IHc2 with (n:=n); auto.
    apply IHc1 with (n:=m); auto. intro x.
    apply infer_f_expectation; auto. apply compile_wf; auto.
    intro x. unfold compose. simpl.
    rewrite Hc1. rewrite Hc2.
    unfold kcomp. simpl. rewrite <- infer_f_bind. reflexivity.
    intros n1 x0 Hbound. eapply compile_bound_in_not_in.
    apply Hc1. apply Hc2. omega. apply Hbound.

  (* ite *)
  - unfold compose; simpl.
    set (fi := infer_f f).
    inversion Hwf; subst.
    unfold evalCompile, evalState in *. simpl.
    destruct (runState (compile c1) m) eqn:Hc1.
    destruct (runState (compile c2) n) eqn:Hc2. simpl.
    econstructor. apply IHc1 with (n:=m); auto.
    apply IHc2 with (n:=n); auto.
    intro x. destruct (e x).
    rewrite Hc1; reflexivity.
    rewrite Hc2; reflexivity.

  (* choice *)
  - unfold compose, evalCompile, evalState in *; simpl.
    inversion Hwf; subst.
    specialize (IHc1 f m H3 Hexp).
    destruct (runState (compile c1) m) eqn:Hc1.
    specialize (IHc2 f n H4 Hexp).
    destruct (runState (compile c2) n) eqn:Hc2. simpl in *.
    econstructor.
    apply IHc1.
    apply IHc2.
    reflexivity.

  (* while *)
  -
    (* Need to provide a chain of approximations that satisfies the
       conditions of the while wp constructor, and such that infer
       after compile yields of the supremum of that chain (probably
       via an argument based on convergence of geometric series). *)
    
    simpl. unfold compose. simpl.
    (* econstructor. *)

    admit.

  (* observe *)
  - unfold compose, evalCompile, evalState; simpl.
    constructor. intro x. destruct (e x); reflexivity.
Admitted.

Theorem wlp_infer (c : cpGCL) (f : St -> Q) (n : nat) :
  wf_cpGCL c ->
  expectation f ->
  wlp c f (infer_f_lib f ∘ evalCompile c n).
Proof.
(*   revert f n. induction c; intros f m Hwf Hexp; try solve [constructor]. *)
(*   (* abort *) *)
(*   - simpl; rewrite Nat.eqb_refl; constructor. *)
(*   (* sequence *) *)
(*   - simpl. *)
(*     inversion Hwf; subst. *)
(*     econstructor. *)
(*     apply IHc2 with (n:=m); auto. *)
(*     assert (Hexp': expectation ((fun st : St => infer_f_lib f m (compile c2 st)))). *)
(*     { admit. } *)
(*     specialize (IHc1 _ m H1 Hexp'). *)
(*     assert (Heq: (fun st : St => infer_f_lib *)
(*                                 f m (kcomp (compile c1) (compile c2) st)) = *)
(*                  (fun st : St => *)
(*                     infer_f_lib *)
(*                       (fun st0 : St => infer_f_lib f m (compile c2 st0)) *)
(*                       m (compile c1 st))). *)
(*     { extensionality st. admit. } *)
(*     solve [rewrite Heq; apply IHc1]. *)
(*   (* ite *) *)
(*   - simpl. *)
(*     assert (Heq: (fun st : St => infer_f_lib *)
(*                                 f m (compile (if e st then c1 else c2) st)) = *)
(*                  (fun st : St => if e st *)
(*                               then infer_f_lib f m (compile c1 st) *)
(*                               else infer_f_lib f m (compile c2 st))). *)
(*     { extensionality x; destruct (e x); reflexivity. } *)
(*     rewrite Heq. *)
(*     inversion Hwf; subst. *)
(*     constructor; auto. *)
(*   (* choice *) *)
(*   - simpl; inversion Hwf; subst. *)
(*     econstructor. *)
(*     apply IHc1 with (n:=m); auto. *)
(*     apply IHc2 with (n:=m); auto. *)
(*     intro st; simpl; field. *)
(*   (* while *) *)
(*   - admit. *)
(*   (* observe *) *)
(*   - simpl. *)
(*     assert (Heq: (fun st : St => *)
(*                     infer_f_lib f m (if e st then Leaf st else Fail St 0)) = *)
(*                  fun st => if e st then f st else 0). *)
(*     { extensionality st; destruct (e st); reflexivity. } *)
(*     rewrite Heq; constructor. *)

Admitted.

Theorem infer_correct (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  expectation f ->
  cwp c f (infer f ∘ evalCompile' c).
Proof.
  intros Hwf Hexp.
  eexists; eexists; split.
  - split.
    + apply wp_infer with (n:=O); auto.
    + apply wlp_infer with (n:=O); auto.
      compute; congruence.
  - reflexivity.
Qed.


(** Using CWP on example programs *)

Ltac rewrite_equiv :=
  match goal with
  | [ H : forall _ : St, _ == _ |- _ ] => rewrite H; simpl
  | [ H : _ ==f _ |- _ ] => rewrite H; simpl
  end.

Ltac wp_inversion :=
  match goal with
  | [ H : wp ?c ?f ?f' |- _ ] => inversion H; subst; clear H
  end;
  repeat rewrite_equiv.

Ltac wlp_inversion :=
  match goal with
  | [ H : wlp ?c ?f ?f' |- _ ] => inversion H; subst; clear H
  end;
  repeat rewrite_equiv.

Lemma goldfish_piranha_cwp (f : St -> Q) :
  cwp goldfish_piranha (fun st => if st O then 1 else 0) f -> f ==f const (2#3).
Proof.
  unfold goldfish_piranha, cwp.
  intros (f' & g' & [Hwp Hwlp] & Hf) x.
  repeat wp_inversion; repeat wlp_inversion.
  reflexivity.
Qed.

Fixpoint Qpow (x : Q) (n : nat) :=
  match n with
  | O => 1
  | S n' => x * Qpow x n'
  end.

Fixpoint geometric_series (a r : Q) (n : nat) :=
  match n with
  | O => a
  | S n' => geometric_series a r n' + a * Qpow r n
  end.

(* Definition sum_Q_list (l : list Q) : Q := *)
(*   fold_left Qplus l 0. *)

Definition geometric_series' (a r : Q) (n : nat) : Q :=
  sum_Q_list (map (fun n => a * Qpow r n) (seq O (S n))).

Lemma sum_Q_list_l (f : nat -> Q) (n m : nat) :
  f n + sum_Q_list (map f (seq (S n) m)) ==
  sum_Q_list (map f (seq n (S m))).
Proof. reflexivity. Qed.

Lemma sum_Q_list_r (f : nat -> Q) (n m : nat) :
  sum_Q_list (map f (seq n m)) + f (n + m)%nat ==
  sum_Q_list (map f (seq n (S m))).
Proof.
  revert n. induction m; intro n.
  - simpl. ring_simplify. rewrite plus_comm. reflexivity.
  - simpl in *.
    assert (n + (S m) = S n + m)%nat.
    { omega. }
    rewrite H.
    specialize (IHm (S n)).
    rewrite <- IHm; field.
Qed.

Lemma sum_Q_list_distr {A : Type} (l : list A) (f : A -> Q) (q : Q) :
  q * sum_Q_list (map f l) == sum_Q_list (map (fun x => q * f x) l).
Admitted.

Lemma geometric_series_geometric_series' (a r : Q) (n : nat) :
  geometric_series a r n == geometric_series' a r n.
Proof.
  unfold geometric_series'.
  induction n.
  - simpl; field.
  - simpl in *.
    rewrite IHn. ring_simplify.
    set (f := fun n => a * Qpow r n).
    assert (a == f O).
    { unfold f. simpl. field. }
    rewrite H.
    rewrite <- Qplus_assoc.
    rewrite sum_Q_list_l.
    rewrite Qplus_comm.
    simpl.
    assert (H0: f O * r * Qpow r n == f (1 + n)%nat).
    { unfold f. simpl. field. }
    rewrite H0.
    rewrite <- Qplus_assoc.
    rewrite sum_Q_list_r.
    unfold f. simpl. field.
Qed.


(* Eval compute in (Qred (geometric_series (2#9) (5#9) 10)). *)

Axiom geometric_series_converges :
  forall a r eps,
    0 <= a <= 1 -> 0 <= r -> r < 1 -> 0 < eps ->
    exists n0, forall n,
        (n0 <= n)%nat -> (a / (1 - r)) - geometric_series a r n < eps.

(* Definition prefix_series {A : Type} (n : nat) (f : nat -> A) (i : nat) := *)
(*   f (i-n)%nat. *)

(* Definition postfix_series {A : Type} (n : nat) (f : nat -> A) (i : nat) := *)
(*   f (i-n)%nat. *)

Lemma sum_Q_list_map_proper {A : Type} (l : list A) (f g : A -> Q) :
  f ==f g ->
  sum_Q_list (map f l) == sum_Q_list (map g l).
Proof.
  induction l; intro Heq; simpl; try field.
  - rewrite IHl; auto; rewrite Heq; reflexivity.
Qed.


Lemma geometric_series_fact (a r : Q) (n : nat) :
  a + r * geometric_series a r n == geometric_series a r (S n).
Proof.
  induction n.
  - simpl; field.
  - rewrite <- IHn. simpl.
    rewrite geometric_series_geometric_series'.
    unfold geometric_series'. simpl.
    ring_simplify.
    assert (Hpow: r^2 == Qpow r 2).
    { simpl. field. }
    rewrite Hpow.
    rewrite sum_Q_list_distr.
    assert (Hpow': (fun x => Qpow r 2 * (a * Qpow r x))
                   ==f (fun x => a * Qpow r (S (S x)))).
    { intro x. simpl. field. }
    rewrite sum_Q_list_map_proper; eauto.
    admit.
Admitted.

Lemma fair_coin_cwp (f : St -> Q) :
  cwp fair_coin (fun st => if st O then 1 else 0) f -> f ==f const (1#2).
Proof.
  unfold fair_coin.
  unfold cwp.
  intros (f' & g' & [Hwp Hwlp] & Hf).
  set (fx := fun st : St => if st O : bool then 1 else 0).
  repeat wp_inversion.
  repeat wlp_inversion.  
  intro x. rewrite Hf. unfold const.
  assert (forall i, ch0 i ==f const 1).
  { clear Hf H5 H6 H8 H1 H3 H7 H10 H13 f f' f'1 ch x g g'0 g0 g'1.
    intro i. induction i.
    - intro x; rewrite H2; reflexivity.
    - specialize (H9 i).
      destruct H9 as (g & Hwlp & H).
      repeat wlp_inversion.
      unfold const in *.
      intro st.
      assert (H9' := H9).
      specialize (H9 (upd O true st)).
      specialize (H9' (upd O false st)).
      specialize (H10 st).
      rewrite 2!IHi in H9.
      rewrite 2!IHi in H9'.
      rewrite H9 in H10.
      rewrite H9' in H10.
      rewrite H.
      destruct (eqb (st O) (st (S O))); try reflexivity.
      rewrite H10. field. }
  assert (infimum (const 1) ch0).
  { apply const_infimum; intro i; apply f_Qeq_equ; auto. }
  assert (Hf'1: f'1 ==f const 1).
  { apply f_Qeq_equ; eapply infimum_unique; eauto. }
  rewrite Hf'1.
  assert (supremum (fun st => if eqb (st O) (st (S O)) then 1#2 else fx st) ch).
  {
    split.
    - intros i st. unfold const; simpl.
      clear Hf. clear H6. clear H2. clear H5. clear H9.
      clear x. clear H0. clear Hf'1. clear H. clear H13. clear H8 g.
      clear ch0. revert st.
      induction i; intro st.
      + rewrite H1. unfold const, fx.
        destruct (st O); destruct (st (S O)); simpl; compute; congruence.
      + specialize (H3 i).
        destruct H3 as (g & Hwp & H).
        repeat wp_inversion.
        unfold const in H.
        rewrite H.
        assert (Hi0 := IHi (upd 1 true (upd 0 true st))).
        assert (Hi1 := IHi (upd 1 false (upd 0 true st))).
        assert (Hi2 := IHi (upd 1 true (upd 0 false st))).
        assert (Hi3 := IHi (upd 1 false (upd 0 false st))).
        unfold fx in *. simpl in *.
        destruct (st O) eqn:Hx; destruct (st (S O)) eqn:Hy; simpl in *; try lra;
        repeat rewrite_equiv; unfold const; lra.
    - intros ub Hub st.
      unfold upper_bound in Hub.
      simpl in *.
      unfold fx.
      assert (forall i, ch (S (S i)) ==f fun st => if eqb (st O) (st (S O))
                                           then geometric_series (2#9) (5#9) i
                                           else fx st).
      { clear Hf. clear H6. clear H2. clear H5. clear H9.
        clear x. clear H0. clear Hf'1. clear H.
        clear H13 ch0. revert st.
        clear Hub ub. clear H8 g.
        induction i; intro x.
        - simpl.
          assert (Hch1 := H3 O).
          specialize (H3 (S O)).
          destruct H3 as (g & Hwp & H3).
          rewrite H3.
          simpl.
          repeat wp_inversion.
          destruct Hch1 as (? & Hwp & Hch1).
          repeat wp_inversion.
          unfold const in *.
          unfold fx.
          destruct (x O); destruct (x (S O)); simpl; try reflexivity;
            repeat rewrite_equiv; rewrite Hch1; simpl;
              repeat rewrite_equiv; rewrite H1; reflexivity.
        - set (geom := geometric_series (2#9) (5#9) (S i)).
          simpl.
          destruct (H3 (S (S i))) as (g & Hwp & Hch).
          repeat wp_inversion.
          rewrite Hch. unfold const.
          clear Hch.
          unfold fx in *.
          destruct (x O); destruct (x (S O)); simpl;
            try rewrite 4!IHi; simpl; try reflexivity;
              unfold geom; rewrite <- geometric_series_fact;
                rewrite H8; repeat rewrite_equiv; field. }
      assert (Hle0: 0 <= 2#9 <= 1). lra.
      assert (Hle1: 0 <= 5#9). lra.
      assert (Hlt: 5#9 < 1). lra.
      destruct (st O) eqn:Hx; destruct (st (S O)) eqn:Hy; simpl.
      + assert (forall eps, 0 < eps -> exists n0, (1#2) - ch n0 st < eps).
        { intros eps Heps.
          generalize (@geometric_series_converges _ _ _ Hle0 Hle1 Hlt Heps).
          intros [n0 Hgeom].
          exists (S (S n0)).
          rewrite H4.
          rewrite Hx. rewrite Hy. simpl.
          specialize (Hgeom n0 (Nat.le_refl _)).
          assert (H': (2#9) / (1 - (5#9)) == 1#2).
          { reflexivity. }
          rewrite <- H'. apply Hgeom. }
        destruct (Qlt_le_dec (ub st) (1#2)); auto.
        * assert (H': 0 < (1#2) - ub st).
          { lra. }
          specialize (H11 ((1#2) - ub st) H').
          destruct H11 as [n0 H11].
          assert (ub st < ch n0 st).
          { lra. }
          specialize (Hub n0 st); lra.
      + specialize (Hub (S O) st).
        specialize (H3 O). clear H6 H8 g.
        destruct H3 as (g & Hwp & H3).
        rewrite H3 in Hub.
        rewrite Hx in Hub.
        rewrite Hy in Hub.
        apply Hub.
      + specialize (Hub O st). rewrite H1 in Hub. apply Hub.
      + assert (forall eps, 0 < eps -> exists n0, (1#2) - ch n0 st < eps).
        { intros eps Heps.
          generalize (@geometric_series_converges _ _ _ Hle0 Hle1 Hlt Heps).
          intros [n0 Hgeom].
          exists (S (S n0)).
          rewrite H4.
          rewrite Hx. rewrite Hy. simpl.
          specialize (Hgeom n0 (Nat.le_refl _)).
          assert (H': (2#9) / (1 - (5#9)) == 1#2).
          { reflexivity. }
          rewrite <- H'. apply Hgeom. }
        destruct (Qlt_le_dec (ub st) (1#2)); auto.
        * assert (H': 0 < (1#2) - ub st).
          { lra. }
          specialize (H11 ((1#2) - ub st) H').
          destruct H11 as [n0 H11].
          assert (ub st < ch n0 st).
          { lra. }
          specialize (Hub n0 st).
          lra. }
  rewrite H5. repeat rewrite_equiv. unfold const.
  assert (Hg0 : g0 ==f fun st => if eqb (st O) (st (S O)) then 1#2 else fx st).
  { apply f_Qeq_equ; eapply supremum_unique; eauto. }
  rewrite Hg0; reflexivity.
Qed.
