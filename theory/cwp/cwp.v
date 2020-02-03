Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Init.Nat.
Require Import PeanoNat.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Coq.micromega.Lqa.
Require Import Omega.
Require Import ExtLib.Structures.Monad.
Require Import FunctionalExtensionality.
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
| Fix : (nat -> tree A) -> tree A.

Fixpoint fmap {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf x => Leaf (f x)
  | Fail _ n => Fail _ n
  | Choice p t1 t2 => Choice p (fmap f t1) (fmap f t2)
  | Fix k => Fix (fmap f ∘ k)
  end.

Fixpoint join {A : Type} (t : tree (tree A)) : tree A :=
  match t with
  | Leaf t' => t'
  | Fail _ n => Fail _ n
  | Choice p t1 t2 => Choice p (join t1) (join t2)
  | Fix k => Fix (join ∘ k)
  end.

Definition tree_bind {A B : Type} (t : tree A) (k : A -> tree B) : tree B :=
  join (fmap k t).

Instance Monad_tree : Monad tree := { ret := Leaf; bind := @tree_bind }.

Definition kcomp {A B C : Type} (f : A -> tree B) (g : B -> tree C) : A -> tree C :=
  fun x => bind (f x) g.

Inductive wf_tree {A : Type} : tree A -> Prop :=
| wf_leaf : forall x, wf_tree (Leaf x)
| wf_fail : forall n, wf_tree (Fail _ n)
| wf_choice : forall p t1 t2,
    0 <= p <= 1 ->
    wf_tree t1 -> wf_tree t2 ->
    wf_tree (Choice p t1 t2)
| wf_fix : forall k,
    (forall n, wf_tree (k n)) ->
    wf_tree (Fix k).


(** Compiling cpGCL commands to trees *)
Fixpoint compile (c : cpGCL) : St -> tree St :=
  match c with
  | CSkip => @Leaf _
  | CAbort => fun st => Fix (Fail _)
  | CSeq c1 c2 => kcomp (compile c1) (compile c2)
  | CAssign x e => fun st => Leaf (upd x (e st) st)
  | CIte e c1 c2 => fun st => compile (if (e st) then c1 else c2) st
  | CChoice p c1 c2 => fun st => Choice p (compile c1 st) (compile c2 st)
  | CWhile e body =>
    fun st => Fix (fun n => bind (compile body st)
                           (fun st => if e st then Fail _ n else Leaf st))
  | CObserve e => fun st => if e st then Leaf st else Fail _ O
  end.


(** Inference on trees *)

Fixpoint infer_fail {A : Type} (n i : nat) (t : tree A) : Q :=
  match t with
  | Leaf _ => 0
  | Fail _ m => if m =? n then 1 else 0
  | Choice p t1 t2 => p * infer_fail n i t1 + (1-p) * infer_fail n i t2
  | Fix k =>
    let a := infer_fail n (S i) (k (S i)) in
    let b := infer_fail (S i) (S i) (k (S i)) in
    a / (1 - b)
  end.

Fixpoint infer_f {A : Type} (f : A -> Q) (i : nat) (t : tree A) : Q :=
  match t with
  | Leaf x => f x
  | Fail _ _ => 0
  | Choice p t1 t2 => p * infer_f f i t1 + (1-p) * infer_f f i t2
  | Fix k =>
    let a := infer_f f (S i) (k (S i)) in
    let b := infer_fail (S i) (S i) (k (S i)) in
    a / (1 - b)
  end.


Fixpoint infer_fail_lib {A : Type} (n i : nat) (t : tree A) : Q :=
  match t with
  | Leaf _ => 0
  | Fail _ m => if m =? n then 1 else 0
  | Choice p t1 t2 => p * infer_fail n i t1 + (1-p) * infer_fail n i t2
  | Fix k =>
    let a := infer_fail_lib n (S i) (k (S i)) in
    let b := infer_fail_lib (S i) (S i) (k (S i)) in
    if Qeq_bool b 1 then 1 else a / (1 - b)
  end.

Fixpoint infer_f_lib {A : Type} (f : A -> Q) (i : nat) (t : tree A) : Q :=
  match t with
  | Leaf x => f x
  | Fail _ _ => 0
  | Choice p t1 t2 => p * infer_f_lib f i t1 + (1-p) * infer_f_lib f i t2
  | Fix k =>
    let a := infer_f_lib f (S i) (k (S i)) in
    let b := infer_fail_lib (S i) (S i) (k (S i)) in
    if Qeq_bool b 1 then 1 else a / (1 - b)
  end.
  

Definition infer {A : Type} (f : A -> Q) (t : tree A) : Q :=
  let a := infer_f f O t in
  (* let b := infer_fail O O t in *)
  (* a / (1 - b). *)
  let b := infer_f_lib (const 1) O t in
  a / b.
  (* let b := infer_f (const 1) O t in *)
  (* a / b. *)

(* Lemma infer_fail_f_lib {A : Type} (f : A -> Q) (t : tree A) (n : nat) : *)
(*   1 - infer_fail O n t == infer_f_lib (const 1) n t. *)
(* Proof. *)
(*   revert f n. induction t; intros f m. *)
(*   - unfold const; simpl. reflexivity. *)
(*   - simpl. *)


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
  compile goldfish_piranha empty.

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             goldfish_piranha_tree)).

Definition test_abort : cpGCL :=
  CChoice (1#3) (CAssign 0%nat (const true)) CAbort.

Definition test_abort_tree : tree St := compile test_abort empty.

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             test_abort_tree)).
Eval compute in (Qred (infer (fun st => if negb (st O) then 1 else 0)
                             test_abort_tree)).
Eval compute in (Qred (infer (const 1) test_abort_tree)).

Eval compute in (Qred (infer_f (fun st => if st O : bool then 1 else 0) O test_abort_tree)).
Eval compute in (Qred (infer_f (const 1) O (compile (CChoice (1#2) CSkip CAbort) empty))).

Definition fair_coin : cpGCL :=
  CAssign 0 (const false) ;;
  CAssign 1 (const false) ;;
  CWhile (fun st => eqb (st 0%nat) (st 1%nat))
         (sample 0%nat (1#3) ;; sample 1%nat (1#3)).

Definition fair_coin_tree : tree St := compile fair_coin empty.

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

Definition fair_coin_loop_tree : tree St := compile fair_coin_loop empty.

Eval compute in (Qred (infer (fun st => if st O : bool then 1 else 0)
                             fair_coin_loop_tree)).


(** Relational specification of weakest pre-expectation semantics *)
Inductive wp : cpGCL -> (St -> Q) -> (St -> Q) -> Prop :=
| wp_skip : forall f, wp CSkip f f
| wp_abort : forall f, wp CAbort f (const 0)
| wp_assign : forall x e f,
    wp (CAssign x e) f (fun st => f (upd x (e st) st))
| wp_seq : forall c1 c2 f f' f'',
    wp c2 f f' ->
    wp c1 f' f'' ->
    wp (CSeq c1 c2) f f''
| wp_ite : forall e c1 c2 f g h,
    wp c1 f g ->
    wp c2 f h ->
    wp (CIte e c1 c2) f (fun st => if e st then g st else h st)
| wp_choice : forall p c1 c2 f g h,
    wp c1 f g ->
    wp c2 f h ->
    wp (CChoice p c1 c2) f (fun st => p * g st + (1-p) * h st)
| wp_while : forall e body f f' ch,
    ch O = const 0 ->
    (forall n, exists g, wp body (ch n) g /\
               ch (S n) = fun st => if e st : bool then g st else f st) ->
    supremum f' ch ->
    wp (CWhile e body) f f'
| wp_observe : forall e f,
    wp (CObserve e) f (fun st => if e st then f st else 0).


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

Ltac wp_inversion :=
  match goal with
  | [ H : wp ?c ?f ?f' |- _ ] => inversion H; subst; clear H
  end.

Ltac wlp_inversion :=
  match goal with
  | [ H : wlp ?c ?f ?f' |- _ ] => inversion H; subst; clear H
  end.


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

Lemma wf_tree_bind {A B : Type} (t : tree A) (k : A -> tree B) :
  wf_tree t ->
  (forall x, wf_tree (k x)) ->
  wf_tree (tree_bind t k).
Proof.
  unfold tree_bind. revert k.
  induction t; intros k Hwf_t Hwf_k; simpl; auto.
  - constructor.
  - inversion Hwf_t; subst.
    constructor; auto.
  - constructor.
    intro n. unfold compose.
    inversion Hwf_t; subst.
    apply H; auto.
Qed.

Lemma compile_wf (c : cpGCL) :
  wf_cpGCL c ->
  (forall st, wf_tree (compile c st)).
Proof.
  induction c; intros Hwf st; try solve [repeat constructor].
  - inversion Hwf; subst.
    apply wf_tree_bind; auto.
  - simpl; inversion Hwf; subst.
    destruct (e st); auto.
  - simpl; inversion Hwf; subst.
    constructor; auto.
  - simpl. constructor.
    intro n.
    inversion Hwf; subst.
    apply wf_tree_bind; auto.
    intro x.  destruct (e x); constructor.
  - simpl. destruct (e st); constructor.
Qed.

(* Lemma wp_deterministic (c : cpGCL) (f f' f'' : St -> Q) : *)
(*   wp c f f' -> wp c f f'' -> f' ==f f''. *)
(* Proof. *)
(*   revert f f' f''. *)
(*   induction c; intros f f' f'' Hwp0 Hwp1; *)
(*     try solve [inversion Hwp0; inversion Hwp1; subst; apply f_Qeq_refl]. *)
(*   - inversion Hwp0; inversion Hwp1; subst. *)
(*     (* IH not strong enough for seq case. Need to loosen it to *)
(*        equivalence of input functions instead of equality.  *) *)
(* Admitted. *)

(* Lemma wlp_deterministic (c : cpGCL) (f f' f'' : St -> Q) : *)
(*   wlp c f f' -> wlp c f f'' -> f' ==f f''. *)
(* Admitted. *)

(* Lemma cwp_deterministic (c : cpGCL) (f f' f'' : St -> Q) : *)
(*   cwp c f f' -> cwp c f f'' -> f' ==f f''. *)
(* Admitted. *)


(* Lemma jksfdg {A B : Type} (f : B -> Q) (t : nat -> tree A) (k : A -> tree B) (n m : nat) : *)
(*   infer_f f n (join (fmap k (t m))) = infer_f f (S n) (join (fmap k (t (S n)))). *)
(* Proof. *)
(*   revert t k f m. *)
(*   induction n; intros t k f m. *)
(*   - simpl. *)

(* Lemma jksfdg {A : Type} (f : A -> Q) (t1 t2 : tree A) (n : nat) : *)
(*   (* t1 and t2 are alpha equivalent *) *)
(*   (* all fvs of t1 and t2 are <= n *) *)
(*   infer_f f n t1 = infer_f f n t2. *)
(* Proof. *)
(*   revert t k f m. *)
(*   induction n; intros t k f m. *)
(*   - simpl. *)

Lemma infer_f_bind {A B : Type} (f : B -> Q) (t1 : tree A) (k : A -> tree B) (n m : nat) :
  infer_f (infer_f f n ∘ k) m t1 = infer_f f n (tree_bind t1 k).
Proof.
  revert f k n m.
  induction t1; intros f k m m'; try reflexivity.
  - simpl in *. rewrite IHt1_1, IHt1_2. reflexivity.
  - simpl.
    rewrite H. unfold tree_bind, compose.
    f_equal.
    +      


      admit.
    + f_equal.
      
    (* unfold tree_bind in H. *)
    (* unfold compose. *)
    (* erewrite <- H. *)
    (* specialize (H (S m') f k m (S m')). *)
    (* (* unfold tree_bind, compose in H. *) *)
    (* rewrite H. clear H. *)
    (* unfold tree_bind. unfold compose. *)
Admitted.


Lemma infer_f_expectation {A : Type} (f : A -> Q) (t : tree A) (n : nat) :
  wf_tree t ->
  expectation f ->
  0 <= infer_f f n t.
Proof.
  revert f n. induction t; intros f m Hwf Hexp.
  - simpl; apply Hexp.
  - apply Qle_refl.
  - simpl.
    inversion Hwf; subst.
    specialize (IHt1 f m H3 Hexp).
    specialize (IHt2 f m H4 Hexp).
    nra.
  - simpl.
    inversion Hwf.
    specialize (H (S m) f (S m) (H1 _) Hexp).
    assert (infer_fail (S m) (S m) (t (S m)) <= 1).
    { admit. }
    subst.
    assert (0 <= 1 - infer_fail (S m) (S m) (t (S m))).
    { lra. }
    apply Qle_lt_or_eq in H0.
    destruct H0.
    + apply Qle_shift_div_l; auto; lra.
    + rewrite <- H0. apply Qle_lteq.
      right. simpl.
      admit.
Admitted.


Theorem wp_infer (c : cpGCL) (f : St -> Q) (n : nat) :
  wf_cpGCL c ->
  expectation f ->
  wp c f (infer_f f n ∘ compile c).
Proof.
  revert f n. induction c; intros f m Hwf Hexp; try solve [constructor].
  (* abort *)
  - unfold compose. simpl. rewrite Nat.eqb_refl.
    assert (0 / (1 - 1) = 0).
    { reflexivity. }
    rewrite H; constructor.
    (* sequence *)
  - unfold compose. simpl.
    inversion Hwf; subst.
    specialize (IHc2 f m H2 Hexp).
    econstructor. apply IHc2; auto.
    set (f2 := infer_f f m ∘ compile c2).
    set (f1 := infer_f f2 m ∘ compile c1).
    set (g := fun x : St => infer_f f m (kcomp (compile c1) (compile c2) x)).
    (* assert (f1 ==f g). *)
    (* { intro x; apply infer_f_bind. } *)
    assert (f1 = g).
    { extensionality st; apply infer_f_bind. }
    rewrite <- H.
    apply IHc1; auto.
    unfold f2.
    intro x. unfold compose. 
    unfold compose in f2. unfold f2.
    apply infer_f_expectation; auto.
    apply compile_wf; auto.
  (* ite *)
  - unfold compose; simpl.
    set (fi := infer_f f).
    assert ((fun x : St => fi m (compile (if e x then c1 else c2) x)) =
            (fun x => if e x then fi m (compile c1 x) else fi m (compile c2 x))).
    { extensionality x; destruct (e x); reflexivity. }
    rewrite H.
    inversion Hwf; subst.
    constructor.
    apply IHc1; auto.
    apply IHc2; auto.
  (* choice *)
  - unfold compose; simpl.
    inversion Hwf; subst.
    econstructor.
    apply IHc1 with (n:=m); auto.
    apply IHc2 with (n:=m); auto.
  (* while *)
  -
    (* econstructor. *)
    (* Need to provide a chain of approximations that satisfies the
       conditions of the while wp constructor, and such that infer
       after compile yields of the supremum of that chain (probably
       via an argument based on convergence of geometric series). *)
    
    admit.
  (* observe *)
  - unfold compose; simpl.
    assert ((fun x : St =>
               infer_f f m (if e x then Leaf x else Fail St 0)) =
            (fun x => if e x then f x else 0)).
    { extensionality x; destruct (e x); reflexivity. }
    solve [rewrite H; constructor].
Admitted.

Theorem wlp_infer (c : cpGCL) (f : St -> Q) (n : nat) :
  wf_cpGCL c ->
  expectation f ->
  wlp c f (fun st => infer_f_lib f n (compile c st)).
  (* wlp c (const 1) (fun st => 1 - infer_fail O n (compile c st)). *)
Proof.
  revert f n. induction c; intros f m Hwf Hexp; try solve [constructor].
  (* abort *)
  - simpl; rewrite Nat.eqb_refl; constructor.
  (* sequence *)
  - simpl.
    inversion Hwf; subst.
    econstructor.
    apply IHc2 with (n:=m); auto.
    assert (Hexp': expectation ((fun st : St => infer_f_lib f m (compile c2 st)))).
    { admit. }
    specialize (IHc1 _ m H1 Hexp').
    assert (Heq: (fun st : St => infer_f_lib
                                f m (kcomp (compile c1) (compile c2) st)) =
                 (fun st : St =>
                    infer_f_lib
                      (fun st0 : St => infer_f_lib f m (compile c2 st0))
                      m (compile c1 st))).
    { extensionality st. admit. }
    solve [rewrite Heq; apply IHc1].
  (* ite *)
  - simpl.
    assert (Heq: (fun st : St => infer_f_lib
                                f m (compile (if e st then c1 else c2) st)) =
                 (fun st : St => if e st
                              then infer_f_lib f m (compile c1 st)
                              else infer_f_lib f m (compile c2 st))).
    { extensionality x; destruct (e x); reflexivity. }
    rewrite Heq.
    inversion Hwf; subst.
    constructor; auto.
  (* choice *)
  - simpl; inversion Hwf; subst.
    econstructor.
    apply IHc1 with (n:=m); auto.
    apply IHc2 with (n:=m); auto.
    intro st; simpl; field.
  (* while *)
  - admit.
  (* observe *)
  - simpl.
    assert (Heq: (fun st : St =>
                    infer_f_lib f m (if e st then Leaf st else Fail St 0)) =
                 fun st => if e st then f st else 0).
    { extensionality st; destruct (e st); reflexivity. }
    rewrite Heq; constructor.
Admitted.

Theorem infer_correct (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  expectation f ->
  cwp c f (infer f ∘ compile c).
Proof.
  intros Hwf Hexp.
  eexists. eexists. split.
  - split.
    + apply wp_infer with (n:=O); auto.
    + apply wlp_infer with (n:=O); auto.
      compute; congruence.
  - reflexivity.
Qed.


(** Using CWP on example programs *)

Lemma goldfish_piranha_cwp (f : St -> Q) :
  cwp goldfish_piranha (fun st => if st O then 1 else 0) f -> f ==f const (2#3).
Proof.
  unfold goldfish_piranha, cwp.
  intros (f' & g' & [Hwp Hwlp] & Hf).
  repeat wp_inversion; repeat wlp_inversion.
  simpl in *; unfold const in *.
  intro x; rewrite Hf; rewrite H8; rewrite 2!H9.
  compute; reflexivity.
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

(* Eval compute in (Qred (geometric_series (2#9) (5#9) 10)). *)

Axiom geometric_series_converges :
  forall a r eps,
    0 <= a <= 1 -> 0 <= r -> r < 1 -> 0 < eps ->
    exists n0, forall n,
        (n0 <= n)%nat -> (a / (1 - r)) - geometric_series a r n < eps.

Lemma geometric_series_fact (a r : Q) (n : nat) :
  a + r * geometric_series a r n == geometric_series a r (S n).
Proof.
  induction n.
  - simpl; field.
  - rewrite <- IHn.
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
  { clear Hf. clear H3. clear H6. clear H1. clear ch.
    clear H9. clear x. clear f f' f'1.
    intro i. induction i.
    - intro x; rewrite H2; reflexivity.
    - specialize (H5 i).
      destruct H5 as (g & Hwlp & H).
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
      clear x. clear H0. clear Hf'1. clear H.
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
        destruct (st O) eqn:Hx; destruct (st (S O)) eqn:Hy; simpl in *; try lra.
    - intros ub Hub st.
      unfold upper_bound in Hub.
      simpl in *.
      unfold fx.

      assert (forall i, ch (S (S i)) ==f fun st => if eqb (st O) (st (S O))
                                           then geometric_series (2#9) (5#9) i
                                           else fx st).
      { clear Hf. clear H6. clear H2. clear H5. clear H9.
        clear x. clear H0. clear Hf'1. clear H.
        clear ch0. revert st.
        clear Hub ub.
        induction i; intro x.
        - simpl.
          assert (Hch1 := H3 O).
          specialize (H3 (S O)).
          destruct H3 as (g & Hwp & H3).
          rewrite H3.
          simpl.
          repeat wp_inversion.          
          destruct Hch1 as (g & Hwp & Hch1).
          repeat wp_inversion.
          unfold const in *.
          rewrite Hch1. unfold fx. simpl. rewrite H1.
          destruct (x O); destruct (x (S O)); reflexivity.
        - set (geom := geometric_series (2#9) (5#9) (S i)).
          simpl.
          destruct (H3 (S (S i))) as (g & Hwp & Hch).
          repeat wp_inversion.
          rewrite Hch. unfold const.
          clear Hch.
          unfold fx in *.
          destruct (x O); destruct (x (S O)); simpl; try rewrite 4!IHi; simpl.
          + unfold geom. rewrite <- geometric_series_fact. simpl. field.
          + reflexivity.
          + reflexivity.
          + simpl.
            unfold geom. rewrite <- geometric_series_fact. field. }

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
          assert (H7: (2#9) / (1 - (5#9)) == 1#2).
          { reflexivity. }
          rewrite <- H7. apply Hgeom. }
        destruct (Qlt_le_dec (ub st) (1#2)); auto.
        * assert (0 < (1#2) - ub st).
          { lra. }
          specialize (H7 ((1#2) - ub st) H8).
          destruct H7 as [n0 H7].
          assert (ub st < ch n0 st).
          { lra. }
          specialize (Hub n0 st).
          lra.
      + specialize (Hub (S O) st).
        specialize (H3 O).
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
          assert (H7: (2#9) / (1 - (5#9)) == 1#2).
          { reflexivity. }
          rewrite <- H7. apply Hgeom. }
        destruct (Qlt_le_dec (ub st) (1#2)); auto.
        * assert (0 < (1#2) - ub st).
          { lra. }
          specialize (H7 ((1#2) - ub st) H8).
          destruct H7 as [n0 H7].
          assert (ub st < ch n0 st).
          { lra. }
          specialize (Hub n0 st).
          lra. }
  assert (Hf' : f' ==f fun st => if eqb (st O) (st (S O)) then 1#2 else fx st).
  { apply f_Qeq_equ; eapply supremum_unique; eauto. }
  rewrite Hf'; reflexivity.
Qed.
