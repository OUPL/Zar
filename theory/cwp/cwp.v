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
  ; prog_query : exp
  }.

Notation "a ';;' b" := (CSeq a b) (at level 100, right associativity) : cpGCL_scope.
Open Scope cpGCL_scope.


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


(** Compiling cpGCL commands to trees *)
Fixpoint compile (c : cpGCL) : St -> tree St :=
  match c with
  | CSkip => @Leaf _
  | CAbort => fun st => Fix (fun n => Fail _ n)
  | CSeq c1 c2 => kcomp (compile c1) (compile c2)
  | CAssign x e => fun st => Leaf (upd x (e st) st)
  | CIte e c1 c2 => fun st => compile (if (e st) then c1 else c2) st
  | CChoice p c1 c2 => fun st => Choice p (compile c1 st) (compile c2 st)
  | CWhile e body =>
    fun st => Fix (fun n => bind (compile body st)
                           (fun st => if e st then Fail _ n else Leaf st))
  | CObserve e => fun st => if e st then Leaf st else Fail _ O
  end.


(** Inference on trees*)
Fixpoint infer_aux {A : Type} (f : tree A -> Q) (n : nat) (t : tree A) : Q :=
  match t with
  | Choice p t1 t2 => p * infer_aux f n t1 + (1-p) * infer_aux f n t2
  | Fix k =>
    let a := infer_aux f (S n) (k (S n)) in
    let b := infer_aux (fun t' => match t' with
                               | Fail _ m => if Nat.eqb m (S n) then 1 else 0
                               | _ => 0
                               end) (S n) (k (S n)) in
    a / (1 - b)
  | _ => f t
  end.

Definition infer {A : Type} (f : A -> Q) (t : tree A) : Q :=
  let a := infer_aux (fun t' => match t' with
                             | Leaf x => f x
                             | _ => 0
                             end) O t in
  let b := infer_aux (fun t' => match t' with
                             | Fail _ O => 1
                             | _ => 0
                             end) O t in
  a / (1 - b).


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
               ch (S n) = fun st => if e st : bool then f st else g st) ->
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
| wlp_choice : forall p c1 c2 f g h,
    wlp c1 f g ->
    wlp c2 f h ->
    wlp (CChoice p c1 c2) f (fun st => p * g st + (1-p) * h st)
| wlp_while : forall e body f f' ch,
    ch O = const 1 ->
    (forall n, exists g, wlp body (ch n) g /\
               ch (S n) = fun st => if e st : bool then f st else g st) ->
    infimum f' ch ->
    wlp (CWhile e body) f f'
| wlp_observe : forall e f,
    wlp (CObserve e) f (fun st => if e st then f st else 0).

(** cwp_ is decomposed into wp and wlp *)
Definition cwp_ (c : cpGCL) (f f' g g' : St -> Q) :=
  wp c f f' /\ wlp c g g'.

(** cwp is the ratio of the pair given by cwp_ *)
Definition cwp (c : cpGCL) (f f'' : St -> Q) :=
  exists f' g', cwp_ c f f' (const 1) g' /\ f'' = fun st => f' st / g' st.

(* (** Relational specification of CWP semantics *) *)
(* Inductive cwp_ : cpGCL -> (St -> Q) -> (St -> Q) -> (St -> Q) -> (St -> Q) -> Prop := *)
(* | cwp_skip : forall f g, cwp_ CSkip f g f g *)
(* | cwp_assign : forall x e f g, *)
(*     cwp_ (CAssign x e) f g *)
(*          (fun st => f (upd x (e st) st)) *)
(*          (fun st => g (upd x (e st) st)) *)
(* | cwp_seq : forall c1 c2 f f' f'' g g' g'', *)
(*     cwp_ c2 f g f' g' -> *)
(*     cwp_ c1 f' g' f'' g'' -> *)
(*     cwp_ (CSeq c1 c2) f g f'' g'' *)
(* | cwp_ite : forall e c1 c2 f f' f'' g g' g'', *)
(*     cwp_ c1 f g f' g' -> *)
(*     cwp_ c2 f g f'' g'' -> *)
(*     cwp_ (CIte e c1 c2) f g *)
(*          (fun st => if e st then f' st else f'' st) *)
(*          (fun st => if e st then g' st else g'' st) *)
(* | cwp_choice : forall p c1 c2 f f' f'' g g' g'', *)
(*     cwp_ c1 f g f' g' -> *)
(*     cwp_ c2 f g f'' g'' -> *)
(*     cwp_ (CChoice p c1 c2) f g *)
(*          (fun st => p * f' st + (1-p) * f'' st) *)
(*          (fun st => p * g' st + (1-p) * g'' st) *)
(* | cwp_while : forall c f g f' g', *)
(*     lfp f' (fun f_hat => f_hat) -> *)
(*     cwp_ c f g f' g' *)
(* | cwp_observe : forall e f g, *)
(*     cwp_ (CObserve e) f g *)
(*          (fun st => if e st then f st else 0) *)
(*          (fun st => if e st then g st else 0). *)

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
| wf_choice : forall p c1 c2,
    0 <= p <= 1 -> wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CChoice p c1 c2)
| wf_while : forall e body, wf_cpGCL body -> wf_cpGCL (CWhile e body)
| wf_observe : forall e, wf_cpGCL (CObserve e).

(** f is an expectation *)
Definition expectation {A : Type} (f : A -> Q) :=
  forall x, 0 <= f x.

Lemma Qle_Qdiv_1 (x : Q) :
  x == x / 1.
Proof. field. Qed.

(* Maybe decompose this into proofs wrt wp and wlp *)
Lemma cwp_expectation (c : cpGCL) (f f'' : St -> Q) :
  expectation f ->
  cwp c f f'' ->
  expectation f''.
Proof.
  revert f f''.
  unfold expectation.  
  induction c; intros f f'' Hexp (f' & g' & [Hcwp0 Hcwp1] & Hcwp2) x.
  - inversion Hcwp0; subst. inversion Hcwp1; subst.
    unfold const. specialize (Hexp x).
    eapply Qle_trans; eauto.
    rewrite <- Qle_Qdiv_1; apply Qle_refl.
  - inversion Hcwp0; subst. inversion Hcwp1; subst.
    unfold const. compute; congruence.
  - inversion Hcwp0; subst. inversion Hcwp1; subst.
    unfold const.
    apply Qle_trans with (y := f (upd n (e x) x)); auto.
    rewrite <- Qle_Qdiv_1; apply Qle_refl.
  - inversion Hcwp0; subst. inversion Hcwp1; subst.
    admit.
  - admit.
  - admit.
  - inversion Hcwp0; subst. inversion Hcwp1; subst.
    admit.
  - inversion Hcwp0; subst. inversion Hcwp1; subst.
    destruct (e x).
    + eapply Qle_trans; eauto.
      rewrite <- Qle_Qdiv_1; apply Qle_refl.
    + compute; congruence.
Admitted.

Lemma wp_deterministic (c : cpGCL) (f f' f'' : St -> Q) :
  wp c f f' -> wp c f f'' ->
  f' = f''.
Proof.
  revert f  f' f''.
  induction c; intros f f' f'' Hwp0 Hwp1.
  - inversion Hwp0; subst; inversion Hwp1; subst; reflexivity.
  - inversion Hwp0; subst; inversion Hwp1; subst; reflexivity.
  - inversion Hwp0; subst; inversion Hwp1; subst; reflexivity.
  - inversion Hwp0; subst; inversion Hwp1; subst.
    eapply IHc2 in H1; eauto; subst.
    eapply IHc1 in H4; eauto.
  - inversion Hwp0; subst; inversion Hwp1; subst.
    eapply IHc1 in H4; eauto; subst.
    eapply IHc2 in H5; eauto; subst.
    reflexivity.
  - inversion Hwp0; subst; inversion Hwp1; subst.
    eapply IHc1 in H4; eauto; subst.
    eapply IHc2 in H5; eauto; subst.
    reflexivity.
  - 
    inversion Hwp0; subst; inversion Hwp1; subst.
    assert (ch = ch0).
    { admit. }
    subst.
    generalize (supremum_unique f' f'' ch0 H5 H8).
    unfold equ. simpl.
    intros [Hleq0 Hleq1].
    extensionality st.
    admit. (* Need to use Qeq instead of definitional equality -_- *)
  - inversion Hwp0; subst; inversion Hwp1; subst; reflexivity.
Admitted.

(* Lemma fair_coin_cwp : *)
(*   cwp fair_coin (fun st => if st O then 1 else 0) (const (1#2)). *)

(** Probably need to quantify over possible solutions and say that
    they are equivalent to 1/2 (Qeq).*)
Lemma fair_coin_cwp :
  cwp fair_coin (fun st => if st O then 1 else 0) (const (1#2)).
Proof.
  unfold fair_coin.
  unfold cwp.
  eexists. eexists.
  unfold cwp_. split. split.
  - econstructor.
    + econstructor.
      * admit.
      * econstructor.
    + econstructor.
  - econstructor.
    + econstructor.
      * admit.
      * econstructor.
    + econstructor.
  - 
    extensionality st. unfold const.
    admit.
Admitted.


(** Main theorem establishing correctness of compilation+inference
    wrt. CWP semantics. *)
Theorem cwp_infer (c : cpGCL) (f f' : St -> Q) :
  wf_cpGCL c ->
  expectation f ->
  cwp c f f' <-> forall st, infer f (compile c st) == f' st.
Admitted.
