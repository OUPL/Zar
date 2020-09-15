Set Implicit Arguments.

(* To install ITree, do:
     opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.

(* From stdpp Require Import tactics. *)

Require Import Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Logic.Eqdep_dec.
(* Require Import List. *)
(* Import ListNotations. *)
Local Open Scope program_scope.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.

Require Import axioms.
Require Import cpGCL.
Require Import infer.
Require Import borel.
Require Import Q.
Require Import tree.

(** A biased coin event can be raised, passing a rational p to the
  environment and receiving in return a single bit with probability p
  of being 1. *)
Variant biasedE : Type -> Type :=
| GetBiased : Q -> biasedE bool.
(* | GetBiased : forall p : Q, 0 <= p <= 1 -> biasedE bool. *)

Variant unbiasedE : Type -> Type :=
| GetUnbiased : unbiasedE bool.


(** Commands to itrees directly. *)

Fixpoint compile_itree (c : cpGCL) : ktree biasedE St (unit + St) :=
  match c with
  | CSkip => ret ∘ inr
  | CAbort => (const ∘ ret ∘ inl) tt
  | CAssign n e => fun st => ret (inr (upd n (e st) st))
  | CSeq c1 c2 =>
    fun st => x <- compile_itree c1 st ;;
           match x with
           | inl tt => ret (inl tt)
           | inr st' => compile_itree c2 st'
           end
  | CIte e c1 c2 =>
    fun st => if e st then compile_itree c1 st else compile_itree c1 st
  | CChoice p c1 c2 =>
    fun st => Vis (GetBiased p) (fun b => if b : bool
                                 then compile_itree c1 st
                                 else compile_itree c2 st)
  | CWhile e body =>
    fun st => Basics.iter (map (fun x =>
                               match x with
                               | inl tt => inr (inl tt)
                               | inr st' =>
                                 if e st' then inl st else inr (inr st')
                               end) (compile_itree body)) st
  | CObserve e => fun st => if e st then ret (inr st) else ret (inl tt)
  end.

Import MonadNotation.
Local Open Scope monad_scope.

Fixpoint tree_to_sampler {A : Type}
         (f : nat -> bool) (t : tree A) (env : nat -> tree A) (n : nat)
  : state nat (unit + A) :=
  match n with
  | O => ret (inl tt)
  | S n' =>
    match t with
    | Leaf x => ret (inr x)
    | Fail _ lbl => tree_to_sampler f (env lbl) env n'
    | Choice _ t1 t2 =>
      i <- get ;;
      put (S i) ;;
      tree_to_sampler f (if f i then t1 else t2) env n'
    | Fix lbl t1 =>
      tree_to_sampler f t1 (fun m => if m =? lbl then t1 else env m) n'
    end
  end.

Definition tree_to_sampler' {A : Type} (f : nat -> bool) (t : tree A) (n : nat)
  : state nat (unit + A) :=
  tree_to_sampler f t (const (Fail _ O)) n.


Definition tie_itree {A : Type} (k : ktree biasedE A (unit + A))
  : ktree biasedE A A :=
  fun x => Basics.iter (map (fun y => match y with
                                | inl tt => inl x
                                | inr x' => inr x'
                                end) k) x.

Definition compile_itree' (c : cpGCL) : ktree biasedE St St :=
  tie_itree (compile_itree c).


(** Inductive trees to itrees. *)

Definition diverge {E : Type -> Type} {A : Type} : itree E A :=
  Basics.iter (ret ∘ inl) tt.

Fixpoint tree_to_itree {A : Type} (t : tree A) : itree biasedE (nat + A) :=
  match t with
  | Leaf x => ret (inr x)
  | Fail _ lbl => ret (inl lbl)
  | Choice p t1 t2 =>
    Vis (GetBiased p) (fun b => if b : bool
                             then tree_to_itree t2
                             else tree_to_itree t1)
  | Fix lbl t1 => Basics.iter (fun _ => x <- tree_to_itree t1 ;;
                                    match x with
                                    | inl n =>
                                      if n =? lbl
                                      then ret (inl tt)
                                      else ret (inr (inl n))
                                    | inr y =>
                                      ret (inr (inr y))
                                    end) tt
  end.

Definition tie_itree' {A : Type} {E : Type -> Type} (t : itree E (nat + A)) 
  : itree E A :=
  Basics.iter (fun _ => x <- t ;;
                     match x with
                     | inl _ => ret (inl tt)
                     | inr y => ret (inr y)
                     end) tt.

Definition tree_to_itree' {A : Type} (t : tree A) : itree biasedE A :=
  tie_itree' (tree_to_itree t).

(** [sample t P bs] means that itree [t] produces a sample in [P]
    given [bs] as input. We require that [bs] be nil at leaf nodes so
    that any two distinct bit sequence that produce samples represent
    disjoint intervals. *)
Inductive sample {A : Type} :
  itree unbiasedE A -> (A -> Prop) -> list bool -> Prop :=
| sample_ret : forall t (P : A -> Prop) x,
    observe t = RetF x ->
    P x ->
    sample t P nil
| sample_tau : forall t t' P bs,
    observe t = TauF t' ->
    sample t' P bs ->
    sample t P bs
| sample_vis_false : forall t t1 bs P k,
    observe t = VisF GetUnbiased k ->
    k false = t1 ->
    sample t1 P bs ->
    sample t P (false :: bs)
| sample_vis_true : forall t t2 bs P k,
    observe t = VisF GetUnbiased k ->
    k true = t2 ->
    sample t2 P bs ->
    sample t P (true :: bs).

(** Step-indexed version of [sample]. [sample_n t P bs n] means that
  itree [t] produces a sample in [P] given [bs] as input in at most
  [n] steps. *)
Inductive sample_n {A : Type} :
  itree unbiasedE A -> (A -> Prop) -> list bool -> nat -> Prop :=
| sample_n_ret : forall t (P : A -> Prop) x n,
    observe t = RetF x ->
    P x ->
    sample_n t P nil n
| sample_n_tau : forall t t' P bs n,
    observe t = TauF t' ->
    sample_n t' P bs n ->
    sample_n t P bs (S n)
| sample_n_vis_false : forall t t1 bs P n k,
    observe t = VisF GetUnbiased k ->
    k false = t1 ->
    sample_n t1 P bs n ->
    sample_n t P (false :: bs) (S n)
| sample_n_vis_true : forall t t2 bs P n k,
    observe t = VisF GetUnbiased k ->
    k true = t2 ->
    sample_n t2 P bs n ->
    sample_n t P (true :: bs) (S n).

Definition sample_sample_n {A : Type}
           (t : itree unbiasedE A) (P : A -> Prop) (bs : list bool) :
  sample t P bs <-> exists n, sample_n t P bs n.
Proof.
  split.
  - induction 1.
    + exists O; eapply sample_n_ret; eauto.
    + destruct IHsample as [n IH].
      exists (S n); eapply sample_n_tau; eauto.
    + destruct IHsample as [n IH].
      exists (S n); eapply sample_n_vis_false; eauto.
    + destruct IHsample as [n IH].
      exists (S n); eapply sample_n_vis_true; eauto.
  - intros [n Hsample].
    induction Hsample.
    + eapply sample_ret; eauto.
    + eapply sample_tau; eauto.
    + eapply sample_vis_false; eauto.
    + eapply sample_vis_true; eauto.
Qed.

(** The preimage of a set of samples [P] wrt itree [t] is the set of
    bit sequences [bs] such that [sample t bs P]. *)
Definition preimage {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
  : list bool -> Prop :=
  sample t P.


(* Definition preimage' {A : Type} (t : itree unbiasedE A) (P : A -> Prop) *)
(*   : list bool -> Prop := *)
(*   fun bs => exists n, sample_n t P bs n. *)

Require Import List.
Import ListNotations.
Require Import Nat.

Fixpoint sample_nb {A : Type}
         (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) (n : nat) : bool :=
  match n with
  | O =>
    match observe t with
    | RetF x =>
      match bs with
      | [] => P x
      | _ => false
      end
    | _ => false
    end
  | S n' =>
    match observe t with
    | RetF x =>
      match bs with
      | [] => P x
      | _ => false
      end
    | TauF t' => sample_nb t' P bs n'
    | VisF e k =>
      match e in unbiasedE T return (T -> itree unbiasedE A) -> bool with
      | GetUnbiased =>
        fun f => match bs with
              | [] => false
              | b :: bs' => sample_nb (f b) P bs' n'
              end
      end k
    end
  end.

Lemma VisF_inversion {A B : Type} e (f g : bool -> itree unbiasedE B) :
  @VisF unbiasedE A (itree unbiasedE B) bool e f =
  @VisF unbiasedE A (itree unbiasedE B) bool e g ->
  f = g.
Proof.
  intro Heq; inversion Heq.
  apply inj_pair2 in H0; auto.
Qed.

Lemma sample_nb_spec {A : Type}
      (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) (n : nat)
  : reflect (sample_n t P bs n) (sample_nb t P bs n).
Proof.
  revert t bs.
  induction n; intros t bs; simpl.
  - destruct (observe t) eqn:Ht.
    + destruct (P r) eqn:HP; destruct bs; constructor.
      * econstructor; eauto.
      * intro HC; inversion HC.
      * intro HC; inversion HC; congruence.
      * intro HC; inversion HC; congruence.
    + constructor; intro HC; inversion HC; congruence.
    + constructor; intro HC; inversion HC; congruence.
  - destruct (observe t) eqn:Ht.
    + destruct (P r) eqn:HP; destruct bs; constructor.
      * econstructor; eauto.
      * intro HC; inversion HC; congruence.
      * intro HC; inversion HC; congruence.
      * intro HC; inversion HC; congruence.
    + destruct (IHn t0 bs); constructor.
      * econstructor; eauto.
      * intro HC; inversion HC; congruence.
    + destruct e.
      destruct bs.
      * constructor; intro HC; inversion HC; congruence.
      * destruct (IHn (k b) bs); constructor.
        -- destruct b.
           ++ eapply sample_n_vis_true; eauto.
           ++ eapply sample_n_vis_false; eauto.
        -- intro HC; inversion HC; subst; try congruence;
             rewrite Ht in H4; apply VisF_inversion in H4; subst; congruence.
Qed.
      
Lemma sample_n_S {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (bs : list bool) (n : nat) :
  sample_n t P bs n -> sample_n t P bs (S n).
Proof.
  intro Hsample.
  induction Hsample.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply sample_n_vis_false; eauto.
  - eapply sample_n_vis_true; eauto.
Qed.

Lemma sample_n_decidableb {A : Type}
      (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) :
  forall n, sample_n t P bs n \/ ~ sample_n t P bs n.
Proof. intro n; destruct (sample_nb_spec t P bs n); auto. Qed.

Lemma sample_n_bool_sumbool {A : Type}
      (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) :
  forall n, {sample_n t P bs n} + {~ sample_n t P bs n}.
Proof. intro n; destruct (sample_nb_spec t P bs n); auto. Defined.

Lemma sample_n_decidable {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (bs : list bool) :
  (forall x, P x \/ ~ P x) ->
  forall n, sample_n t P bs n \/ ~ sample_n t P bs n.
Proof.
  intros Hdec n.
  revert t bs. induction n; intros t bs.
  - destruct (observe t) eqn:Ht;
      try (right; intro HC; inversion HC; subst; rewrite Ht in H; congruence).
    destruct bs; destruct (Hdec r);
      try solve [left; eapply sample_n_ret; eauto];
      right; intro HC; inversion HC; subst.
    rewrite Ht in H0; inversion H0; subst; congruence.
  - destruct (IHn t bs).
    + left; apply sample_n_S; auto.
    + destruct (observe t) eqn:Ht.
      * destruct (Hdec r); destruct bs;
          try (right; intro HC; inversion HC; subst; congruence);
          left; econstructor; eauto.
      * destruct (IHn t0 bs).
        -- left; econstructor; eauto.
        -- right; intro HC; inversion HC; subst; congruence.
      * destruct e; destruct bs.
        -- right; intro HC; inversion HC; subst; congruence.
        -- destruct b.
           ++ destruct (IHn (k true) bs).
              ** left; eapply sample_n_vis_true; eauto.
              ** right; intro HC; inversion HC; subst.
                 { congruence. }
                 { rewrite Ht in H3; apply VisF_inversion in H3;
                     subst; congruence. }
           ++ destruct (IHn (k false) bs).
              ** left; eapply sample_n_vis_false; eauto.
              ** right; intro HC; inversion HC; subst.
                 { congruence. }
                 { rewrite Ht in H3; apply VisF_inversion in H3;
                     subst; congruence. }
Qed.

Lemma sample_n_sumbool {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (bs : list bool) :
  (forall x, {P x} + {~ P x}) ->
  forall n, {sample_n t P bs n} + {~ sample_n t P bs n}.
Proof.
  intros Hdec n.
  revert t bs. induction n; intros t bs.
  - destruct (observe t) eqn:Ht;
      try (right; intro HC; inversion HC; subst; rewrite Ht in H; congruence).
    destruct bs; destruct (Hdec r);
      try solve [left; eapply sample_n_ret; eauto];
      right; intro HC; inversion HC; subst.
    rewrite Ht in H; inversion H; subst; congruence.
  - destruct (IHn t bs).
    + left; apply sample_n_S; auto.
    + destruct (observe t) eqn:Ht.
      * destruct (Hdec r); destruct bs;
          try (right; intro HC; inversion HC; subst; congruence);
          left; econstructor; eauto.
      * destruct (IHn t0 bs).
        -- left; econstructor; eauto.
        -- right; intro HC; inversion HC; subst; congruence.
      * destruct e; destruct bs.
        -- right; intro HC; inversion HC; subst; congruence.
        -- destruct b.
           ++ destruct (IHn (k true) bs).
              ** left; eapply sample_n_vis_true; eauto.
              ** right; intro HC; inversion HC; subst.
                 { congruence. }
                 { rewrite Ht in H1; apply VisF_inversion in H1;
                     subst; congruence. }
           ++ destruct (IHn (k false) bs).
              ** left; eapply sample_n_vis_false; eauto.
              ** right; intro HC; inversion HC; subst.
                 { congruence. }
                 { rewrite Ht in H1; apply VisF_inversion in H1;
                     subst; congruence. }
Qed.

(* (** Boolean version of preimage. Coincides with the propositional *)
(*     version for trees with no Tau nodes. *) *)
(* Fixpoint preimageb {A : Type} *)
(*          (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) : bool := *)
(*   match _observe t with *)
(*   | RetF x => *)
(*     match bs with *)
(*     | [] => P x *)
(*     | _ => false *)
(*     end *)
(*   | VisF e k => *)
(*     (* Convoy pattern. *) *)
(*     match e in unbiasedE T return (T -> itree unbiasedE A) -> bool with *)
(*     | GetUnbiased => *)
(*       fun f => match bs with *)
(*             | [] => false *)
(*             | b :: bs' => preimageb (f b) P bs' *)
(*             end *)
(*     end k *)
(*   | _ => false *)
(*   end. *)

(** Maybe preimageb can be factored into two parts: one that is just a
    sampler function that uses a finite list of bits as input and
    produces an option result, then we just return true if it returns
    a result and that result is in P. *)

(** I guess the problem with that approach is that it's a bit
    unnatural to disallow overdetermined bit sequences. *)

(* Fixpoint walk_path {A : Type} (t : itree unbiasedE A) (bs : list bool) *)
(*   : option (itree unbiasedE A) := *)
(*   match bs with *)
(*   | [] => Some t *)
(*   | b :: bs' => *)
(*     match observe t with *)
(*     | VisF e k => *)
(*       match e in unbiasedE T return *)
(*             (T -> itree unbiasedE A) -> option (itree unbiasedE A) with *)
(*       | GetUnbiased => fun f => walk_path (f b) bs' *)
(*       end k *)
(*     | _ => None *)
(*     end *)
(*   end. *)

Fixpoint walk_path {A : Type} (t : itree unbiasedE A) (bs : list bool) (n : nat)
  : option (itree unbiasedE A) :=
  match n with
  | O => None
  | S n' =>
    match bs with
    | [] => Some t
    | b :: bs' =>
      match observe t with
      | VisF e k =>
        match e in unbiasedE T return
              (T -> itree unbiasedE A) -> option (itree unbiasedE A) with
        | GetUnbiased => fun f => walk_path (f b) bs' n'
        end k
      | TauF t' => walk_path t' bs n'
      | _ => None
      end
    end
  end.

Fixpoint exists_tau {A : Type} (t : itree unbiasedE A) (n : nat) : bool :=
  match n with
  | O => false
  | S n' =>
    match observe t with
    | TauF _ => true
    | VisF e k =>
      match e in unbiasedE T return (T -> itree unbiasedE A) -> bool with
      | GetUnbiased => fun f => exists_tau (f false) n' || exists_tau (f true) n'
      end k
    | RetF _ => false
    end
  end.

(** Reduce any finite sequence of Taus to a single one. Any infinite
    sequence of Taus is unchanged. *)
CoFixpoint remove_taus {E : Type -> Type} {A : Type} (t : itree E A)
  : itree E A :=
  match t with
  | Ret x => Ret x
  | Vis e k => Vis e (fun x => remove_taus (k x))
  | Tau (Tau t') => Tau (remove_taus t')
  | Tau t' => Tau t'
  end.

(* Fixpoint partial_sample {A : Type} (t : itree unbiasedE A) (bs : list bool) *)
(*   : option A := *)
(*   match bs with *)
(*   | [] => *)
(*     match observe t with *)
(*     | RetF x => Some x *)
(*     | _ => None *)
(*     end *)
(*   | b :: bs' => *)
(*     match observe t with *)
(*     | VisF e k => *)
(*       match e in unbiasedE T return (T -> itree unbiasedE A) -> option A with *)
(*       | GetUnbiased => fun f => partial_sample (f b) bs' *)
(*       end k *)
(*     | _ => None *)
(*     end *)
(*   end. *)

(** Will tree [t] either run out of bits in [bs] or successfully
    produce a sample within [n] steps? *)
Inductive terminates {A : Type} : itree unbiasedE A -> list bool -> nat -> Prop :=
| terminates_nil : forall t n,
    terminates t [] n
| terminates_ret : forall t x bs n,
    observe t = RetF x ->
    terminates t bs n
| terminates_tau : forall t t' bs n,
    observe t = TauF t' ->
    terminates t' bs n ->
    terminates t bs (S n)
| terminates_vis_false : forall t t1 t2 bs n,
    observe t = VisF GetUnbiased (fun b => if b : bool then t2 else t1) ->
    terminates t1 bs n ->
    terminates t (false :: bs) (S n)
| terminates_vis_true : forall t t1 t2 bs n,
    observe t = VisF GetUnbiased (fun b => if b : bool then t2 else t1) ->
    terminates t2 bs n ->
    terminates t (true :: bs) (S n).

(* Fixpoint partial_sample {A : Type} (t : itree unbiasedE A) (bs : list bool) (n : nat) *)
(*   : option A := *)
(*   match n with *)
(*   | O => None *)
(*   | S n' => *)
(*     match bs with *)
(*     | [] => *)
(*       match observe t with *)
(*       | RetF x => Some x *)
(*       | _ => None *)
(*       end *)
(*     | b :: bs' => *)
(*       match observe t with *)
(*       | VisF e k => *)
(*         match e in unbiasedE T return (T -> itree unbiasedE A) -> option A with *)
(*         | GetUnbiased => fun f => partial_sample (f b) bs' n' *)
(*         end k *)
(*       | TauF t' => partial_sample t' bs n' *)
(*       | _ => None *)
(*       end *)
(*     end *)
(*   end. *)

(* Definition preimageb' {A : Type} *)
(*            (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) : bool := *)
(*   match partial_sample t bs (length bs * 100) with *)
(*   | None => false *)
(*   | Some x => P x *)
(*   end. *)

(* Lemma preimageb_spec {A : Type} *)
(*       (t : itree unbiasedE A) (P : A -> bool) (bs : list bool) *)
(*   : reflect (preimage t (fun x => P x = true) bs) (preimageb t P bs). *)
(* Proof. *)
(*   destruct (_observe t) eqn:H. *)
(*   - destruct bs. *)
(*     + simpl. rewrite H. *)
(*       destruct (P r); constructor. *)
(*       assert (t = Ret r). *)
(*       {  *)
      
      

(* Definition measure (bs : list bool) : Q := *)
(*   1 / (Q.Qpow 2 (length bs)). *)

(* Eval compute in (measure [false; true]). *)

Definition bit_sequences : nat -> list bool :=
  fun n => removelast (nat_binary (S n)).

Definition bit_sequences_inverse (l : list bool) : nat :=
  pred (binary_nat (l ++ [true])).

Inductive last_element {A : Type} : list A -> A -> Prop :=
| last_element_x : forall x,
    last_element [x] x
| last_element_cons : forall x y z l,
    last_element (z :: l) x ->
    last_element (y :: z :: l) x.

Lemma last_element_remove_last {A : Type} (l : list A) (x : A) :
  last_element l x ->
  removelast l ++ [x] = l.
Proof.
  induction l; simpl; intro Hlast.
  - inversion Hlast.
  - inversion Hlast; subst.
    + reflexivity.
    + simpl in *; rewrite IHl; auto.
Qed.

Lemma last_element_positive_binary (p : positive) :
  last_element (positive_binary p) true.
Proof.
  induction p; simpl.
  - inversion IHp; subst.
    + repeat constructor.
    + constructor; rewrite H; auto.
  - inversion IHp; subst.
    + repeat constructor.
    + constructor; rewrite H; auto.
  - constructor.
Qed.

Lemma last_element_nat_binary (n : nat) :
  n <> O ->
  last_element (nat_binary n) true.
Proof.
  intro Hneq.
  destruct n; try congruence.
  unfold nat_binary; simpl.
  apply last_element_positive_binary.
Qed.

Lemma S_pred (n : nat) :
  (0 < n)%nat ->
  S (pred n) = n.
Proof. destruct n; lia. Qed.

Lemma bit_sequences_right_inverse (bs : list bool) :
  bit_sequences (bit_sequences_inverse bs) = bs.
Proof.
  unfold bit_sequences.
  unfold bit_sequences_inverse.
  rewrite S_pred.
  rewrite nat_binary_binary_nat.
  - rewrite removelast_app.
    + simpl; rewrite app_nil_r; reflexivity.
    + intro HC; inversion HC.
  - apply no_leading_falses_app.
    + intro HC; inversion HC.
    + repeat constructor.
  - induction bs; simpl.
    + unfold binary_nat; simpl; lia.
    + unfold binary_nat, binary_N.
      rewrite no_leading_falses_strip_falses_noop; simpl.
      * destruct (bs ++ [true]) eqn:Hl; lia.
      * rewrite app_comm_cons; apply no_leading_falses_app.
        -- intro HC; inversion HC.
        -- repeat constructor.
Qed.

Lemma bit_sequences_left_inverse (n : nat) :
  bit_sequences_inverse (bit_sequences n) = n.
Proof.
  unfold bit_sequences_inverse.
  unfold bit_sequences.
  rewrite last_element_remove_last.
  - rewrite binary_nat_nat_binary; reflexivity.
  - apply last_element_nat_binary; lia.
Qed.

(* Eval compute in (prefix bit_sequences 5). *)
(* Eval compute in (map bit_sequences_inverse (prefix bit_sequences 10)). *)

(* Definition measure_seq' {A : Type} *)
(*            (t : itree unbiasedE A) (P : A -> bool) (n : nat) : Q := *)
(*   if preimageb' t P (bit_sequences n) *)
(*   then interval_measure (bit_sequences n) *)
(*   else 0. *)

Lemma is_true_dec {A : Type} (P : A -> bool) :
  forall x, is_true (P x) \/ ~ is_true (P x).
Proof. intro x; destruct (P x); intuition. Qed.

Lemma is_true_sumbool {A : Type} (P : A -> bool) :
  forall x, {is_true (P x)} + {~ is_true (P x)}.
Proof. intro x; destruct (P x); intuition. Defined.

(** LPO version of measure_seq (assuming decidability of termination). *)
Definition measure_seq {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (n : nat) : Q :=
  let bs := bit_sequences n in
  if strong_LPO (sample_n t (fun x => is_true (P x)) bs)
                (sample_n_sumbool t (fun x => is_true (P x))
                                  bs (is_true_sumbool P))
  then interval_measure bs
  else 0.

Definition measure_chain {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (n : nat) : Q :=
  partial_sum (measure_seq t P) n.


(** Purely propositional version. *)

Inductive measure_seqP {A : Type}
  : itree unbiasedE A -> (A -> Prop) -> nat -> Q -> Prop :=
| measure_seq_false : forall t P n q,
    ~ preimage t P (bit_sequences n) ->
    q == 0 ->
    measure_seqP t P n q
| measure_seq_true : forall t P n q,
    preimage t P (bit_sequences n) ->
    q == interval_measure (bit_sequences n) ->
    measure_seqP t P n q.

(* Inductive measure_chainP {A : Type} *)
(*   : itree unbiasedE A -> (A -> Prop) -> nat -> Q -> Prop := *)
(* | measure_chain_O : forall t P q, *)
(*     measure_seqP t P O q -> *)
(*     measure_chainP t P O q *)
(* | measure_chain_S : forall t P n p q, *)
(*     measure_chainP t P n p -> *)
(*     measure_seqP t P (S n) q -> *)
(*     measure_chainP t P (S n) (p + q). *)

Definition measure_chainP {A : Type}
           (t : itree unbiasedE A) (P : A -> Prop) : nat -> Q -> Prop :=
  partial_sumP (measure_seqP t P).

Lemma measure_seqP_deterministic {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (n : nat) (p q : Q) :
  measure_seqP t P n p ->
  measure_seqP t P n q ->
  p == q.
Proof.
  intros Hp Hq; inversion Hp; inversion Hq; subst; try lra; congruence.
Qed.

Definition ubP (ub : Q) (f : nat -> Q -> Prop) : Prop :=
  forall n q, f n q -> q <= ub.

Definition supremumP (sup : Q) (f : nat -> Q -> Prop) : Prop :=
  ubP sup f /\ forall ub, ubP ub f -> sup <= ub.

Definition preimage_measure {A : Type}
           (t : itree unbiasedE A) (P : A -> Prop) (m : Q) : Prop :=
  supremumP m (measure_chainP t P).

Require Import order.
Definition preimage_measure' {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (m : Q) : Prop :=
  supremum m (measure_chain t P).

Lemma measure_seq_spec {A : Type}
      (t : itree unbiasedE A) (P : A -> bool) :
  f_relation (measure_seq t P) (measure_seqP t (fun x => is_true (P x))).
Proof.
  intro n.
  unfold measure_seq. simpl.
  destruct_LPO.
  - apply measure_seq_true; try reflexivity.
    apply sample_sample_n; auto.
  - apply measure_seq_false; try lra.
    intro HC; apply sample_sample_n in HC; congruence.
Qed.

Instance Proper_measure_seqP {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
  : Proper (eq ==> Qeq ==> iff) (measure_seqP t P).
Proof.
  intros ? n ? p q Heq; subst.
  split; intro H; inversion H; subst; solve [constructor; auto; lra].
Qed.

Lemma measure_chain_spec {A : Type}
      (t : itree unbiasedE A) (P : A -> bool) (n : nat) :
  measure_chainP t (fun x => is_true (P x)) n (measure_chain t P n).
Proof.
  unfold measure_chainP.
  unfold measure_chain.
  apply partial_sum_spec.
  apply measure_seq_spec.
  apply Proper_measure_seqP.
Qed.

(** TODO *)
(* Lemma preimage_measure_spec {A : Type} *)
(*       (t : itree unbiasedE A) (P : A -> bool) (m : Q) : *)
(*   preimage_measure t P m <-> preimage_measure' t P m. *)
(* Proof. *)
(*   split; intro H. *)
(*   - unfold preimage_measure in H. *)
(*     unfold preimage_measure'. *)
(*     unfold supremum. *)
(*     unfold supremumP in H. *)

(* Eval compute in (first_n bit_sequences 31). *)

(* Eval compute in (first_n measure_chain' 10). *)
(* Eval compute in (map Qred (first_n (partial_sum measure_chain') 100)). *)

Fixpoint unbiased_tree_to_itree {A : Type} (t : tree A)
  : itree unbiasedE (nat + A) :=
  match t with
  | Leaf x => ret (inr x)
  | Fail _ l => ret (inl l)
  | Choice _ t1 t2 =>
    Vis GetUnbiased (fun b => if b : bool
                           then unbiased_tree_to_itree t2
                           else unbiased_tree_to_itree t1)
  | Fix l t1 => Basics.iter (fun _ => x <- unbiased_tree_to_itree t1 ;;
                                  match x with
                                  | inl n =>
                                    if n =? l
                                    then ret (inl tt)
                                    else ret (inr (inl n))
                                  | inr y =>
                                    ret (inr (inr y))
                                  end) tt
  end.

Definition unbiased_tree_to_itree' {A : Type} (t : tree A) : itree unbiasedE A :=
  tie_itree' (unbiased_tree_to_itree t).

(* (** *) *)
(* Lemma preimage_measure_infer {A : Type} (t : tree A) (P : A -> bool) : *)
(*   preimage_measure (unbiased_tree_to_itree' t) P *)
(*                    (infer (fun x => if P x then 1 else 0) t). *)
(* Admitted. *)

Definition meas_seq {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (n : nat) : meas :=
  let bs := bit_sequences n in
  if (strong_LPO (sample_n t (fun x => is_true (P x)) bs)
                 (sample_n_sumbool t (fun x => is_true (P x))
                                   bs (is_true_sumbool P)))
  then meas_interval bs
  else meas_empty.

(* Definition meas_seq' {A : Type} *)
(*            (t : itree unbiasedE A) (P : A -> bool) : nat -> meas := *)
(*   (fun bs => if (strong_LPO (sample_n t (fun x => is_true (P x)) bs) *)
(*                          (sample_n_sumbool t (fun x => is_true (P x)) *)
(*                                            bs (is_true_sumbool P))) *)
(*           then meas_interval bs *)
(*           else meas_empty) ∘ bit_sequences. *)

(* Lemma meas_seq_meas_seq' {A : Type} (t : itree unbiasedE A) (P : A -> bool) (n : nat) : *)
(*   meas_seq t P n = meas_seq' t P n. *)
(* Proof. reflexivity. Qed. *)

(** The preimage of a set P under itree t is a measurable set. *)
Definition preimage_meas {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) : meas :=
  meas_union (meas_seq t P).

(* Lemma sample_n_deterministic {A : Type} *)
(*       (t : itree unbiasedE A) (P : A -> bool) (bs bs' : list bool) (n m : nat) : *)
(*   sample_n t P bs n -> *)
(*   sample_n t P bs' m -> *)
(*   bs = bs'. *)
(* Proof. *)
(*   intro H. revert m bs'. induction H; intros m bs' Hsample. *)
(*   (* induction 1; intro Hsample. *) *)
(*   - inversion Hsample; subst; auto; congruence. *)
(*   - inversion Hsample; subst; try congruence. *)
(*     rewrite H in H1; inversion H1; subst. *)
(*     eapply IHsample_n; eauto. *)
(*   - inversion Hsample; subst; try congruence. *)
(*     + rewrite H in H2. *)
(*       apply VisF_inversion in H2; subst. *)
(*       f_equal. *)
(*       eapply IHsample_n; eauto. *)
(*     + rewrite H in H2. *)
(*       apply VisF_inversion in H2; subst.   *)
(*     admit. *)
(*   - admit. *)
(* Admitted. *)

(* Inductive test := *)
(* | test_f : (nat -> nat) -> test. *)

(* Lemma test_inv (f g : nat -> nat) : *)
(*   test_f f = test_f g -> *)
(*   f = g. *)
(* Proof. *)
(*   intro H. *)
(*   inversion H; auto. *)
(* Qed. *)

Lemma sample_n_is_prefix_eq {A : Type}
      (t : itree unbiasedE A) (P Q : A -> Prop) (l1 l2 : list bool) (n m : nat) :
  is_prefix l1 l2 ->
  sample_n t P l1 n ->
  sample_n t Q l2 m ->
  l1 = l2.
Proof.
  revert t l1 l2 m.
  induction n; intros t l1 l2 m Hpre H0 H1.
  - inversion H0; subst; inversion H1; subst; congruence.
  - inversion H0; subst; inversion H1; subst; try congruence.
    + rewrite H2 in H; inversion H; subst.
      eapply IHn; eauto.
    + f_equal.
      rewrite H2 in H; apply VisF_inversion in H; subst.
      inversion Hpre; subst.
      eapply IHn; eauto.
    + inversion Hpre.
    + inversion Hpre.
    + f_equal.
      rewrite H2 in H; apply VisF_inversion in H; subst.
      inversion Hpre; subst.
      eapply IHn; eauto.
Qed.

Lemma sample_n_comparable_eq {A : Type}
      (t : itree unbiasedE A) (P Q : A -> Prop) (l1 l2 : list bool) (n m : nat) :
  comparable l1 l2 ->
  sample_n t P l1 n ->
  sample_n t Q l2 m ->
  l1 = l2.
Proof.
  intros Hcomp H0 H1.
  apply is_prefix_comparable in Hcomp.
  destruct Hcomp.
  - eapply sample_n_is_prefix_eq; eauto.
  - symmetry; eapply sample_n_is_prefix_eq; eauto.
Qed.

Inductive last_element_same {A : Type} : list A -> list A -> Prop :=
| last_element_same_x : forall x,
    last_element_same [x] [x]
| last_element_same_cons1 : forall x xs ys,
    last_element_same xs ys ->
    last_element_same (x :: xs) ys
| last_element_same_cons2 : forall xs y ys,
    last_element_same xs ys ->
    last_element_same xs (y :: ys).

(** The last elements may be the same but don't have to be. *)
Inductive all_but_last_same {A : Type} : list A -> list A -> Prop :=
(* | all_but_last_same_nil : *)
(*     all_but_last_same [] [] *)
| all_but_last_same_xy : forall x y,
    all_but_last_same [x] [y]
| all_but_last_same_cons : forall x xs ys,
    all_but_last_same xs ys ->
    all_but_last_same (x :: xs) (x :: ys).

Lemma not_last_element_same_nil {A : Type} (l : list A) :
  ~ last_element_same [] l.
Proof.
  induction l; simpl; intro HC; inversion HC; subst; congruence.
Qed.

Instance Symmetric_last_element_same {A : Type}
  : Symmetric (@last_element_same A).
Proof. induction 1; constructor; auto. Qed.

Lemma last_element_same_singleton {A : Type} (x y : A) :
  last_element_same [x] [y] ->
  x = y.
Proof.
  intro Hlast.
  inversion Hlast; subst; auto.
  - apply not_last_element_same_nil in H2; contradiction.
  - exfalso. eapply not_last_element_same_nil; symmetry; eauto.
Qed.

Lemma last_element_same_last_element {A : Type} (l : list A) (x : A) :
  last_element_same l [x] ->
  last_element l x.
Proof.  
  induction l; intro Hlast.
  - apply not_last_element_same_nil in Hlast; contradiction.
  - inversion Hlast; subst.
    + constructor.
    + destruct l.
      * apply not_last_element_same_nil in H2; contradiction.
      * constructor; auto.
    + symmetry in H1.
      apply not_last_element_same_nil in H1; contradiction.
Qed.

Lemma removelast_all_but_last_same {A : Type} (l1 l2 : list A) :
  l1 <> nil -> l2 <> nil ->
  removelast l1 = removelast l2 <-> all_but_last_same l1 l2.
Proof.
  intros H0 H1.
  split.
  - revert H0 H1. revert l2.
    induction l1; intros l2 H0 h1 Heq; try congruence.
    destruct l2; try congruence.
    destruct l1, l2; simpl in *; try congruence.
    + constructor.
    + inversion Heq; subst.
      constructor.
      apply IHl1; auto; intros HC; inversion HC.
  - induction 1.
    + reflexivity.
    + simpl.
      destruct xs, ys; auto.
      * inversion H.
      * inversion H.
      * f_equal; apply IHall_but_last_same; intros HC; inversion HC.
Qed.

Lemma last_element_same_cons {A : Type} (x y : A) (l1 l2 : list A) :
  last_element_same l1 (x :: y :: l2) ->
  last_element_same l1 (y :: l2).
Proof.
  revert x y l2.
  induction l1; intros x y l2 Hlast.
  - apply not_last_element_same_nil in Hlast; contradiction.
  - inversion Hlast; subst; auto.
    apply IHl1 in H2; constructor; auto.
Qed.

Lemma last_element_same_cons' {A : Type} (x y : A) (l1 l2 : list A) :
  last_element_same (x :: l1) (y :: l2) ->
  (l1 = nil /\ l2 = nil /\ x = y) \/
  (l1 = nil /\ last_element l2 x) \/
  (l2 = nil /\ last_element l1 y) \/
  last_element_same l1 l2.
Proof.
  intros Hlast.
  inversion Hlast; subst; auto.
  - inversion H2; subst; auto.
    + right. right. left. split; auto; constructor.
    + right. right.
      destruct l2.
      * left; split; auto.
        apply last_element_same_last_element in H.
        destruct xs.
        inversion H. constructor; auto.
      * right; constructor.
        eapply last_element_same_cons; eauto.
  - inversion H1; subst; auto.
    + right. left. split; auto.
      apply last_element_same_last_element; auto.
    + right.
      destruct l1.
      * left; split; auto.
        apply last_element_same_last_element.
        constructor.
        symmetry; auto.
      * right. right.
        symmetry.
        eapply last_element_same_cons.
        constructor.
        symmetry; eauto.
Qed.

Lemma all_but_last_same_length {A : Type} (l1 l2 : list A) :
  all_but_last_same l1 l2 ->
  length l1 = length l2.
Proof. induction 1; simpl; auto. Qed.

Lemma last_element_all_but_last_eq {A : Type} (l1 l2 : list A) :
  last_element_same l1 l2 ->
  all_but_last_same l1 l2 ->
  l1 = l2.
Proof.
  revert l2.
  induction l1; intros l2 Hlast Hall.
  - apply not_last_element_same_nil in Hlast; contradiction.
  - destruct l2.
    + symmetry in Hlast.
      apply not_last_element_same_nil in Hlast; contradiction.
    + apply last_element_same_cons' in Hlast.
      destruct Hlast as [[? [? ?]] | [[? ?] | [[? ?] | ?]]]; subst.
      * reflexivity.
      * apply all_but_last_same_length in Hall.
        simpl in *. destruct l2; simpl in *; try lia.
        inversion H0.
      * apply all_but_last_same_length in Hall.
        simpl in *. destruct l1; simpl in *; try lia.
        inversion H0.
      * inversion Hall; subst.
        -- inversion H.
        -- erewrite IHl1; eauto.
Qed.

Lemma removelast_inj {A : Type} (l1 l2 : list A) :
  last_element_same l1 l2 ->
  removelast l1 = removelast l2 ->
  l1 = l2.
Proof.
  destruct l1, l2; auto; intros Hlast Heq.
  - apply not_last_element_same_nil in Hlast; contradiction.
  - symmetry in Hlast.
    apply not_last_element_same_nil in Hlast; contradiction.
  - apply removelast_all_but_last_same in Heq;
      try solve[intro HC; inversion HC].
    apply last_element_all_but_last_eq; auto.
Qed.

Lemma last_element_singleton_same {A : Type} (l : list A) (x : A) :
  last_element l x ->
  last_element_same [x] l.
Proof.
  induction l; simpl; intro Hlast; inversion Hlast; subst.
  - constructor.
  - apply last_element_same_cons2; auto.
Qed.

Lemma last_element_last_element_same {A : Type} (l1 l2 : list A) (x : A) :
  last_element l1 x ->
  last_element l2 x ->
  last_element_same l1 l2.
Proof.
  revert l2.
  induction l1; intros l2 H0 H1.
  - inversion H0.
  - inversion H0; subst.
    + apply last_element_singleton_same; auto.
    + apply last_element_same_cons1; auto.
Qed.

Lemma bit_sequences_inj (i j : nat) :
  bit_sequences i = bit_sequences j ->
  i = j.
Proof.
  unfold bit_sequences.
  intro H.
  apply removelast_inj in H.
  - apply nat_binary_injective in H; lia.
  - clear H.
    eapply last_element_last_element_same;
      apply last_element_nat_binary; lia.
Qed.

Lemma meas_seq_disjoint {A : Type}
      (t : itree unbiasedE A) (P : A -> bool) (i j : nat) :
  i <> j ->
  disjoint (meas_seq t P i) (meas_seq t P j).
Proof.
  intro Hneq; unfold meas_seq.
  repeat destruct_LPO; try constructor.
  destruct e as [n H0].
  destruct e0 as [m H1].
  unfold interval_disjoint.
  apply incomparable_not_comparable.
  intro HC.
  eapply sample_n_comparable_eq in HC; eauto.
  apply bit_sequences_inj in HC; congruence.
Qed.

Lemma infer_f_supremum_measure (A : Type) (P : A -> bool) (t : tree A) :
  supremum (infer (fun x : A => if P x then 1 else 0) t)
           (partial_sum (measure_seq (unbiased_tree_to_itree' t) P)).
Proof.
  
Admitted.

Lemma preimage_meas_infer {A : Type} (t : tree A) (P : A -> bool) :
  measure (preimage_meas (unbiased_tree_to_itree' t) P)
          (infer (fun x => if P x then 1 else 0) t).
Proof.
  apply measure_union with (g := measure_seq (unbiased_tree_to_itree' t) P).
  - intros i j Hneq; apply meas_seq_disjoint; auto.
  - intro i; unfold meas_seq, measure_seq.
    destruct_LPO; constructor; reflexivity.
  - apply infer_f_supremum_measure.
Qed.

Lemma sample_n_singleton_P {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (bs : list bool) (n m : nat) (x : A) :
  sample_n t (fun y => y = x) bs n ->
  sample_n t P bs m ->
  P x.
Proof.
  revert t bs m.
  induction n; intros t bs m H0 H1;
    inversion H0; subst; inversion H1; subst; try congruence.
  - rewrite H2 in H; inversion H; subst; eapply IHn; eauto.
  - rewrite H2 in H3; apply VisF_inversion in H3; subst.
    eapply IHn; eauto.
  - rewrite H2 in H3; apply VisF_inversion in H3; subst.
    eapply IHn; eauto.
Qed.

Lemma sample_n_singleton_P' {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (bs : list bool) (n : nat) (x : A) :
  sample_n t (fun y => y = x) bs n ->
  P x ->
  sample_n t P bs n.
Proof.
  revert t bs.
  induction n; intros t bs H0 H1;
    inversion H0; subst; solve[econstructor; eauto].
Qed.

Lemma sample_n_real_in_measb {A : Type}
      (t : itree unbiasedE A) (r : real) (x : A) (P : A -> bool) (n m : nat) :
  sample_n t (fun y : A => y = x) (prefix r m) n ->
  (exists n0, real_in_measb (meas_seq t P n0) r = true) <-> P x = true.
Proof.
  intro Hsample. split.
  - intros [n0 Hin].
    unfold meas_seq in Hin.
    destruct_LPO.
    + destruct e as [n' H].
      unfold real_in_measb in Hin.
      unfold real_in_intervalb in Hin.
      destruct (real_in_intervalb_aux_spec r (bit_sequences n0) 0);
        try congruence; clear Hin.
      apply real_in_interval_exists_prefix in r0.
      rewrite <- r0 in H; clear r0.
      assert (Heq: prefix r m = prefix r (length (bit_sequences n0))).
      { eapply sample_n_comparable_eq; eauto.
        apply comparable_prefix. }
      rewrite <- Heq in H; clear Heq.
      set (P' := fun x => P x = true).
      assert (P' x).
      { eapply sample_n_singleton_P; eauto. }
      apply H0.
    + simpl in Hin; congruence.
  - intro HP.
    unfold meas_seq.
    exists (bit_sequences_inverse (prefix r m)).
    destruct_LPO.
    + simpl.
      destruct e as [n0 H].
      rewrite bit_sequences_right_inverse.
      destruct (real_in_intervalb_spec r (prefix r m)); auto.
      exfalso; apply n1.
      apply real_in_interval_prefix.
    + exfalso.
      apply n0. exists n. rewrite bit_sequences_right_inverse; auto.
      eapply sample_n_singleton_P'; eauto.
Qed.

(** Sampling theorem. *)
Section sample.
  Variable A : Type.
  Variable t : tree A.
  Definition it : itree unbiasedE A := unbiased_tree_to_itree' t.

  Variable reals : nat -> real.
  Hypothesis reals_uniform : uniform reals.

  Variable samples : nat -> A.
  Hypothesis reals_samples
    : forall i, exists m n, sample_n it (fun x => x = samples i) (prefix (reals i) m) n.

  Variable P : A -> bool.
  Definition P_prob : Q := infer (fun x => if P x then 1 else 0) t.

  Lemma samples_measure :
    forall eps : Q,
      0 < eps ->
      exists n : nat, Qabs (P_prob - rel_freq P (prefix samples n)) < eps.
  Proof.
    intros eps Heps.
    specialize (reals_uniform (preimage_meas_infer t P) Heps).
    destruct reals_uniform as [n Habs].
    exists n. unfold rel_freq' in Habs.
    assert (Heq: rel_freq (real_in_measb (preimage_meas it P))
                          (prefix reals n) ==
                 rel_freq P (prefix samples n)).
    { rewrite rel_freq_eq with (Q:=P) (g:=samples).
      - reflexivity.
      - intro i; destruct (reals_samples i) as [m [fuel reals_sample]].
        apply sample_n_real_in_measb with (P0:=P) in reals_sample.
        simpl; destruct_LPO.
        + apply reals_sample in e; auto.
        + destruct (P (samples i)); auto.
          exfalso; apply n0; apply reals_sample; auto. }
    rewrite <- Heq; auto.
  Qed.
End sample.


(** TODO: translating biased choice events into bernoulli trees with
  unbiased choice events. *)
Definition handle_biased {A : Type} (e : biasedE A) : itree unbiasedE A :=
  match e with
  | GetBiased p => diverge
  end.

(** TODO:

 * Two versions of inference? "high" and "low" level inference
     (parameterized probabilistic choice and unbiased (uniform)
     choice).
   
   Compiling high to low level (replacing choice nodes with bernoulli
     subtrees) and correctness theorem?

 * Fueled inference function on itrees.
 
 * NTS either:
 
   - given an inductive tree, fueled inference on the itree compiled
     from it converges in the limit to inference on the inductive
     tree.
 
   - given a command, fueled inference on the itree compiled from it
     converges in the limit to cwp of the command (wrt some initial
     state).

   The first implies the second due to the already established
   connection between inductive abstract trees and cwp.

 * Need a bernoulli tree construction, either directly as an itree or
   first as an inductive tree that can then be converted to an itree.


 ONE EXTREME: compile commands directly to abstract itrees and then
 translate those to ky itrees, reasoning directly about fueled
 inference (wrt cwp first, then wrt the two versions of fueled
 inference). It could be tricky connecting the two versions of fueled
 inference because the low level version will require more fuel in
 general.
 
 The theorem could say something like: forall t : itree, forall n :
 nat, exists n' : nat, infer n t == infer' n' (translate t)

 The inductive case for choice nodes would be the meat of the proof,
 requiring a proof of correctness of the bernoulli tree construction.

 OTHER EXTREME: compile commands to inductive abstract trees, then to
 inductive ky trees, then to ky itrees, with a theorem similar to
 above connecting inference on the inductive tree types, and then
 connecting to itrees only at the lowest level.
 
 IN BETWEEN: commands to abstract trees, then to abstract itrees, then
 translate to ky itrees.

 DIAGRAM:

 cpGCL -> abstract tree -> ky tree
 
      \ | | \ v v | \ v -> abstract itree -> ky itree

 cpGCL' -> ky tree or ky itree directly

* cpGCL -> abstract tree : done. state monad compiler.
 
* abstract tree -> ky tree : replace choice nodes with bernoulli trees
                             (with unbiased flip nodes)
 
* cpGCL -> abstract itree : done. relatively straightforward.
 
* abstract itree -> ky itree : event handler that constructs ky itrees
                               given a rational. Should be similar to
                               the bernoulli tree construction for
                               inductive trees. Could even just use
                               the inductive tree construction and
                               convert it.
 
* abstract tree -> abstract itree : done. relatively straightforward.
 
* ky tree -> ky itree : should be almost the exact same as for
                        abstract trees.

* cpGCL -> cpGCL' : desugaring probabilistic choices to loops and
                    unbiased choices.



Three main features of cpGCL:
* loops
* probabilistic choice
* conditioning

Compiling from cpGCL to trees can be seen as eliminating conditioning
(replacing with a big outer loop). Compilation is only correct when
all loops are iid, and the outer loop is always iid.

Translating from "abstract" to "ky" is reduction from parametric
probabilistic choice to more primitive uniform (unbiased) coin
flips.

Translating from inductive trees to coinductive trees can be seen
as eliminating loops by taking their infinite expansions.

In the end we arrive at "ky itrees" in which conditioning and loops
have been eliminated, and probabilistic choice is reduced to its most
primitive form.

*)

(** Abstract trees -> abstract itrees

- Theorem: converges (infer_n f t) (infer f t)

  How to prove? Possibly just by induction and using a geometric
  series argument in the fix case...

*)

Fixpoint infer_fail_n {A : Type} (n l : nat) (t : tree A) : Q :=
  match n with
  | O => 0
  | S n' =>
    match t with
    | Leaf _ => 0
    | Fail _ m => if m =? l then 1 else 0
    | Choice p t1 t2 =>
      p * infer_fail_n n' l t1 + (1-p) * infer_fail_n n' l t2
    | Fix m t =>
      let a := infer_fail_n n' l t in
      let b := infer_fail_n n' m t in
      a / (1 - b)
    end
  end.

(* Fixpoint infer_f_n {A : Type} (n : nat) (f : A -> Q) (t : tree A) : Q := *)
(*   match n with *)
(*   | O => 0 *)
(*   | S n' => *)
(*     match t with *)
(*     | Leaf x => f x *)
(*     | Fail _ _ => 0 *)
(*     | Choice p t1 t2 => p * infer_f_n n' f t1 + (1-p) * infer_f_n n' f t2 *)
(*     | Fix m t => *)
(*       let a := infer_f_n n' f t in *)
(*       let b := infer_fail_n n' m t in *)
(*       a / (1 - b) *)
(*     end *)
(*   end. *)

Inductive px_tree (A : Type) :=
| px_leaf : A -> px_tree A
| px_choice : Q -> px_tree A -> px_tree A -> px_tree A
| px_end : px_tree A.

Inductive simple {A : Type} : tree A -> Prop :=
| simple_leaf : forall x, simple (Leaf x)
| simple_choice : forall p t1 t2,
    simple t1 -> simple t2 ->
    simple (Choice p t1 t2)
| simple_fail : simple (Fail _ O).

(** Finite prefix of an itree. *)
Fixpoint prefix {A : Type} (t : itree biasedE A) (n : nat) : tree A :=
  match n with
  | O => Fail _ O
  | S n' =>
    match _observe t with
    | RetF x => Leaf x
    | TauF t' => prefix t' n'
    | VisF (GetBiased p) k =>
      Choice p (prefix (k false) n') (prefix (k true) n')
    end
  end.

(** Finite prefix of an itree. *)
Fixpoint prefix' {A : Type} (t : itree unbiasedE A) (n : nat) : tree A :=
  match n with
  | O => Fail _ O
  | S n' =>
    match observe t with
    | RetF x => Leaf x
    | TauF t' => prefix' t' n'
    | VisF GetUnbiased k =>
      Choice (1#2) (prefix' (k false) n') (prefix' (k true) n')
    end
  end.

Lemma prefix_simple {A : Type} (t : itree biasedE A) (n : nat) :
  simple (prefix t n).
Proof.
  revert t; induction n; intro t; simpl.
  - constructor.
  - destruct (_observe t); try destruct e; try constructor; auto.
Qed.

(** TODO: define inference on prefix trees and prove everything about
  them? Then use a chain of prefixes.. Not sure how much this buys us,
  but at least it should be easier to prove that inference is monotone
  wrt the prefix ordering. *)

(* Fixpoint infer_f_px {A : Type} (f : A -> Q) (t : px_tree A) : Q := *)
(*   match t with *)
(*   | px_leaf x => f x *)
(*   | px_choice p t1 t2 => *)
(*     p * infer_f_px f t1 + (1-p) * infer_f_px f t2 *)
(*   | px_end _ => 0 *)
(*   end. *)

Fixpoint infer_f_n {A : Type} (f : A -> Q) (t : itree biasedE A) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' =>
    match _observe t with
    | RetF x => f x
    | TauF t' => infer_f_n f t' n'
    | VisF (GetBiased p) k =>
      p * infer_f_n f (k true) n' + (1-p) * infer_f_n f (k false) n'
    end
  end.

Fixpoint infer_f_n' {A : Type}
         (f : A -> Q) (t : itree unbiasedE A) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' =>
    match _observe t with
    | RetF x => f x
    | TauF t' => infer_f_n' f t' n'
    | VisF GetUnbiased k =>
      (1#2) * infer_f_n' f (k true) n' + (1#2) * infer_f_n' f (k false) n'
    end
  end.

CoInductive wf_itree {A : Type} : itree biasedE A -> Prop :=
| wf_itree_ret : forall x, wf_itree (Ret x)
| wf_itree_tau : forall t, wf_itree t -> wf_itree (Tau t)
| wf_itree_vis : forall p k,
    0 <= p <= 1 ->
    wf_itree (k false) ->
    wf_itree (k true) ->
    wf_itree (Vis (GetBiased p) k).

Lemma ldfg {A : Type} {E : Type -> Type} (t : itree E A) :
  t ≅ go (observe t).
Proof.
  (* Set Printing All. *)
  apply itree_eta.
Qed.

Lemma kfsdf {A : Type} {E : Type -> Type} (t t' : itree E A) :
  _observe t = TauF t' ->
  t ≅ Tau t'.
Proof.
  intro Heq.
  rewrite <- Heq.
  apply itree_eta.
Qed.

(* Require Import Paco.paco. *)

(* Instance Proper_wf_itree {A : Type} *)
(*   : Proper (eq_itree eq ==> iff) (@wf_itree A). *)
(* Proof. *)
(*   intros t1 t2 Heq. split; intro Hwf. *)
(*   -      *)

(* Lemma gdg {A : Type} (f : A -> Q) (t : itree biasedE A) (n : nat) : *)
(*   expectation f -> *)
(*   wf_itree t -> *)
(*   infer_f_n f t n <= infer_f_n f t (S n). *)
(* Proof. *)
(*   intro Hexp. *)
(*   revert t. *)
(*   induction n; intros t Hwf; simpl. *)
(*   - destruct (_observe t); try destruct e; auto; lra. *)
(*   - destruct (_observe t) eqn:Ht. *)
(*     + lra. *)
(*     + apply IHn. *)
(*       rewrite kfsdf. *)
      
(*     + destruct e. *)
(*       pose proof (IHn (k true)) as IHtrue. *)
(*       pose proof (IHn (k false)) as IHfalse. *)
(*       simpl in *. *)
(*       assert (0 <= q <= 1). admit. *)
(*       nra. *)
(* Admitted. *)

(* Instance monotone_infer_f_n {A : Type} (f : A -> Q) (t : itree biasedE A) *)
(*   : Proper (le ==> Qle) (infer_f_n f t). *)
(* Proof. *)
(*   intros n m Hle. simpl. *)

(* Fixpoint infer_f_lib_n {A : Type} (n : nat) (f : A -> Q) (t : itree biasedE A) : Q := *)
(*   match n with *)
(*   | O => 1 *)
(*   | S n' => *)
(*     match t with *)
(*     | Ret x => f x *)
(*     | Tau t' => infer_f_lib_n n' f t' *)
(*     | Vis (GetBiased p) k => *)
(*       p * (infer_f_lib_n n' f (k true)) + (1-p) * (infer_f_lib_n n' f (k false)) *)
(*     end *)
(*   end. *)

(* Definition infer_n {A : Type} (n : nat) (f : A -> Q) (t : itree biasedE A) : Q := *)
(*   let a := infer_f_n n f t in *)
(*   let b := infer_f_lib_n n (const 1) t in *)
(*   a / b. *)
