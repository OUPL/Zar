Set Implicit Arguments.

(* To install ITree, do:
     opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

Require Import Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Logic.Eqdep_dec.
Require Import RelationClasses.
Require Import Coq.Classes.Equivalence.
Local Open Scope equiv_scope.
Require Import Nat.
Local Open Scope program_scope.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Require Import axioms.
Require Import borel.
Require Import cpGCL.
Require Import incomparable.
Require Import infer.
Require Import infer_regular.
Require Import itree_lang_unique.
Require Import itree_regular.
Require Import order.
Require Import misc.
Require Import nondivergent.
Require Import Q.
Require Import regular.
Require Import semiring.
Require Import tree.
Require Import unbiased_itree.

(** A biased coin event can be raised, passing a rational p to the
  environment and receiving in return a single bit with probability p
  of being 1. *)
Variant biasedE : Type -> Type :=
| GetBiased : Q -> biasedE bool.
(* | GetBiased : forall p : Q, 0 <= p <= 1 -> biasedE bool. *)

(* Variant unbiasedE : Type -> Type := *)
(* | GetUnbiased : unbiasedE bool. *)

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
    fun st => ITree.iter (map (fun x =>
                              match x with
                              | inl tt => inr (inl tt)
                              | inr st' =>
                                if e st' then inl st else inr (inr st')
                              end) (compile_itree body)) st
  | CObserve e => fun st => if e st then ret (inr st) else ret (inl tt)
  end.

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

(** Inductive trees to itrees. *)

Fixpoint tree_to_itree {A : Type} (t : tree A) : itree biasedE (nat + A) :=
  match t with
  | Leaf x => ret (inr x)
  | Fail _ lbl => ret (inl lbl)
  | Choice p t1 t2 =>
    Vis (GetBiased p) (fun b => if b : bool
                             then tree_to_itree t2
                             else tree_to_itree t1)
  | Fix lbl t1 => ITree.iter (fun _ => x <- tree_to_itree t1 ;;
                                   match x with
                                   | inl n =>
                                     if n =? lbl
                                     then ret (inl tt)
                                     else ret (inr (inl n))
                                   | inr y =>
                                     ret (inr (inr y))
                                   end) tt
  end.

(** The preimage of a set of samples [P] wrt itree [t] is the set of
    bit sequences [bs] such that [sample t bs P]. *)
Definition preimage {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
  : list bool -> Prop :=
  sample t P.

Require Import List.
Import ListNotations.

Fixpoint sample_nb {A : Type} (P : A -> bool)
         (t : itree unbiasedE A) (bs : list bool) (n : nat) : bool :=
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
    | TauF t' => sample_nb P t' bs n'
    | VisF e k =>
      match e in unbiasedE T return (T -> itree unbiasedE A) -> bool with
      | GetUnbiased =>
        fun f => match bs with
              | [] => false
              | b :: bs' => sample_nb P (f b) bs' n'
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
  apply Classical_Prop.EqdepTheory.inj_pair2 in H0; auto.
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

Lemma bit_sequences_nil_O n :
  bit_sequences n = [] ->
  n = O.
Proof.
  intro H; eapply inj_spec.
  - apply bit_sequences_left_inverse.
  - rewrite H; reflexivity.
Qed.

Lemma is_true_dec {A : Type} (P : A -> bool) :
  forall x, is_true (P x) \/ ~ is_true (P x).
Proof. intro x; destruct (P x); intuition. Qed.

Lemma is_true_sumbool {A : Type} (P : A -> bool) :
  forall x, {is_true (P x)} + {~ is_true (P x)}.
Proof. intro x; destruct (P x); intuition. Defined.

(* (** LPO version of measure_seq (assuming decidability of termination). *) *)
Definition measure_seq {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (n : nat) : Q :=
  let bs := bit_sequences n in
  if strong_LPO (* (sample_n (fun x => is_true (P x)) t bs) *)
       (sample_n_sumbool t (fun x => is_true (P x))
                         bs (is_true_sumbool P))
  then interval_measure bs
  else 0.

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

Instance Proper_measure_seqP {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
  : Proper (eq ==> Qeq ==> iff) (measure_seqP t P).
Proof.
  intros ? n ? p q Heq; subst.
  split; intro H; inversion H; subst; solve [constructor; auto; lra].
Qed.

Definition tie_itree {A : Type} {E : Type -> Type} (t : itree E (unit + A)) (lbl : nat)
  : itree E A :=
  ITree.iter (const t) tt.

Definition itree_topdown_lang {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (n : nat) : option (list bool) :=
  let bs := bit_sequences n in
  if (strong_LPO (sample_n_sumbool t (fun x => is_true (P x))
                                   bs (is_true_sumbool P)))
  then Some bs
  else None.

Definition meas_seq {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) (n : nat) : meas :=
  match itree_topdown_lang t P n with
  | Some bs => meas_interval bs
  | None => meas_empty
  end.

Definition measure_seq' {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) : nat -> Q :=
  option_measure ∘ itree_topdown_lang t P.

(* Weird thought: any infinite object can be represented, instead of
   by explicit coinduction, by a nat-indexed function of finite
   approximations. E.g., an infinite tree can be taken to be the
   "limit" of a function from a nat n to the nth finite approximation
   of the tree. A proof of a property of the tree could then proceed
   by 1) proving it for all finite approximations (by induction on n),
   and 2) showing that the property is continuous in that it preserves
   suprema (i.e., P(supf) iff forall n, P(f n). We are still using
   induction to prove a universal property (for all nats), it only
   amounts to an "existential" property about a particular infinite
   tree (the infinite nature of the tree "uses up" all of the
   universality of the nat induction). Is there a way to do some kind
   of transfinite induction or something similar, in a sense to gain
   "more universality", to prove universal properties of *all*
   elements of a coinductive type (or a countable subset)? *)

Lemma seq_nodup_topdown_lang {A : Type} (t : itree unbiasedE A) (P : A -> bool) :
  seq_nodup (itree_topdown_lang t P).
Proof.
  intros i j x Hnz H0 H1.
  unfold itree_topdown_lang in *.
  unfold equiv, zero in Hnz; simpl in Hnz.
  repeat destruct_LPO; try congruence.
  clear Hnz e0 e.
  rewrite <- H0 in H1; inversion H1; subst; clear H1.
  eapply inj_spec; eauto.
  apply bit_sequences_left_inverse.
Qed.

Lemma itree_lang_topdown_lang {A : Type} (t : itree unbiasedE A) (P : A -> bool) :
  itree_lang (is_true ∘ P) t (itree_topdown_lang t P).
Proof.
  revert t.
  unfold compose.
  pcofix CH; intro t.
  unfold itree_topdown_lang in *.
  pstep. unfold itree_lang_.
  destruct (observe t) eqn:Ht.
  - destruct (P r0) eqn:Hr0.
    + apply itree_langF_ret_true; auto.
      split.
      * unfold seq_injection_upto_0.
        exists id, id.
        intros i HC.
        split; auto.
        destruct_LPO.
        -- apply sample_sample_n in e.
           inversion e; subst; try solve[inversion Ht]; try congruence.
           symmetry in H. apply bit_sequences_nil_O in H; subst.
           reflexivity.
        -- exfalso; apply HC; reflexivity.
      * unfold seq_injection_upto_0.
        exists id, id. unfold id.
        intros i HC.
        split; auto.
        destruct_LPO.
        -- apply sample_sample_n in e.
           inversion e; subst; try solve[inversion Ht]; try congruence.
           symmetry in H; apply bit_sequences_nil_O in H; subst.
           reflexivity.
        -- apply singleton_seq_nonzero in HC; subst.
           exfalso; apply n.
           apply sample_sample_n.
           econstructor; eauto.
    + assert (H: (fun n : nat =>
                    if
                      strong_LPO
                        (sample_n_sumbool t (fun x : A => is_true (P x))
                                          (bit_sequences n) (is_true_sumbool P))
                    then Some (bit_sequences n)
                    else None) === seq_zero).
      { split; exists id, id; intros i Hnz; unfold id;
          split; auto; unfold equiv, seq_zero, const; destruct_LPO; auto;
            destruct e as [n HC]; inversion HC; subst; congruence. }
      rewrite H.
      apply itree_langF_ret_false; unfold is_true; congruence.
  - econstructor; eauto.
    split; exists id, id; intros i Hnz; split; auto; unfold id in *.
    + destruct_LPO; destruct_LPO.
      * reflexivity.
      * exfalso. apply n.
        destruct e as [m H0].
        exists (S m). econstructor; eauto.
      * exfalso; apply Hnz; reflexivity.
      * reflexivity.
    + destruct_LPO; destruct_LPO.
      * reflexivity.
      * exfalso. apply n.
        destruct e as [m H0].
        inversion H0; subst; try solve[inversion Ht]; try congruence.
        rewrite Ht in H. inversion H; subst.
        eexists; eauto.
      * exfalso; apply Hnz; reflexivity.
      * reflexivity.
  - destruct e.
    eapply itree_langF_vis.
    { right; apply CH. }
    { right; apply CH. }
    clear CH.
    split.
    + exists (fun n => match bit_sequences n with
               | true :: bs => (bit_sequences_inverse bs * 2)%nat
               | false :: bs => (bit_sequences_inverse bs * 2 + 1)%nat
               | nil => O
               end).
      exists (fun n => match n mod 2 with
               | O => bit_sequences_inverse (true :: bit_sequences (n / 2)%nat)
               | S _ => bit_sequences_inverse (false :: bit_sequences (n / 2)%nat)
               end).
      unfold equiv, zero.
      intros i Hnz; simpl in Hnz; split.
      * destruct_LPO; try congruence; clear Hnz.
        destruct e as [n Hsample].
        destruct (bit_sequences i) eqn:Hi.
        -- inversion Hsample; congruence.
        -- destruct b.
           ++ rewrite Nat.mod_mul; auto.
              rewrite Nat.div_mul; auto.
              rewrite bit_sequences_right_inverse.
              rewrite <- Hi, bit_sequences_left_inverse; reflexivity.
           ++ rewrite plus_comm, Nat.mod_add; auto.
              replace ((1 + bit_sequences_inverse l * 2) / 2)%nat with
                  ((Nat.b2n true + bit_sequences_inverse l * 2) / 2)%nat by reflexivity.
              rewrite mult_comm.
              rewrite (Nat.add_b2n_double_div2 true (bit_sequences_inverse l)).
              simpl.
              rewrite bit_sequences_right_inverse.
              rewrite <- Hi, bit_sequences_left_inverse; reflexivity.
      * destruct_LPO; try congruence; clear Hnz.
        destruct e as [n Hsample].
        unfold compose, seq_union.
        destruct (bit_sequences i) eqn:Hi.
        { inversion Hsample; try congruence. }
        destruct b.
        -- rewrite Nat.mod_mul; auto.
           rewrite Nat.div_mul; auto.
           rewrite bit_sequences_right_inverse.
           destruct_LPO; auto.
           exfalso; apply n0; inversion Hsample; subst; try congruence.
           rewrite Ht in H0; inversion H0.
           apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
           exists n1; auto.
        -- rewrite plus_comm, Nat.mod_add; auto.
           replace ((1 + bit_sequences_inverse l * 2) / 2)%nat with
               ((Nat.b2n true + bit_sequences_inverse l * 2) / 2)%nat by reflexivity.
           rewrite mult_comm.
           rewrite (Nat.add_b2n_double_div2 true (bit_sequences_inverse l)).
           rewrite bit_sequences_right_inverse.
           simpl.
           destruct_LPO; auto.
           exfalso; apply n0; inversion Hsample; subst; try congruence.
           rewrite Ht in H0; inversion H0.
           apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
           exists n1; auto.
    + exists (fun n => match n mod 2 with
               | O => bit_sequences_inverse (true :: bit_sequences (n / 2)%nat)
               | S _ => bit_sequences_inverse (false :: bit_sequences (n / 2)%nat)
               end).
      exists (fun n => match bit_sequences n with
               | true :: bs => (bit_sequences_inverse bs * 2)%nat
               | false :: bs => (bit_sequences_inverse bs * 2 + 1)%nat
               | nil => O
               end).
      unfold equiv, zero.
      intros i Hnz; simpl in Hnz; split.
      * destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod.
        -- rewrite bit_sequences_right_inverse.
           rewrite bit_sequences_left_inverse.
           rewrite mult_comm.
           apply mod_n_div; auto.
        -- rewrite bit_sequences_right_inverse.
           rewrite bit_sequences_left_inverse.
           rewrite mult_comm.
           apply mod_n_div_plus_1; auto.
      * unfold seq_union in *.
        destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod in *;
          unfold compose in *; rewrite bit_sequences_right_inverse;
            repeat destruct_LPO; auto; simpl in Hnz; try congruence;
              destruct e as [m HC]; exfalso; apply n.
        -- exists (S m); eapply sample_n_vis_true; eauto.
        -- exists (S m); eapply sample_n_vis_false; eauto.
Qed.

Definition tree_lang_meas {A : Type}
           (t : tree A) (P : A -> bool) (lbl n : nat) : meas :=
  match tree_sequence t P lbl n with
  | Some bs => meas_interval bs
  | None => meas_empty
  end.

(* Definition tree_lang_measures {A : Type} *)
(*            (t : tree A) (P : A -> bool) (lbl n : nat) : Q := *)
(*   match tree_sequence t P lbl n with *)
(*   | Some bs => interval_measure bs *)
(*   | None => 0 *)
(*   end. *)

(** The preimage of a set P under itree t is a measurable set. *)
Definition preimage_meas {A : Type}
           (t : itree unbiasedE A) (P : A -> bool) : meas :=
  meas_union (meas_seq t P).

Definition preimage_tree_lang_meas {A : Type}
           (t : tree A) (P : A -> bool) (lbl : nat) : meas :=
  meas_union (tree_lang_meas t P lbl).

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

(* Lemma itree_lang_comparable_eq {A : Type} *)
(*       (t : itree unbiasedE A) (P Q : A -> Prop) (l1 l2 : list bool)  : *)
(*   comparable l1 l2 -> *)
(*   in_itree_lang P t l1 -> *)
(*   in_itree_lang Q t l2 -> *)
(*   l1 = l2. *)
(* Proof. *)
(*   intros Hcomp H0 H1. *)
(*   apply is_prefix_comparable in Hcomp. *)
(*   destruct Hcomp. *)
(*   - eapply in_itree_lang_is_prefix_eq; eauto. *)
(*   - symmetry; eapply in_itree_lang_is_prefix_eq; eauto. *)
(* Qed. *)

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
  borel.disjoint (meas_seq t P i) (meas_seq t P j).
Proof.
  intro Hneq; unfold meas_seq, itree_topdown_lang.
  repeat destruct_LPO; try constructor.
  destruct e as [n H0].
  destruct e0 as [m H1].
  unfold interval_disjoint.
  apply incomparable_not_comparable.
  intro HC.
  eapply sample_n_comparable_eq in HC; eauto.
  apply bit_sequences_inj in HC; congruence.
Qed.

Lemma measure_seq_measure_seq' {A : Type} (t : itree unbiasedE A) (P : A -> bool) :
  forall i, measure_seq t P i = measure_seq' t P i.
Proof.
  unfold measure_seq, measure_seq', compose, itree_topdown_lang.
  intro i; destruct_LPO; auto.
Qed.

Instance Proper_option_measure : Proper (equiv ==> equiv) option_measure.
Proof. intros [] [] Heq; congruence. Qed.

Lemma seq_bijection_upto_0_tree_sequence_measure_seq
      {A : Type} (P : A -> bool) (t : tree A) (n : nat) :
  wf_tree t ->
  nondivergent'' n t ->
  not_bound_in n t ->
  (forall l : nat, free_in l t -> l = n) ->
  option_measure ∘ tree_sequence t P n === measure_seq (unbiased_tree_to_itree' t) P.
Proof.
  intros Hwf Hnd Hnotbound Hfree.
  transitivity (measure_seq' (unbiased_tree_to_itree' t) P).
  2: { apply ext_eq_seq_bijection_upto_0.
       intro i; rewrite measure_seq_measure_seq'; reflexivity. }
  unfold measure_seq'.
  apply compose_seq_bijection_upto_0; try reflexivity.
  { apply Proper_option_measure. }
  eapply itree_fintau_itree_lang_unique with (P0 := is_true ∘ P).
  - eapply nondivergent''_itree_fintau; eauto.
  - apply itree_lang_tree'; auto.
  - apply itree_lang_topdown_lang.
  - apply (@seq_nodup_tree_sequence A t [n] P); auto.
    + inversion Hnd; auto.
    + intros m Hbound [? | []]; subst.
      apply bound_in_not_bound_in in Hnotbound; congruence.
  - apply seq_nodup_topdown_lang.
Qed.

Lemma infer_supremum_measure {A : Type} (P : A -> bool) (t : tree A) (n : nat) :
  wf_tree t ->
  unbiased t ->
  (forall m, free_in m t -> m = n) ->
  not_bound_in n t ->
  nondivergent'' n t ->
  supremum (infer (fun x : A => if P x then 1 else 0) t)
           (partial_sum (measure_seq (unbiased_tree_to_itree' t) P)).
Proof.
  intros Hwf Hunbiased Hfree Hnotbound Hnd.
  apply seq_bijection_upto_0_supremum with (s1:=option_measure ∘ tree_sequence t P n).
  - intro i; apply option_measure_nonnegative.
  - intro i; unfold measure_seq; destruct_LPO; try lra;
      apply interval_measure_nonnegative.
  - apply seq_bijection_upto_0_tree_sequence_measure_seq; auto.
  - apply infer_supremum; auto.
Qed.

(* (* TODO: replace measure_seq with the analogue using tree_lang_meas *)
(*    and see how far we can go in the sampling theorem using this and *)
(*    preimage_tree_lang_meas_infer instead of the topdown lang stuff. *) *)
(* Lemma infer_supremum_measure' {A : Type} (P : A -> bool) (t : tree A) (n : nat) : *)
(*   wf_tree t -> *)
(*   unbiased t -> *)
(*   (forall m, free_in m t -> m = n) -> *)
(*   not_bound_in n t -> *)
(*   nondivergent'' n t -> *)
(*   supremum (infer (fun x : A => if P x then 1 else 0) t) *)
(*            (partial_sum (option_measure ∘ tree_sequence t P n)). *)
(* Proof. *)
(*   intros Hwf Hunbiased Hfree Hnotbound Hnd. *)
(*   apply infer_supremum; auto. *)
(* Qed. *)
(*   apply seq_bijection_upto_0_supremum with (s1:=option_measure ∘ tree_sequence t P n). *)
(*   - intro i; apply option_measure_nonnegative. *)
(*   - intro i; unfold measure_seq; destruct_LPO; try lra; *)
(*       apply interval_measure_nonnegative. *)
(*   - apply seq_bijection_upto_0_tree_sequence_measure_seq; auto. *)
(*   - apply infer_supremum; auto. *)
(* Qed. *)

Lemma preimage_tree_lang_meas_infer {A : Type} (t : tree A) (P : A -> bool) (n : nat) :
  wf_tree t ->
  unbiased t ->
  (forall m, free_in m t -> m = n) ->
  not_bound_in n t ->
  nondivergent'' n t ->
  measure (preimage_tree_lang_meas t P n)
          (infer (fun x => if P x then 1 else 0) t).
Proof.
  intros Hwf Hunbiased Hfree Hnotbound Hnd.
  unfold preimage_tree_lang_meas.
  econstructor.
  3: { eapply infer_supremum; eauto. }
  unfold tree_lang_meas.
  - intros i j Hneq.
    destruct (tree_sequence t P n i) eqn:Hi, (tree_sequence t P n j) eqn:Hj;
      constructor.
    eapply seq_incomparable_tree_sequence; eauto.
    + inversion Hnd; subst; eauto.
    + intros m Hbound [Hin | []]; subst.
      apply bound_in_not_bound_in in Hnotbound; congruence.
  - unfold compose, option_measure.
    intro i. unfold tree_lang_meas.
    destruct (tree_sequence t P n i); constructor; reflexivity.
Qed.

Lemma preimage_meas_infer {A : Type} (t : tree A) (P : A -> bool) (n : nat) :
  wf_tree t ->
  unbiased t ->
  (forall m, free_in m t -> m = n) ->
  not_bound_in n t ->
  nondivergent'' n t ->
  measure (preimage_meas (unbiased_tree_to_itree' t) P)
          (infer (fun x => if P x then 1 else 0) t).
Proof.
  intros Hwf Hunbiased Hfree Hnotbound Hnd.
  apply measure_union with (g := measure_seq (unbiased_tree_to_itree' t) P).
  - intros i j Hneq; apply meas_seq_disjoint; auto.
  - intro i; unfold meas_seq, measure_seq, itree_topdown_lang.
    destruct_LPO; constructor; reflexivity.
  - eapply infer_supremum_measure; eauto.
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
    unfold meas_seq, itree_topdown_lang in Hin.
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
    unfold meas_seq, itree_topdown_lang.
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

(* idea: use the top-down construction of the sequence using
   sample_n and strong LPO as before, and show that it's a language of
   the itree. Then, equivalence to the inductive construction follows
   from uniqueness of the itree language (which only holds under
   nondivergence). *)

(* TODO: sampling fixpoint on inductive trees? using a map from labels to subtrees *)



Lemma uniform_samples_nondivergent {A : Type} `{EqType A} (t : tree A) (lbl : nat)
      (reals : nat -> real) (samples : nat -> A) :
  uniform reals ->
  (forall i, exists m n, sample_n (unbiased_tree_to_itree' t)
                        (fun x => x = samples i) (prefix (reals i) m) n) ->
  nondivergent'' lbl t.
Proof.
  intros Huniform Hsample.
  unfold unbiased_tree_to_itree', tie_itree' in Hsample.
  
  assert (H0: forall i, exists n, sample (unbiased_tree_to_itree' t)
                           (eq (samples i)) (prefix (reals i) n)).
  { intros i; specialize (Hsample i).
    destruct Hsample as [m [n Hsample]].
    exists m; apply sample_sample_n; exists n.
    eapply sample_n_singleton_P'; eauto. }
  clear Hsample.
  unfold nondivergent''.
  destruct (nondivergent''_dec lbl t) as [? | Hdiv]; auto.
  exfalso.
  unfold divergent' in Hdiv.
  
  (* may need induction on Hdiv? *)
  inversion Hdiv; subst.
  destruct H3.
  - destruct H1 as [H1 H2].
    admit.
  - 
  
Admitted.

(** Sampling theorem. *)
Section sampling_theorem.
  Context (A : Type) `{EqType A} (t : tree A) (lbl : nat)
          (reals : nat -> real) (samples : nat -> A) (P : A -> bool)
          (Hwf : wf_tree t) (Hunbiased : unbiased t)
          (Hfree : forall m, free_in m t -> m = lbl)
          (Hnotbound : not_bound_in lbl t)
          (Hnd : nondivergent'' lbl t).

  Definition it : itree unbiasedE A := unbiased_tree_to_itree' t.

  Hypothesis reals_uniform : uniform reals.
  Hypothesis reals_samples
    : forall i, exists m n, sample_n it (fun x => x = samples i) (prefix (reals i) m) n.

  Definition P_prob : Q := infer (fun x => if P x then 1 else 0) t.
  
  (* Context (A : Type) `{EqType A}. *)
  (* Variable t : tree A. *)
  (* Variable lbl : nat. *)
  (* Hypothesis Hwf : wf_tree t. *)
  (* Hypothesis Hunbiased : unbiased t. *)
  (* Hypothesis Hfree : forall m, free_in m t -> m = lbl. *)
  (* Hypothesis Hnotbound : not_bound_in lbl t. *)
  (* Hypothesis Hnd : nondivergent'' lbl t. (* eliminate somehow? should *)
  (*                                           be implied by reals_samples below. *) *)

  (* Definition it : itree unbiasedE A := unbiased_tree_to_itree' t. *)

  (* Variable reals : nat -> real. *)
  (* Hypothesis reals_uniform : uniform reals. *)
  
  (* Variable samples : nat -> A. *)
  (* Hypothesis reals_samples *)
    (* : forall i, exists m n, sample_n it (fun x => x = samples i) (prefix (reals i) m) n. *)

  (* Variable P : A -> bool. *)
  (* Definition P_prob : Q := infer (fun x => if P x then 1 else 0) t. *)

  Theorem samples_converge :
    forall eps : Q,
      0 < eps ->
      exists n0 : nat, forall n, (n0 <= n)%nat -> Qabs (P_prob - rel_freq P (prefix samples n)) < eps.
  Proof.
    intros eps Heps.
    
    specialize (reals_uniform (preimage_meas_infer P Hwf Hunbiased Hfree Hnotbound Hnd) Heps).
    destruct reals_uniform as [n0 Habs].
    exists n0. unfold rel_freq' in Habs.
    intros n Hle.
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
          exfalso; apply n1; apply reals_sample; auto. }
    rewrite <- Heq; auto.
    
    (* specialize (reals_uniform (preimage_tree_lang_meas_infer P Hwf Hunbiased Hfree Hnotbound Hnd) Heps). *)
    (* destruct reals_uniform as [n Habs]. *)
    (* exists n. unfold rel_freq' in Habs. *)
    (* assert (Heq: rel_freq (real_in_measb (preimage_tree_lang_meas t P lbl)) *)
    (*                       (prefix reals n) == *)
    (*              rel_freq P (prefix samples n)). *)
    (* { rewrite rel_freq_eq with (Q:=P) (g:=samples). *)
    (*   - reflexivity. *)
    (*   - intro i; destruct (reals_samples i) as [m [fuel reals_sample]]. *)
    (*     apply sample_n_real_in_measb_tree with (P0:=P) (lbl0:=lbl) in reals_sample. *)
    (*     simpl; destruct_LPO. *)
    (*     + apply reals_sample in e; auto. *)
    (*     + destruct (P (samples i)); auto. *)
    (*       exfalso; apply n0; apply reals_sample; auto. } *)
    (* rewrite <- Heq; auto. *)
    
  Qed.
End sampling_theorem.

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
