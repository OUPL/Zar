Set Implicit Arguments.

(* To install ITree, do:
     opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

Require Import Coq.Program.Basics.
Require Import Coq.Bool.Bool.
Require Import Nat.
Require Import PeanoNat.
Require Import List.
Import ListNotations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import ExtLib.Structures.Monoid.

Require Import itree_regular.
Require Import misc.
Require Import regular.
Require Import tree.

Local Open Scope equiv_scope.

Fixpoint unbiased_tree_to_itree {A : Type} (t : tree A)
  : itree unbiasedE (nat + A) :=
  match t with
  | Leaf x => ret (inr x)
  | Fail _ l => ret (inl l)
  | Choice _ t1 t2 =>
    Vis GetUnbiased (fun b => if b : bool
                           then unbiased_tree_to_itree t1
                           else unbiased_tree_to_itree t2)
  | Fix l t1 => ITree.iter (fun _ => x <- unbiased_tree_to_itree t1 ;;
                                 match x with
                                 | inl n =>
                                   if n =? l
                                   then ret (inl tt)
                                   else ret (inr (inl n))
                                 | inr y =>
                                   ret (inr (inr y))
                                 end) tt
  end.

Definition tie_itree' {A : Type} {E : Type -> Type} (t : itree E (nat + A))
  : itree E A :=
  ITree.iter (fun _ => x <- t ;;
                    match x with
                    | inl _ => ret (inl tt)
                    | inr r => ret (inr r)
                    end) tt.

Definition unbiased_tree_to_itree' {A : Type} (t : tree A) : itree unbiasedE A :=
  tie_itree' (unbiased_tree_to_itree t).

Lemma itree_lang_tree_fail {A : Type} (t : tree A) (n : nat) :
  not_bound_in n t ->
  wf_tree t ->
  itree_lang (cotuple (eq n) (const False)) (unbiased_tree_to_itree t)
             (RE_sequence (RE_of_tree_fail t n)).
Proof.
  revert n.
  induction t; simpl; intros m Hnotbound Hwf; unfold tree_sequence_f; simpl.
  - pstep; constructor; auto.
  - pstep; destruct (Nat.eqb_spec n m); subst; constructor; auto; reflexivity.
  - inversion Hnotbound; inversion Hwf; subst.
    pstep; econstructor; eauto; try reflexivity; left.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - inversion Hnotbound; inversion Hwf; subst.
    apply itree_lang_iter_reps_product_lbl; auto.
Qed.

Lemma itree_lang_tree {A : Type} (t : tree A) (P : A -> bool) :
  wf_tree t ->
  itree_lang (cotuple (const False) (is_true ∘ P)) (unbiased_tree_to_itree t) (tree_sequence_f t P).
Proof.
  induction t; simpl; intros Hwf; unfold tree_sequence_f; simpl.
  - unfold compose.
    pstep. destruct (P a) eqn:Ha; simpl; constructor; auto.
    + reflexivity.
    + simpl; rewrite Ha; intuition.
  - pstep; constructor; auto.
  - inversion Hwf; subst; pstep; econstructor; eauto; try reflexivity; left.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - inversion Hwf; subst.
    apply itree_lang_iter_reps_product_P; auto.
    apply itree_lang_tree_fail; auto.
Qed.

Lemma itree_all_unfold_bind {A B : Type} {E : Type -> Type}
      P (t : itree E A) (k : A -> itree E B) r :
  paco1 (itree_all_ P) r (match observe t with
                          | RetF r => k r
                          | TauF t0 => Tau (x <- t0;; k x)
                          | VisF e ke => Vis e (fun x => x <- ke x;; k x)
                          end) ->
  paco1 (itree_all_ P) r (x <- t;; k x).
Proof.
  revert t k.
  pcofix CH.
  simpl.
  intros t k H.
  pstep.
  unfold itree_all_.
  unfold ITree.bind, ITree.subst in *.
  compute.
  rewrite 2!_observe_observe.
  punfold H.
  destruct (observe t).
  - eapply itree_allF_impl.
    2: { apply H. }
    intros t'[H0 | H0].
    + left; eapply itree_all_impl; eauto.
    + right; auto.
  - inversion H; subst; constructor.
    destruct H1 as [H1 | H1].
    + left; eapply itree_all_impl; eauto.
    + right; auto.
  - inversion H; subst; constructor; intro x.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3; subst.
    specialize (H1 x). destruct H1 as [H1 | H1].
    + left; eapply itree_all_impl; eauto.
    + right; auto.
Qed.

Lemma itree_all_unfold_iter {A B : Type} {E : Type -> Type}
      P (f : A -> itree E (A + B)) x r :
  paco1 (itree_all_ P) r (lr <- f x;; match lr with
                                     | inl l => Tau (ITree.iter f l)
                                     | inr r => Ret r
                                     end) ->
  paco1 (itree_all_ P) r (ITree.iter f x).
Proof.
  revert f x.
  pcofix CH.
  simpl.
  intros f x H.
  pstep.
  unfold itree_all_.
  unfold ITree.bind, ITree.subst in *.
  compute.
  rewrite 2!_observe_observe.
  punfold H.
  compute in H.
  rewrite 2!_observe_observe in H.
  destruct (observe (f x)).
  - eapply itree_allF_impl.
    2: { apply H. }
    intros t'[H0 | H0].
    + left; eapply itree_all_impl; eauto.
    + right; auto.
  - inversion H; subst; constructor.
    destruct H1 as [H1 | H1].
    + left; eapply itree_all_impl; eauto.
    + right; auto.
  - inversion H; subst; constructor; intro y.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3; subst.
    specialize (H1 y). destruct H1 as [H1 | H1].
    + left; eapply itree_all_impl; eauto.
    + right; auto.
Qed.

Lemma itree_all_bind {A B : Type} {E : Type -> Type}
      P Q (t : itree E A) (k : A -> itree E B) r :
  itree_all P t ->
  (forall x, P x -> paco1 (itree_all_ Q) r (k x)) ->
  paco1 (itree_all_ Q) r (x <- t;; k x).
Proof.
  revert t.
  pcofix CH.
  intros t Hall H0.
  apply itree_all_unfold_bind.
  punfold Hall.
  unfold itree_all_ in Hall. simpl in *.
  destruct (observe t).
  - inversion Hall; subst.
    eapply itree_all_impl; eauto.
  - inversion Hall; subst.
    destruct H1 as [H1 | H1].
    2: { inversion H1. }
    pstep. constructor.
    right; apply CH; auto.
  - inversion Hall; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3; subst.
    pstep; constructor; intro x.
    specialize (H1 x). destruct H1 as [H1 | H1].
    2: { inversion H1. }
    right; apply CH; auto.
Qed.

Lemma itree_all_iter {A B : Type} {E : Type -> Type} (f : A -> itree E (A + B)) P x :
  (forall x, itree_all (cotuple (const True) P) (f x)) ->
  itree_all P (ITree.iter f x).
Proof.
  intros H0.
  revert x.
  pcofix CH.
  intro x.
  apply itree_all_unfold_iter.
  eapply itree_all_bind; eauto.
  intros [a | b]; intro H.
  + pstep; constructor; right; auto.
  + simpl in H.
    pstep; constructor; auto.
Qed.

Lemma dfsgfd {A : Type} {E : Type -> Type} (t : itree E (nat + A)) (ns : list nat) (n : nat) :
  itree_all (cotuple (fun l : nat => Exists (eq l) (n :: ns)) (const True)) t ->
  itree_all (cotuple (const True) (cotuple (fun l : nat => Exists (eq l) ns) (const True)))
            (x <- t;;
             match x with
             | inl n0 => if n0 =? n then Ret (inl tt) else Ret (inr (inl n0))
             | inr y => Ret (inr (inr y))
             end).
Proof.
  revert t.
  pcofix CH.
  intros t H.
  + apply itree_all_unfold_bind.
    punfold H. pstep.
    unfold itree_all_ in *.
    destruct (observe t); simpl.
    * destruct r0.
      -- inversion H; subst; simpl in H1.
         destruct (Nat.eqb_spec n0 n); subst.
         ++ constructor; apply I.
         ++ constructor; simpl; inversion H1; subst; congruence.
      -- constructor; apply I.
    * inversion H; subst.
      destruct H1 as [H1 | H1].
      2: { inversion H1. }
      constructor; right; apply CH; auto.
    * inversion H; subst.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H3; subst.
      constructor; intro x.
      specialize (H1 x). destruct H1 as [H1 | H1].
      2: { inversion H1. }
      right; apply CH; auto.
Qed.

Lemma fsdd {A : Type} (t : tree A) (ns : list nat) :
  (forall l, free_in l t -> In l ns) ->
  itree_all (cotuple (fun l => Exists (eq l) ns) (const True)) (unbiased_tree_to_itree t).
Proof.
  revert ns.
  induction t; intros ns Hfree.
  - pstep; constructor; apply I.
  - pstep; constructor; auto. simpl.
    specialize (Hfree n (free_in_fail n)); subst.
    apply Exists_exists; exists n; auto.
  - pstep; constructor; auto; left; destruct x.
    + apply IHt1; auto; intros l H; apply Hfree; constructor; auto.
    + apply IHt2; auto; intros l H; apply Hfree; solve [constructor; auto].
  - assert (H0: forall l, free_in l t -> In l (n :: ns)).
    { intros l H0.
      destruct (Nat.eqb_spec l n); subst.
      - left; auto.
      - right; apply Hfree; constructor; auto. }
    specialize (IHt (n :: ns) H0).
    simpl.
    apply itree_all_iter. intros [].
    apply dfsgfd; auto.
Qed.

Lemma itree_all_P_impl {A : Type} {E : Type -> Type} (P Q : A -> Prop) (t : itree E A) :
  (forall x, P x -> Q x) ->
  itree_all P t ->
  itree_all Q t.
Proof.
  revert t.
  pcofix CH.
  intros t Himpl H.
  punfold H. pstep.
  unfold itree_all_ in *.
  destruct (observe t).
  - inversion H; subst; constructor; auto.
  - inversion H; subst.
    destruct H1 as [H1 | H1].
    2: { inversion H1. }
    constructor; right; apply CH; auto.
  - inversion H; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3; subst.
    constructor; intro x.
    specialize (H1 x). destruct H1 as [H1 | H1].
    2: { inversion H1. }
    right; apply CH; auto.
Qed.

Lemma fsdd' {A : Type} (t : tree A) (n : nat) :
  (forall l, free_in l t -> l = n) ->
  itree_all (cotuple (eq n) (const True)) (unbiased_tree_to_itree t).
Proof.
  intros H.
  generalize (@fsdd A t [n]).
  intro H0.
  simpl in *.
  eapply itree_all_P_impl.
  2: { apply H0.
       intros l Hfree; left; symmetry; auto. }
  intros [] H1; auto; simpl in *.
  inversion H1; subst; auto. inversion H3.
Qed.

(* Main result here. *)
Lemma itree_lang_tree' {A : Type} (t : tree A) (P : A -> bool) n :
  wf_tree t ->
  not_bound_in n t ->
  (forall l, free_in l t -> l = n) ->
  itree_lang (is_true ∘ P) (unbiased_tree_to_itree' t) (tree_sequence t P n).
Proof.
  intros Hwf Hnotbound Hfree. unfold unbiased_tree_to_itree'.
  unfold tie_itree'.
  unfold tree_sequence.
  simpl.
  apply itree_all_itree_lang_iter_P with (l:=n).
  - apply fsdd'; auto.
  - apply itree_lang_tree_fail; auto.
  - apply itree_lang_tree; auto.
Qed.

Definition in_tree_lang {A : Type} (t : tree A) (P : A -> bool) (n : nat) (bs : list bool) : Prop :=
  exists i, tree_sequence t P n i = Some bs.

(* (** Should be equivalent to strong LPO. *) *)
(* Axiom in_itree_lang_dec *)
(*   : forall {A : Type} (t : itree unbiasedE A) (P : A -> bool) (bs : list bool), *)
(*     { in_itree_lang (is_true ∘ P) t bs } + { ~ in_itree_lang (is_true ∘ P) t bs }. *)

Definition diverge {E : Type -> Type} {A : Type} : itree E A :=
  ITree.iter (ret ∘ inl) tt.

Lemma kfdsgf {A : Type} (M : Monoid A) (L : MonoidLaws M) (s : nat -> option A) :
  s === seq_union seq_zero (seq_product M (seq_one (monoid_unit M)) s).
Proof.
  rewrite seq_product_unit_l; auto.
  rewrite seq_union_zero_l; reflexivity.
Qed.

(** Any sequence is *a* language of the divergent itree (thus, there
    is no such thing as *the* language for a given itree in
    general). *)
Lemma in_itree_lang_diverge {A : Type} P s :
  itree_lang P (@diverge unbiasedE A) s.
Proof.
  unfold diverge, compose.
  pcofix CH.
  apply itree_lang_unfold_iter.
  rewrite kfdsgf.
  2: { apply MonoidLawsList. }
  apply itree_lang_bind; auto.
  - pstep; constructor.
    + apply I.
    + reflexivity.
  - pstep; constructor; intro HC; inversion HC.
Qed.

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
