(* To install ITree, do:
     opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

Require Import Coq.Program.Basics.
Require Import Nat.
Require Import PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import List.
Import ListNotations.

Local Open Scope equiv_scope.
Local Open Scope program_scope.

Require Import misc.
Require Import regular.
Require Import semiring.
Require Import tree.

Variant unbiasedE : Type -> Type :=
| GetUnbiased : unbiasedE bool.

Section itree_all.
  Context {A : Type} {E : Type -> Type} (P : A -> Prop).

  Inductive itree_allF (R : itree E A -> Prop) : itree' E A -> Prop :=
  | itree_allF_ret : forall x, P x -> itree_allF R (RetF x)
  | itree_allF_tau : forall t, R t -> itree_allF R (TauF t)
  | itree_allF_vis : forall {A} (e : E A) f,
      (forall x, R (f x)) ->
      itree_allF R (VisF e f).

  Definition itree_all_ R : itree E A -> Prop :=
    fun t => itree_allF R (observe t).

  Lemma itree_allF_mono R R' t
        (IN: itree_allF R t)
        (LE: R <1= R') :
    itree_allF R' t.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_all__mono : monotone1 (itree_all_).
  Proof. do 2 red. intros. eapply itree_allF_mono; eauto. Qed.
  Hint Resolve itree_all__mono : paco.

  Definition itree_all : itree E A -> Prop :=
    paco1 itree_all_ bot1.

  Lemma itree_allF_impl (t : itree' E A) (Q1 Q2 : itree E A -> Prop) :
    (forall t, Q1 t -> Q2 t) ->
    itree_allF Q1 t -> itree_allF Q2 t.
  Proof.
    intros H0 H1.
    destruct t; inversion H1; subst; constructor; auto.
    apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; auto.
  Qed.

  Lemma itree_all_impl (t : itree E A) (Q1 Q2 : itree E A -> Prop) :
    (forall t, Q1 t -> Q2 t) ->
    paco1 itree_all_ Q1 t -> paco1 itree_all_ Q2 t.
  Proof.
    revert t.
    pcofix CH.
    intros t H0 H1.
    punfold H1; pstep.
    eapply itree_allF_impl.
    2: { apply H1. }
    intros t' [H2 | H2].
    - right; apply CH; auto.
    - right; auto.
  Qed.

  (* Lemma itree_allF_all_ {t : itree E A} r : *)
  (*   itree_allF r (observe t) <-> itree_all_ r t. *)
  (* Proof. firstorder. Qed. *)

  (* Global Instance Proper_itree_all' r *)
  (*   : Proper (eq_itree eq ==> flip impl) (paco1 itree_all_ r). *)
  (* Proof. *)
  (*   pcofix CH. *)
  (*   intros t1 t2 Heq Hall. *)
  (*   punfold Hall; pstep. *)
  (*   unfold itree_all_ in *. *)
  (*   punfold Heq. unfold eqit_ in Heq. *)
  (*   destruct (observe t1); destruct (observe t2); inversion Heq; subst; try congruence. *)
  (*   - inversion Hall; subst; constructor; auto. *)
  (*   - inversion Hall; subst. *)
  (*     destruct REL as [REL | REL]. *)
  (*     2: { inversion REL. } *)
  (*     constructor. *)
  (*     destruct H0 as [H0 | H0]. *)
  (*     + right. eapply CH. apply REL. auto. *)
  (*     + right. apply CH0. *)
  (*     constructor. right. *)
  (*     eapply CH. apply REL. *)
  (*     destruct H0 as [H0 | H0]. *)
  (*     + eapply itree_allF_impl. *)
  (*       2: { apply Hall. *)
  (*     2: { inversion H0. } *)
  (*     destruct REL as [H1 | H1]. *)
  (*     2: { inversion H1. } *)
  (*     constructor. right. eapply CH; eauto. *)
  (*   - eapply fold_eqitF with (t3 := Vis e k) (t4 := Vis e0 k0) in Heq; auto. *)
  (*     apply eqitree_inv_Vis_r in Heq. *)
  (*     destruct Heq as [k' [H0 Heq]]. *)
  (*     simpl in H0. *)
  (*     inversion H0; subst. *)
  (*     apply Eqdep.EqdepTheory.inj_pair2 in H3; subst. *)
  (*     apply Eqdep.EqdepTheory.inj_pair2 in H6; subst. *)
  (*     constructor; intros x. *)
  (*     right; eapply CH; eauto. *)
  (*     inversion Hall; subst. *)
  (*     apply Eqdep.EqdepTheory.inj_pair2 in H6; subst. *)
  (*     apply Eqdep.EqdepTheory.inj_pair2 in H7; subst. *)
  (*     destruct (H3 x) as [H | H]; auto; inversion H. *)
  (* Qed. *)

  Global Instance Proper_itree_all : Proper (eq_itree eq ==> flip impl) itree_all.
  Proof.
    pcofix CH.
    intros t1 t2 Heq Hall.
    punfold Hall; pstep.
    unfold itree_all_ in *.
    punfold Heq. unfold eqit_ in Heq.
    destruct (observe t1); destruct (observe t2); inversion Heq; subst; try congruence.
    - inversion Hall; subst; constructor; auto.
    - inversion Hall; subst.
      destruct H0 as [H0 | H0].
      2: { inversion H0. }
      destruct REL as [H1 | H1].
      2: { inversion H1. }
      constructor. right. eapply CH; eauto.
    - eapply fold_eqitF with (t3 := Vis e k) (t4 := Vis e0 k0) in Heq; auto.
      apply eqitree_inv_Vis_r in Heq.
      destruct Heq as [k' [H0 Heq]].
      simpl in H0.
      inversion H0; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H6; subst.
      constructor; intros x.
      right; eapply CH; eauto.
      inversion Hall; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H6; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H7; subst.
      destruct (H3 x) as [H | H]; auto; inversion H.
  Qed.
End itree_all.
Hint Resolve itree_all__mono : paco.

Section in_itree_lang.
  Context {A : Type} (P : A -> Prop).

  Inductive in_itree_langF (R : itree unbiasedE A -> list bool -> Prop)
    : itree' unbiasedE A -> list bool -> Prop :=
  | in_itree_langF_ret_true : forall x,
      P x ->
      in_itree_langF R (RetF x) []
  | in_itree_langF_tau : forall t bs, R t bs -> in_itree_langF R (TauF t) bs
  | in_itree_langF_vis_true : forall f bs,
      R (f true) bs ->
      in_itree_langF R (VisF GetUnbiased f) (true :: bs)
  | in_itree_langF_vis_false : forall f bs,
      R (f false) bs ->
      in_itree_langF R (VisF GetUnbiased f) (false :: bs).

  Definition in_itree_lang_ R : itree unbiasedE A -> list bool -> Prop :=
    fun t bs => in_itree_langF R (observe t) bs.

  Lemma in_itree_langF_mono R R' t bs
        (IN: in_itree_langF R t bs)
        (LE: R <2= R') :
    in_itree_langF R' t bs.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma in_itree_lang__mono : monotone2 (in_itree_lang_).
  Proof. do 2 red. intros. eapply in_itree_langF_mono; eauto. Qed.
  Hint Resolve in_itree_lang__mono : paco.

  Definition in_itree_lang : itree unbiasedE A -> list bool -> Prop :=
    paco2 in_itree_lang_ bot2.
  
  (* Fixpoint in_itree_aux (t : itree unbiasedE A) (bs : list bool) (n : nat) : bool := *)
  (*   match n with *)
  (*   | O => false *)
  (*   | S n' => match observe t with *)
  (*            | RetF x => P x *)
  (*            | TauF t' => in_itree_aux t' bs n' *)
  (*            | VisF GetUnbiased k => *)
  (*              match bs with *)
  (*              | nil => false *)
  (*              | false :: bs' => in_itree_aux (k false) bs' n' *)
  (*              | true :: bs' => in_itree_aux (k true) bs' n' *)
  (*              end *)
  (*            end *)
  (*   end. *)

  (* Definition in_itree (t : itree unbiasedE A) (bs : list bool) : bool := *)
  (*   in_itree_aux t bs (S (length bs)). *)

  (* Lemma in_itree_spec (t : itree unbiasedE A) (bs : list bool) : *)
  (*   itree_notau t -> *)
  (*   in_itree_aux t bs (S (length bs)) = true <-> in_itree_lang t bs. *)
  (* Proof. *)
  (*   revert t. *)
  (*   induction bs; simpl; intros t Hnotau. *)
  (*   - punfold Hnotau; unfold itree_notau_ in Hnotau. *)
  (*     destruct (observe t) eqn:Ht. *)
  (*     + split; intro H. *)
  (*       * pstep; unfold in_itree_lang_; rewrite Ht; constructor; auto. *)
  (*       * punfold H; unfold in_itree_lang_ in H; rewrite Ht in H. *)
  (*         inversion H; auto. *)
  (*     + inversion Hnotau. *)
  (*     + destruct e. *)
  (*       split; intro H; try congruence. *)
  (*       punfold H; unfold in_itree_lang_ in H; rewrite Ht in H; inversion H. *)
  (*   - punfold Hnotau; unfold itree_notau_ in Hnotau. *)
  (*     destruct (observe t) eqn:Ht. *)
  (*     + split; intro H. *)
  (*       * pstep; unfold in_itree_lang_; rewrite Ht; constructor; auto. *)
  (*       * punfold H; unfold in_itree_lang_ in H; rewrite Ht in H. *)
  (*         inversion H; auto. *)
  (*     + inversion Hnotau. *)
  (*     + destruct e. *)
  (*       inversion Hnotau. *)
  (*       apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst. *)
  (*       apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst. *)
  (*       destruct a. *)
  (*       * specialize (H0 true). *)
  (*         destruct H0 as [H0 | H0]. *)
  (*         2: inversion H0. *)
  (*         specialize (IHbs (k true) H0); destruct IHbs as [IH IH']. *)
  (*         split; intro H. *)
  (*         -- pstep; unfold in_itree_lang_; rewrite Ht; constructor. *)
  (*            left; apply IH; auto. *)
  (*         -- punfold H; unfold in_itree_lang_ in H; rewrite Ht in H. *)
  (*            inversion H; subst. *)
  (*            destruct H3 as [H3 | H3]. *)
  (*            2: inversion H3. *)
  (*            apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst. *)
  (*            apply IH'; auto. *)
  (*       * specialize (H0 false). *)
  (*         destruct H0 as [H0 | H0]. *)
  (*         2: inversion H0. *)
  (*         specialize (IHbs (k false) H0); destruct IHbs as [IH IH']. *)
  (*         split; intro H. *)
  (*         -- pstep; unfold in_itree_lang_; rewrite Ht; constructor. *)
  (*            left; apply IH; auto. *)
  (*         -- punfold H; unfold in_itree_lang_ in H; rewrite Ht in H. *)
  (*            inversion H; subst. *)
  (*            destruct H3 as [H3 | H3]. *)
  (*            2: inversion H3. *)
  (*            apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst. *)
  (*            apply IH'; auto. *)
  (* Qed. *)

  (* Lemma in_itree_reflect (t : itree unbiasedE A) (bs : list bool) : *)
  (*   itree_notau t -> *)
  (*   reflect (in_itree_lang t bs) (in_itree t bs). *)
  (* Proof. *)
  (*   intro Hnotau. *)
  (*   generalize (in_itree_spec t bs Hnotau); intro H. *)
  (*   unfold in_itree. *)
  (*   destruct (in_itree_aux t bs (S (length bs))); constructor. *)
  (*   - apply H; auto. *)
  (*   - intro HC. *)
  (*     assert (false = true). *)
  (*     { apply H; auto. } *)
  (*     congruence. *)
  (* Qed. *)
End in_itree_lang.
Hint Resolve in_itree_lang__mono : paco.

Section itree_lang.
  Context {A : Type} (P : A -> Prop).

  (* CoInductive itree_lang' : itree unbiasedE A -> (nat -> option (list bool)) -> Prop := *)
  (* | itree_lang'_false : forall x, P x = false -> itree_lang' (Ret x) seq_zero *)
  (* | itree_lang'_true : forall x, P x = true -> itree_lang' (Ret x) (seq_one []) *)
  (* | itree_lang'_vis : forall f s1 s2, *)
  (*     itree_lang' (f true) s1 -> *)
  (*     itree_lang' (f false) s2 -> *)
  (*     itree_lang' (Vis GetUnbiased f) (seq_union (option_map (cons true) ∘ s1) *)
  (*                                                (option_map (cons false) ∘ s2)). *)

  (** See Eq/Eq.v in the ITree development for explanation of this
      construction (eqitF, eqit_, etc.). *)
  Inductive itree_langF (R : itree unbiasedE A -> (nat -> option (list bool)) -> Prop)
    : itree' unbiasedE A -> (nat -> option (list bool)) -> Prop :=
  | itree_langF_ret_false : forall x, ~ P x -> itree_langF R (RetF x) seq_zero
  | itree_langF_ret_true : forall x s,
      P x ->
      s === seq_one [] ->
      itree_langF R (RetF x) s
  | itree_langF_tau : forall t s1 s2, R t s1 -> s1 === s2 -> itree_langF R (TauF t) s2
  | itree_langF_vis : forall f s1 s2 s,
      R (f true) s1 ->
      R (f false) s2 ->
      s === seq_union (option_map (cons true) ∘ s1) (option_map (cons false) ∘ s2) ->
      itree_langF R (VisF GetUnbiased f) s.

  Definition itree_lang_ R : itree unbiasedE A -> (nat -> option (list bool)) -> Prop :=
    fun t s => itree_langF R (observe t) s.

  Lemma itree_langF_mono R R' t s
        (IN: itree_langF R t s)
        (LE: R <2= R') :
    itree_langF R' t s.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_lang__mono : monotone2 (itree_lang_).
  Proof. do 2 red. intros. eapply itree_langF_mono; eauto. Qed.
  Hint Resolve itree_lang__mono : paco.

  Definition itree_lang : itree unbiasedE A -> (nat -> option (list bool)) -> Prop :=
    paco2 itree_lang_ bot2.

  Definition itree_lang' r : itree unbiasedE A -> (nat -> option (list bool)) -> Prop :=
    paco2 itree_lang_ r.

  Lemma itree_langF_impl (t : itree' unbiasedE A) s
        (r1 r2 : itree unbiasedE A -> (nat -> option (list bool)) -> Prop) :
    (forall t s, r1 t s -> r2 t s) ->
    itree_langF r1 t s -> itree_langF r2 t s.
  Proof.
    intros H0 H1.
    destruct t; inversion H1; subst.
    - constructor; auto.
    - constructor; auto.
    - econstructor; eauto.
    - apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H2; subst; auto.
      econstructor; eauto.
  Qed.

  Lemma itree_lang_impl
        (t : itree unbiasedE A) s
        (r1 r2 : itree unbiasedE A -> (nat -> option (list bool)) -> Prop) :
    (forall t s, r1 t s -> r2 t s) ->
    paco2 itree_lang_ r1 t s -> paco2 itree_lang_ r2 t s.
  Proof.
    revert t s.
    pcofix CH.
    intros t s H0 H1.
    punfold H1; pstep.
    eapply itree_langF_impl.
    2: { apply H1. }
    intros t' s' [H2 | H2].
    - right; apply CH; auto.
    - right; auto.
  Qed.

  Global Instance Proper_itree_langF R
    : Proper (eq ==> seq_bijection_upto_0 ==> iff) (itree_langF R).
  Proof.
    intros ? t ? s1 s2 Hbij; subst; split; intro H0.
    - induction H0.
      + symmetry in Hbij; apply seq_bijection_upto_0_zero in Hbij.
        subst; constructor; auto.
      + constructor; auto; rewrite <- Hbij; auto.
      + econstructor; eauto; rewrite H0; auto.
      + econstructor; eauto; rewrite <- Hbij; auto.
    - induction H0.
      + apply seq_bijection_upto_0_zero in Hbij; subst; constructor; auto.
      + constructor; auto; rewrite Hbij; auto.
      + econstructor; eauto; rewrite Hbij; auto.
      + econstructor; eauto; rewrite Hbij; auto.
  Qed.

  Lemma itree_lang_lang' r t s :
    itree_lang t s -> itree_lang' r t s.
  Proof.
    revert t s.
    pcofix CH; intros t s.
    unfold itree_lang, itree_lang' in *.
    intro H. pstep.
    punfold H.
    unfold itree_lang_ in *.
    destruct (observe t).
    + inversion H; subst; constructor; auto.
    + inversion H; subst.
      eapply itree_langF_tau; eauto.
      right. apply CH.
      destruct H1. apply H0. inversion H0.
    + destruct e.
      inversion H; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H0; subst.
      econstructor; eauto.
      * destruct H1 as [H1 | H1].
        -- apply CH in H1; right; eauto.
        -- inversion H1.
      * destruct H2 as [H2 | H2].
        -- apply CH in H2; right; eauto.
        -- inversion H2.
  Qed.

  Global Instance Proper_itree_lang' r
    : Proper (eq ==> seq_bijection_upto_0 ==> flip impl) (paco2 itree_lang_ r).
  Proof.
    intros ? t ? s1 s2 Hbij H; subst.
    pstep; punfold H; unfold itree_lang_.
    rewrite Hbij; apply H.
  Qed.

  Global Instance Proper_itree_lang : Proper (eq_itree eq ==> eq ==> flip impl) itree_lang.
  Proof.
    pcofix CH; intros x y Heq s1 s2 ? Hlang; subst.
    punfold Heq; unfold eqit_ in Heq.
    punfold Hlang; unfold itree_lang_ in Hlang.
    pstep; unfold itree_lang_.
    destruct (observe x); inversion Heq; subst;
      try congruence; rewrite <- H in Hlang; clear H.
    - inversion Hlang; subst; constructor; auto.
    - inversion Hlang; subst.
      repeat destruct_upaco.
      econstructor; eauto.
    - destruct e.
      apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
      inversion Hlang; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H; subst.
      repeat destruct_upaco.
      unfold id in REL.
      econstructor; eauto.
      + right; specialize (REL true); destruct_upaco.
        eapply CH in REL; eauto.
      + right; specialize (REL false); destruct_upaco.
        eapply CH in REL; eauto.
  Qed.
End itree_lang.
Hint Resolve itree_lang__mono : paco.

Section itree_lang2.
  Context {A : Type} (P : A -> Prop).

  (** See Eq/Eq.v in the ITree development for explanation of this
      construction (eqitF, eqit_, etc.). *)
  Inductive itree_lang2F (R : itree unbiasedE A ->
                              (nat -> option (list bool)) ->
                              (nat -> option (list bool)) -> Prop)
    : itree' unbiasedE A -> (nat -> option (list bool)) -> (nat -> option (list bool)) -> Prop :=
  | itree_lang2F_ret_false : forall x, ~ P x -> itree_lang2F R (RetF x) seq_zero seq_zero
  | itree_lang2F_ret_true : forall x s1 s2,
      P x ->
      s1 === seq_one [] ->
      s2 === seq_one [] ->
      itree_lang2F R (RetF x) s1 s2
  | itree_lang2F_tau : forall t s1 s1' s2 s2',
      R t s1 s1' ->
      s1 === s2 ->
      s1' === s2' ->
      s2 === s2' ->
      itree_lang2F R (TauF t) s2 s2'
  | itree_lang2F_vis : forall f s1 s1' s2 s2' s s',
      R (f true) s1 s1' ->
      R (f false) s2 s2' ->
      s === seq_union (option_map (cons true) ∘ s1) (option_map (cons false) ∘ s2) ->
      s' === seq_union (option_map (cons true) ∘ s1) (option_map (cons false) ∘ s2) ->
      itree_lang2F R (VisF GetUnbiased f) s s'.

  Definition itree_lang2_ R : itree unbiasedE A ->
                              (nat -> option (list bool)) ->
                              (nat -> option (list bool)) -> Prop :=
    fun t s => itree_lang2F R (observe t) s.

  Lemma itree_lang2F_mono R R' t s1 s2
        (IN: itree_lang2F R t s1 s2)
        (LE: R <3= R') :
    itree_lang2F R' t s1 s2.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_lang2__mono : monotone3 (itree_lang2_).
  Proof. do 2 red. intros. eapply itree_lang2F_mono; eauto. Qed.
  Hint Resolve itree_lang2__mono : paco.

  Definition itree_lang2 : itree unbiasedE A ->
                           (nat -> option (list bool)) ->
                           (nat -> option (list bool)) -> Prop :=
    paco3 itree_lang2_ bot3.
End itree_lang2.

Hint Resolve itree_lang2__mono : paco.

Lemma observe_Ret {A : Type} {E : Type -> Type} (t : itree E A) (x : A) :
  observe t = RetF x ->
  t ≅ Ret x.
Proof.
  intro H; pstep; unfold eqit_; simpl; rewrite H; constructor; reflexivity.
Qed.

Lemma observe_Tau {A : Type} {E : Type -> Type} (t1 t2 : itree E A) :
  observe t1 = TauF t2 ->
  t1 ≅ Tau t2.
Proof.
  intro H; pstep; unfold eqit_; simpl.
  rewrite H; apply EqTau; left; apply Reflexive_eqit_eq.
Qed.

Lemma observe_Vis {A B : Type} {E : Type -> Type} (t : itree E A) (e : E B) (f : B -> itree E A) :
  observe t = VisF e f ->
  t ≅ Vis e f.
Proof.
  intro H; pstep; unfold eqit_; simpl.
  rewrite H; constructor; left; apply Reflexive_eqit_eq.
Qed.

Lemma seq_product_option_mult_comm (s1 s2 : nat -> option (list bool)) (b : bool) :
  seq_product MonoidList (option_map (cons b) ∘ s1) s2 =
  option_map (cons b) ∘ (seq_product MonoidList s1 s2).
Proof.
  replace (option_map (cons b)) with (option_mult MonoidList (Some [b])) by reflexivity.
  apply seq_product_option_mult_comm; apply MonoidLawsList.
Qed.

Lemma itree_lang_langF {A : Type} (P : A -> Prop) r t s :
  itree_lang_ P r t s ->
  itree_langF P r (observe t) s.
Proof. firstorder. Qed.

Lemma itree_langF_lang {A : Type} (P : A -> Prop) r t s :
  itree_langF P r (observe t) s ->
  itree_lang_ P r t s.
Proof. firstorder. Qed.

Lemma itree_lang_unfold_bind {A B : Type} (t : itree unbiasedE A) (k : A -> itree unbiasedE B) s r P :
  paco2 (itree_lang_ P) r (match observe t with
                           | RetF r => k r
                           | TauF t0 => Tau (x <- t0;; k x)
                           | VisF e ke => Vis e (fun x => x <- ke x;; k x)
                           end) s ->
  paco2 (itree_lang_ P) r (x <- t;; k x) s.
Proof.
  revert t k s.
  pcofix CH; intros t k s H.
  punfold H. pstep.
  unfold itree_lang_ in H.
  unfold ITree.bind.
  unfold ITree.subst.
  compute.
  apply itree_lang_langF.
  rewrite _observe_observe.
  destruct (observe t) eqn:Ht.
  - unfold itree_lang_.
    eapply itree_langF_impl.
    2: { eauto. }
    intros t' s' [H0 | H0].
    + left; eapply itree_lang_impl; eauto.
    + right; auto.
  - inversion H; subst.
    econstructor; eauto.
    destruct H1 as [H1 | H1].
    + left; eapply itree_lang_impl; eauto.
    + right; auto.
  - destruct e.
    inversion H; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H0; subst.
    destruct H2 as [H2 | H2]; destruct H1 as [H1 | H1];
      econstructor; eauto; left; eapply itree_lang_impl; eauto.
Qed.

Lemma itree_lang_unfold_iter {A B : Type} P (f : A -> itree unbiasedE (A + B)) x s r :
  paco2 (itree_lang_ P) r (lr <- f x ;; match lr with
                                       | inl l => Tau (ITree.iter f l)
                                       | inr r => Ret r
                                       end) s ->
  paco2 (itree_lang_ P) r (ITree.iter f x) s.
Proof.
  revert f x s.
  pcofix CH; intros f x s H.
  punfold H. pstep.
  unfold itree_lang_ in *.
  unfold ITree.bind in H.
  unfold ITree.subst in H.
  compute in H.
  apply itree_langF_lang.
  rewrite 2!_observe_observe in H.
  unfold ITree.iter. compute.
  apply itree_lang_langF.
  rewrite _observe_observe.
  destruct (observe (f x)) eqn:Hfx.
  - destruct r1.
    + unfold itree_lang_.
      simpl in *.
      inversion H; subst.
      econstructor; eauto.
      destruct H1 as [H1 | H1].
      * left; eapply itree_lang_impl; eauto.
      * right; apply CH0; auto.
    + inversion H; subst; constructor; auto.
  - inversion H; subst.
    econstructor; eauto.
    destruct H1 as [H1 | H1].
    * left; eapply itree_lang_impl; eauto.
    * right; apply CH0; auto.
  - destruct e.
    inversion H; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H0; subst.
    destruct H2 as [H2 | H2]; destruct H1 as [H1 | H1];
      econstructor; eauto; left; eapply itree_lang_impl; eauto.
Qed.

Lemma itree_lang_bind {A : Type} (t1 : itree unbiasedE (unit + A)) (t2 : unit -> itree unbiasedE A)
      (P : A -> Prop) (s1 s1' s2 : nat -> option (list bool))
      (r : itree unbiasedE A -> (nat -> option (list bool)) -> Prop) :
  itree_lang (cotuple (const True) (const False)) t1 s1 ->
  itree_lang (cotuple (const False) P) t1 s1' ->
  r (t2 tt) s2 ->
  paco2 (itree_lang_ P) r (lr <- t1;; match lr with
                                     | inl l => Tau (t2 l)
                                     | inr r => Ret r
                                     end) (seq_union s1' (seq_product MonoidList s1 s2)).
Proof.
  intros H0 H1 H2.
  revert H0 H1.
  revert t1 s1 s1'.
  pcofix CH. intros t1 s1 s1'.
  intros H0 H1.
  apply itree_lang_unfold_bind.
  pstep.
  punfold H0. punfold H1.
  unfold itree_lang_ in *.
  destruct (observe t1) eqn:Ht1.
  - destruct r0 eqn:Hr.
    + inversion H0; subst.
      * simpl in H3; exfalso; apply H3; apply I.
      * clear H3.
        inversion H1; subst.
        2: { inversion H3. }
        clear H3.
        pstep_reverse. rewrite H4.
        rewrite seq_union_zero_l.
        rewrite seq_product_unit_l.
        pstep.
        destruct u.
        econstructor; eauto; reflexivity.
        apply MonoidLawsList.
    + inversion H0; subst.
      2: { inversion H3. }
      clear H3.
      inversion H1; subst; simpl in H3.
      * pstep_reverse.
        rewrite seq_union_zero_l.
        rewrite seq_product_zero_l.
        pstep.
        constructor; auto.
      * constructor; auto.
        rewrite seq_product_zero_l.
        rewrite seq_union_zero_r; auto.
  - econstructor; eauto; try reflexivity.
    right. apply CH.
    + inversion H0; subst. rewrite <- H4. destruct H3.
      apply H. inversion H.
    + inversion H1; subst. rewrite <- H4. destruct H3.
      apply H. inversion H.
  - inversion H0; subst; clear H0.
    destruct e; clear H3.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst.
    inversion H1; subst; clear H1.
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst.
    destruct H7 as [H7 | H7].
    2: { inversion H7. }
    destruct H5 as [H5 | H5].
    2: { inversion H5. }
    destruct H3 as [H3 | H3].
    2: { inversion H3. }
    destruct H0 as [H0 | H0].
    2: { inversion H0. }
    pstep_reverse.
    rewrite H4, H8.
    rewrite seq_product_union_distr_r.
    rewrite 2!seq_product_option_mult_comm.
    rewrite seq_union_comm_4.
    rewrite 2!seq_union_compose.
    pstep.
    econstructor; eauto; reflexivity.
Qed.

Lemma itree_lang_iter_reps_product_P {A : Type} (t : itree unbiasedE (nat + A))
      (s1 s2 : nat -> option (list bool)) P l :
  itree_lang (cotuple (eq l) (const False)) t s1 ->
  itree_lang (cotuple (const False) P) t s2 ->
  itree_lang (cotuple (const False) P)
             (ITree.iter (fun _ => x <- t ;;
                                match x with
                                | inl n =>
                                  if n =? l
                                  then ret (inl tt)
                                  else ret (inr (inl n))
                                | inr y =>
                                  ret (inr (inr y))
                                end) tt)
             (seq_product MonoidList (seq_reps MonoidList s1) s2).
Proof.
  intros Hl Hr.
  pcofix CH.
  apply itree_lang_unfold_iter.
  rewrite seq_reps_unfold.
  rewrite seq_product_union_distr_r.
  rewrite seq_product_unit_l.
  2: { apply MonoidLawsList. }
  rewrite seq_product_assoc.
  2: { apply MonoidLawsList. }
  apply itree_lang_bind; auto.
  - clear CH. clear r. clear Hr. clear s2. clear P.
    revert Hl. revert t l s1.
    pcofix CH.
    intros t l s1 H0.
    apply itree_lang_unfold_bind.
    punfold H0. unfold itree_lang_ in H0.
    destruct (observe t) eqn:Ht.
    + inversion H0; subst.
      * destruct r0.
        -- simpl in H1.
           apply PeanoNat.Nat.eqb_neq in H1.
           rewrite PeanoNat.Nat.eqb_sym in H1.
           rewrite H1.
           pstep; constructor; intuition.
        -- clear H1.
           pstep; constructor; intuition.
      * destruct r0.
        -- simpl in H1; subst.
           rewrite PeanoNat.Nat.eqb_refl.
           pstep; constructor; auto; apply I.
        -- inversion H1.
    + inversion H0; subst.
      destruct H1; subst.
      * pstep; econstructor; eauto.
      * inversion H.
    + inversion H0; subst.
      destruct e; clear H1.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      destruct H5 as [H5 | H5].
      2: { inversion H5. }
      destruct H3 as [H3 | H3].
      2: { inversion H3. }
      pstep; econstructor; eauto; right; apply CH; auto.
  - clear CH. clear r. clear Hl. clear s1.
    revert Hr. revert t l s2.
    pcofix CH.
    intros t l s2 H0.
    apply itree_lang_unfold_bind.
    punfold H0. unfold itree_lang_ in H0.
    destruct (observe t) eqn:Ht.
    + inversion H0; subst.
      * destruct r0.
        -- clear H1. pstep.
           destruct (PeanoNat.Nat.eqb_spec n l); subst; constructor; auto.
        -- simpl in H1.
           pstep; constructor; auto.
      * destruct r0.
        -- inversion H1.
        -- simpl in H1.
           pstep; constructor; auto.
    + inversion H0; subst.
      destruct H1; subst.
      * pstep; econstructor; eauto.
      * inversion H.
    + inversion H0; subst.
      destruct e; clear H1.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      destruct H5 as [H5 | H5].
      2: { inversion H5. }
      destruct H3 as [H3 | H3].
      2: { inversion H3. }
      pstep; econstructor; eauto; right; apply CH; auto.
  - apply MonoidLawsList.
Qed.

Lemma itree_all_itree_lang_iter_P {A : Type} (t : itree unbiasedE (nat + A))
      (s1 s2 : nat -> option (list bool)) P l :
  itree_all (cotuple (eq l) (const True)) t ->
  itree_lang (cotuple (eq l) (const False)) t s1 ->
  itree_lang (cotuple (const False) P) t s2 ->
  itree_lang P (ITree.iter (fun _ => x <- t ;;
                                  match x with
                                  | inl _ => ret (inl tt)
                                  | inr y => ret (inr y)
                                  end) tt)
             (seq_product MonoidList (seq_reps MonoidList s1) s2).
Proof.
  intros Hall Hl Hr.
  pcofix CH.
  apply itree_lang_unfold_iter.
  rewrite seq_reps_unfold.
  rewrite seq_product_union_distr_r.
  rewrite seq_product_unit_l.
  2: { apply MonoidLawsList. }
  rewrite seq_product_assoc.
  2: { apply MonoidLawsList. }
  apply itree_lang_bind; auto.
  - clear CH. clear r. clear Hr. clear s2. clear P.
    revert Hall Hl. revert t s1.
    pcofix CH.
    intros t s1 Hall H0.
    apply itree_lang_unfold_bind.
    punfold H0. unfold itree_lang_ in H0.
    punfold Hall. unfold itree_all_ in Hall.
    destruct (observe t) eqn:Ht.
    + inversion H0; subst.
      * destruct r0.
        -- inversion Hall; subst; simpl in *; congruence.
        -- pstep; constructor; intuition.
      * destruct r0.
        -- pstep; constructor; auto; apply I.
        -- inversion H1.
    + inversion Hall; subst.
      destruct H1 as [H1 | H1].
      2: { inversion H1. }
      inversion H0; subst.
      destruct H2; subst.
      * pstep; econstructor; eauto.
      * inversion H.
    + inversion H0; subst.
      destruct e; clear H1.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      destruct H5 as [H5 | H5].
      2: { inversion H5. }
      destruct H3 as [H3 | H3].
      2: { inversion H3. }
      inversion Hall; subst.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H4; subst.
      pose proof (H1 false) as H2.
      specialize (H1 true).
      destruct H2 as [H2 | H2].
      2: { inversion H2. }
      destruct H1 as [H1 | H1].
      2: { inversion H1. }
      pstep; econstructor; eauto; right; apply CH; auto.
  - clear CH. clear r. clear Hl. clear s1.
    revert Hall Hr. revert t s2.
    pcofix CH.
    intros t s2 Hall H0.
    apply itree_lang_unfold_bind.
    punfold Hall. unfold itree_all_ in Hall.
    punfold H0. unfold itree_lang_ in H0.
    destruct (observe t) eqn:Ht.
    + inversion H0; subst.
      * destruct r0; pstep; constructor; auto.
      * destruct r0.
        -- inversion H1.
        -- simpl in H1.
           pstep; constructor; auto.
    + inversion Hall; subst.
      destruct H1 as [H1 | H1].
      2: { inversion H1. }
      inversion H0; subst.
      destruct H2; subst.
      * pstep; econstructor; eauto.
      * inversion H.
    + inversion H0; subst.
      destruct e; clear H1.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      destruct H5 as [H5 | H5].
      2: { inversion H5. }
      destruct H3 as [H3 | H3].
      2: { inversion H3. }
      inversion Hall; subst.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H4; subst.
      pose proof (H1 false) as H2.
      specialize (H1 true).
      destruct H2 as [H2 | H2].
      2: { inversion H2. }
      destruct H1 as [H1 | H1].
      2: { inversion H1. }
      pstep; econstructor; eauto; right; apply CH; auto.
  - apply MonoidLawsList.
Qed.

Lemma itree_lang_iter_reps_product_lbl {A : Type} (t : itree unbiasedE (nat + A))
      (s1 s2 : nat -> option (list bool)) l m :
  l <> m ->
  itree_lang (cotuple (eq l) (const False)) t s1 ->
  itree_lang (cotuple (eq m) (const False)) t s2 ->
  itree_lang (cotuple (eq m) (const False))
             (ITree.iter (fun _ => x <- t ;;
                                match x with
                                | inl n =>
                                  if n =? l
                                  then ret (inl tt)
                                  else ret (inr (inl n))
                                | inr y =>
                                  ret (inr (inr y))
                                end) tt)
             (seq_product MonoidList (seq_reps MonoidList s1) s2).
Proof.
  intros Hneq Hl Hr.
  pcofix CH.
  apply itree_lang_unfold_iter.
  rewrite seq_reps_unfold.
  rewrite seq_product_union_distr_r.
  rewrite seq_product_unit_l.
  2: { apply MonoidLawsList. }
  rewrite seq_product_assoc.
  2: { apply MonoidLawsList. }
  apply itree_lang_bind; auto.
  - clear CH. clear r. clear Hr. clear s2.
    revert Hneq Hl. revert t l m s1.
    pcofix CH.
    intros t l m s1 Hneq H0.
    apply itree_lang_unfold_bind.
    punfold H0. unfold itree_lang_ in H0.
    destruct (observe t) eqn:Ht.
    + inversion H0; subst.
      * destruct r0.
        -- simpl in H1.
           apply PeanoNat.Nat.eqb_neq in H1.
           rewrite PeanoNat.Nat.eqb_sym in H1.
           rewrite H1.
           pstep; constructor; intuition.
        -- clear H1.
           pstep; constructor; intuition.
      * destruct r0.
        -- simpl in H1; subst.
           rewrite PeanoNat.Nat.eqb_refl.
           pstep; constructor; auto; apply I.
        -- inversion H1.
    + inversion H0; subst.
      destruct H1; subst.
      * pstep; econstructor; eauto.
      * inversion H.
    + inversion H0; subst.
      destruct e; clear H1.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      destruct H5 as [H5 | H5].
      2: { inversion H5. }
      destruct H3 as [H3 | H3].
      2: { inversion H3. }
      pstep; econstructor; eauto; right; apply CH; auto.
  - clear CH. clear r. clear Hl. clear s1.
    revert Hneq Hr. revert t l s2.
    pcofix CH.
    intros t l s2 Hneq H0.
    apply itree_lang_unfold_bind.
    punfold H0. unfold itree_lang_ in H0.
    destruct (observe t) eqn:Ht.
    + inversion H0; subst.
      * destruct r0.
        -- simpl in H1; pstep.
           destruct (PeanoNat.Nat.eqb_spec n l); subst; constructor; auto.
        -- simpl in H1; pstep; constructor; auto.
      * destruct r0.
        -- pstep.
           destruct (PeanoNat.Nat.eqb_spec n l); subst.
           ++ simpl in H1; subst; congruence.
           ++ constructor; auto.
        -- simpl in H1.
           pstep; constructor; auto.
    + inversion H0; subst.
      destruct H1; subst.
      * pstep; econstructor; eauto.
      * inversion H.
    + inversion H0; subst.
      destruct e; clear H1.
      apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
      destruct H5 as [H5 | H5].
      2: { inversion H5. }
      destruct H3 as [H3 | H3].
      2: { inversion H3. }
      pstep; econstructor; eauto; right; apply CH; auto.
  - apply MonoidLawsList.
Qed.
