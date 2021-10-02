Set Implicit Arguments.

From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

From Coq Require Import
     Basics
     Morphisms
     List
     PeanoNat.

Require Import misc.
Require Import tree.
Require Import unbiased_itree.

Section itree_notau.
  Context {A : Type} {E : Type -> Type}.

  Inductive itree_notauF (R : itree E A -> Prop) : itree' E A -> Prop :=
  | itree_notauF_ret : forall x, itree_notauF R (RetF x)
  | itree_notauF_vis : forall {A} (e : E A) f,
      (forall x, R (f x)) ->
      itree_notauF R (VisF e f).

  Definition itree_notau_ R : itree E A -> Prop :=
    fun t => itree_notauF R (observe t).

  Lemma itree_notauF_mono R R' t
        (IN: itree_notauF R t)
        (LE: R <1= R') :
    itree_notauF R' t.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_notau__mono : monotone1 (itree_notau_).
  Proof. do 2 red. intros. eapply itree_notauF_mono; eauto. Qed.
  Hint Resolve itree_notau__mono : paco.

  Definition itree_notau : itree E A -> Prop :=
    paco1 itree_notau_ bot1.

  Global Instance Proper_itree_notau
    : Proper (eq_itree eq ==> iff) itree_notau.
  Proof.
    intros x y Heq; split.
    - revert x y Heq; pcofix CH; intros x y Heq Hnotau.
      punfold Hnotau; unfold itree_notau_ in Hnotau.
      punfold Heq; unfold eqit_ in Heq.
      pstep; unfold itree_notau_.
      destruct (observe x).
      + inversion Heq; subst; try congruence; constructor.
      + inversion Hnotau.
      + inversion Heq; subst; try congruence.
        apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        inversion Hnotau; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        unfold id in REL.
        constructor; intro z.
        specialize (H1 z).
        specialize (REL z).
        repeat destruct_upaco.
        right; eapply CH; eauto.
    - revert x y Heq; pcofix CH; intros x y Heq Hnotau.
      punfold Hnotau; unfold itree_notau_ in Hnotau.
      punfold Heq; unfold eqit_ in Heq.
      pstep; unfold itree_notau_.
      destruct (observe y).
      + inversion Heq; subst; try congruence; constructor.
      + inversion Hnotau.
      + inversion Heq; subst; try congruence.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        inversion Hnotau; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        unfold id in REL.
        constructor; intro z.
        specialize (H1 z).
        specialize (REL z).
        repeat destruct_upaco.
        right; eapply CH; eauto.
  Qed.
End itree_notau.
Hint Resolve itree_notau__mono : paco.

Section itree_onetau.
  Context {A : Type} {E : Type -> Type}.

  Definition notau (t : itree E A) : Prop :=
    match observe t with
    | RetF _ => True
    | TauF _ => False
    | VisF _ _ => True
    end.

  Lemma notau_eq_itree (t1 t2 : itree E A) :
    eq_itree eq t1 t2 ->
    notau t1 ->
    notau t2.
  Proof.
    unfold notau; intros Heq Hnotau.
    punfold Heq; unfold eqit_ in Heq.
    destruct (observe t1); inversion Heq; congruence.
  Qed.

  Inductive itree_onetauF (R : itree E A -> Prop) : itree' E A -> Prop :=
  | itree_onetauF_ret : forall x, itree_onetauF R (RetF x)
  | itree_onetauF_tau : forall t,
      R t ->
      notau t ->
      itree_onetauF R (TauF t)
  | itree_onetauF_vis : forall {A} (e : E A) f,
      (forall x, R (f x)) ->
      itree_onetauF R (VisF e f).

  Definition itree_onetau_ R : itree E A -> Prop :=
    fun t => itree_onetauF R (observe t).

  Lemma itree_onetauF_mono R R' t
        (IN: itree_onetauF R t)
        (LE: R <1= R') :
    itree_onetauF R' t.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_onetau__mono : monotone1 itree_onetau_.
  Proof. do 2 red. intros. eapply itree_onetauF_mono; eauto. Qed.
  Hint Resolve itree_onetau__mono : paco.

  Definition itree_onetau : itree E A -> Prop :=
    paco1 itree_onetau_ bot1.

  Global Instance Proper_itree_onetau
    : Proper (eq_itree eq ==> iff) itree_onetau.
  Proof.
    intros x y Heq; split.
    - revert x y Heq; pcofix CH; intros x y Heq Htau.
      punfold Htau; unfold itree_onetau_ in Htau.
      punfold Heq; unfold eqit_ in Heq.
      pstep; unfold itree_onetau_.
      destruct (observe x).
      + inversion Heq; subst; try congruence; constructor.
      + inversion Htau; subst.
        inversion Heq; subst; try congruence.
        repeat destruct_upaco.
        constructor.
        * right; eapply CH; eauto.
        * eapply notau_eq_itree; eauto.
      + inversion Heq; subst; try congruence.
        apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        inversion Htau; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        unfold id in REL.
        constructor; intro z.
        specialize (H1 z).
        specialize (REL z).
        repeat destruct_upaco.
        right; eapply CH; eauto.
    - revert x y Heq; pcofix CH; intros x y Heq Htau.
      punfold Htau; unfold itree_onetau_ in Htau.
      punfold Heq; unfold eqit_ in Heq.
      pstep; unfold itree_onetau_.
      destruct (observe y).
      + inversion Heq; subst; try congruence; constructor.
      + inversion Htau; subst.
        inversion Heq; subst; try congruence.
        repeat destruct_upaco.
        constructor.
        * right; eapply CH; eauto.
        * eapply notau_eq_itree; eauto.
          symmetry; auto.
      + inversion Heq; subst; try congruence.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        inversion Htau; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        unfold id in REL.
        constructor; intro z.
        specialize (H1 z).
        specialize (REL z).
        repeat destruct_upaco.
        right; eapply CH; eauto.
  Qed.
End itree_onetau.
Hint Resolve itree_onetau__mono : paco.

Section itree_fintau.
  Context {A : Type} {E : Type -> Type}.

  (* Finite number of taus at the head. *)
  Inductive fintau : itree E A -> Prop :=
  | fintau_ret : forall t x,
      observe t = RetF x ->
      fintau t
  | fintau_tau : forall t t',
      observe t = TauF t' ->
      fintau t' ->
      fintau t
  | fintau_vis : forall X t (e : E X) (k : X -> itree E A),
      observe t = VisF e k ->
      fintau t.

  Lemma fintau_eq_itree (t1 t2 : itree E A) :
    eq_itree eq t1 t2 ->
    fintau t1 ->
    fintau t2.
  Proof.
    intros Heq Hfintau.
    revert Heq. revert t2.
    induction Hfintau; intros t2 Heq.
    - punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      econstructor; eauto.
    - punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      destruct_upaco.
      eapply fintau_tau; eauto.
    - punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      eapply fintau_vis; eauto.
  Qed.

  Inductive itree_fintauF (R : itree E A -> Prop) : itree' E A -> Prop :=
  | itree_fintauF_ret : forall x, itree_fintauF R (RetF x)
  | itree_fintauF_tau : forall t,
      R t ->
      fintau t ->
      itree_fintauF R (TauF t)
  | itree_fintauF_vis : forall {A} (e : E A) f,
      (forall x, R (f x)) ->
      itree_fintauF R (VisF e f).

  Definition itree_fintau_ R : itree E A -> Prop :=
    fun t => itree_fintauF R (observe t).

  Lemma itree_fintauF_mono R R' t
        (IN: itree_fintauF R t)
        (LE: R <1= R') :
    itree_fintauF R' t.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_fintau__mono : monotone1 itree_fintau_.
  Proof. do 2 red. intros. eapply itree_fintauF_mono; eauto. Qed.
  Hint Resolve itree_fintau__mono : paco.

  Definition itree_fintau : itree E A -> Prop :=
    paco1 itree_fintau_ bot1.
  
  Global Instance Proper_fintau
    : Proper (eq_itree eq ==> iff) fintau.
  Proof.
    intros x y Heq; split.
    - intro Hfin; revert Heq. revert y.
      induction Hfin; intros y Heq; punfold Heq; unfold eqit_ in Heq;
        rewrite H in Heq; inversion Heq; subst; try congruence.
      + econstructor; eauto.
      + destruct_upaco; eapply fintau_tau; eauto.
      + eapply fintau_vis; eauto.
    - intro Hfin; revert Heq. revert x.
      induction Hfin; intros z Heq; punfold Heq; unfold eqit_ in Heq;
        rewrite H in Heq; inversion Heq; subst; try congruence.
      + econstructor; eauto.
      + destruct_upaco; eapply fintau_tau; eauto.
      + eapply fintau_vis; eauto.
  Qed.
  
  Global Instance Proper_itree_fintau
    : Proper (eq_itree eq ==> iff) itree_fintau.
  Proof.
    intros x y Heq; split; revert Heq; revert x y;
      pcofix CH; intros x y Heq Hfin;
        punfold Heq; unfold eqit_ in Heq;
          punfold Hfin; unfold itree_fintau_ in Hfin;
            pstep; unfold itree_fintau_.
    - destruct (observe x); inversion Heq; subst; try congruence.
      + constructor.
      + inversion Hfin; subst.
        repeat destruct_upaco.
        constructor; eauto.
        rewrite <- REL; auto.
      + apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        inversion Hfin; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        constructor; intro z.
        specialize (REL z); specialize (H1 z); unfold id in REL.
        repeat destruct_upaco.
        right; eapply CH; eauto.
    - destruct (observe y); inversion Heq; subst; try congruence.
      + constructor.
      + inversion Hfin; subst.
        repeat destruct_upaco.
        constructor; eauto.
        rewrite  REL; auto.
      + apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        inversion Hfin; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
        constructor; intro z.
        specialize (REL z); specialize (H1 z); unfold id in REL.
        repeat destruct_upaco.
        right; eapply CH; eauto.
  Qed.
End itree_fintau.
Hint Resolve itree_fintau__mono : paco.

Lemma onetau_fintau {E : Type -> Type} {A : Type} (t : itree E A) :
  notau t ->
  fintau t.
Proof.
  unfold notau.
  destruct (observe t) eqn:Ht; try contradiction; intros _.
  - eapply fintau_ret; eauto.
  - eapply fintau_vis; eauto.
Qed.

Lemma itree_onetau_itree_fintau {E : Type -> Type} {A : Type} (t : itree E A) :
  itree_onetau t ->
  itree_fintau t.
Proof.
  revert t; pcofix CH; intros t Hone.
  punfold Hone; unfold itree_onetau_ in Hone.
  pstep; unfold itree_fintau_.
  destruct (observe t).
  - constructor.
  - inversion Hone; subst.
    destruct_upaco.
    constructor; auto.
    apply onetau_fintau; auto.
  - inversion Hone; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
    constructor; intro x; right.
    apply CH; specialize (H0 x); destruct_upaco; auto.
Qed.

(** [itree_reachable P t] iff [Ret x] is finitely reachable in t for
    some x such that [P x]. *)
Inductive itree_reachable {E : Type -> Type} {A : Type} (P : A -> Prop) : itree E A -> Prop :=
| itree_reachable_ret : forall x t,
    P x ->
    observe t = RetF x ->
    itree_reachable P t
| itree_reachable_tau : forall t t',
    observe t = TauF t' ->
    itree_reachable P t' ->
    itree_reachable P t
| itree_reachable_vis : forall t X (e : E X) k y,
    observe t = VisF e k ->
    itree_reachable P (k y) ->
    itree_reachable P t.

(* Helper definition for reasoning about iter. *)
Definition ret_reachable {E I R} : itree E (I + R) -> Prop :=
  itree_reachable (fun s => match s with
                         | inl _ => False
                         | inr _ => True
                         end).

Lemma itree_fintau_impl {E A} (t : itree E A) (r1 r2 : itree E A -> Prop) :
  (forall t, r1 t -> r2 t) ->
  paco1 itree_fintau_ r1 t ->
  paco1 itree_fintau_ r2 t.
Proof.
  revert t.
  pcofix CH; intros t Himpl Hfin.
  punfold Hfin; unfold itree_fintau_ in Hfin.
  pstep; unfold itree_fintau_.
  destruct (observe t) eqn:Ht.
  - constructor.
  - inversion Hfin; subst.
    constructor; auto.
    destruct H0 as [H0 | H0]; right; auto.
  - inversion Hfin; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
    constructor; intro x.
    specialize (H0 x); destruct H0; right; auto.
Qed.

Lemma itree_fintau_unfold_iter {E : Type -> Type} {A B : Type} (f : A -> itree E (A + B)) x r :
  paco1 itree_fintau_ r (lr <- f x ;; match lr with
                                     | inl l => Tau (ITree.iter f l)
                                     | inr r => Ret r
                                     end) ->
  paco1 itree_fintau_ r (ITree.iter f x).
Proof.
  revert f x r.
  pcofix CH; intros f x H.
  punfold H; unfold itree_fintau_ in H.
  unfold ITree.bind in H.
  unfold ITree.subst in H.
  compute in H.
  pstep; unfold itree_fintau_.
  rewrite 2!_observe_observe in H.
  unfold ITree.iter. compute.
  rewrite 2!_observe_observe.
  destruct (observe (f x)) eqn:Hfx; simpl in *.
  - destruct r1; simpl in *.
    + inversion H; subst.
      constructor; auto.
      destruct H1 as [H1 | H1]; auto.
      left; eapply itree_fintau_impl; eauto.
    + constructor.
  - inversion H; subst.
    constructor; auto.
    destruct H1 as [H1 | H1]; auto.
    left; eapply itree_fintau_impl; eauto.
  - inversion H; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
    constructor.
    intro y; specialize (H1 y).
    destruct H1 as [H1 | H1]; auto.
    left; eapply itree_fintau_impl; eauto.
Qed.

Lemma fintau_subst {E I R} t k :
  fintau t ->
  (forall i, fintau (k i)) ->
  fintau
    ((cofix _subst (u : itree E (I + R)) : itree E R :=
        match _observe u with
        | RetF (inl l) => Tau (k l)
        | RetF (inr r2) => Ret r2
        | TauF t0 => Tau (_subst t0)
        | @VisF _ _ _ X e h => Vis e (fun x : X => _subst (h x))
        end) t).
Proof.
  intro Hfin; revert k; induction Hfin; intros f Hk.
  - destruct x.
    + eapply fintau_tau; compute.
      * rewrite 2!_observe_observe.
        rewrite H; reflexivity.
      * auto.
    + eapply fintau_ret; compute.
      * rewrite 2!_observe_observe.
        rewrite H; reflexivity.
  - eapply fintau_tau; compute.
    * rewrite 2!_observe_observe.
      rewrite H; reflexivity.
    * apply IHHfin; auto.
  - eapply fintau_vis; compute.
    * rewrite 2!_observe_observe.
      rewrite H; reflexivity.
Qed.

Lemma itree_fintau_bind {E I R} (t : itree E (I + R)) k (r : itree E R -> Prop) :
  itree_fintau t ->
  (forall i, r (k i)) ->
  (forall i, fintau (k i)) ->
  paco1 itree_fintau_ r
        (lr <- t;; match lr with
                  | inl l => Tau (k l)
                  | inr r0 => Ret r0
                  end).
Proof.
  revert t k r; pcofix CH; intros t k Hfintau Hr Hfin.
  (* revert t k r; pcofix CH; intros t k Hr Hfin. *)
  unfold ITree.bind, ITree.subst.
  pstep; unfold itree_fintau_.
  compute.
  rewrite 2!_observe_observe.
  destruct (observe t) eqn:Ht; simpl.
  - destruct r1; constructor; auto.
  - punfold Hfintau; unfold itree_fintau_ in Hfintau.
    rewrite Ht in Hfintau; inversion Hfintau; subst.
    destruct_upaco.
    constructor.
    + right; apply CH; auto.
    + apply fintau_subst; auto.
  - constructor; intro x.
    punfold Hfintau; unfold itree_fintau_ in Hfintau.
    rewrite Ht in Hfintau; inversion Hfintau; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
    right; apply CH; auto.
    + specialize (H0 x); destruct_upaco; auto.
Qed.

Lemma itree_fintau_iter {E I R} (k : I -> itree E (I + R)) (i : I) :
  (forall j, itree_fintau (k j)) ->
  (forall j, fintau (ITree.iter k j)) ->
  (forall j, ret_reachable (k j)) ->
  itree_fintau (ITree.iter k i).
Proof.
  revert k i; pcofix CH; intros k i Hfin Hfin' Hreach.
  apply itree_fintau_unfold_iter.
  apply itree_fintau_bind; auto.
Qed.

Lemma fintau_bind {E A B} (t : itree E A) (f : A -> itree E B) :
  fintau t ->
  (forall x, fintau (f x)) ->
  fintau (x <- t;; f x).
Proof.
  induction 1; intros Hfin.
  - unfold ITree.bind, ITree.subst.
    destruct (observe (f x)) eqn:Hfx.
    + eapply fintau_ret; compute.
      rewrite 2!_observe_observe, H; eauto.
    + eapply fintau_tau; compute.
      rewrite 2!_observe_observe, H; eauto.
      specialize (Hfin x).
      inversion Hfin; congruence.
    + eapply fintau_vis; compute.
      rewrite 2!_observe_observe, H; eauto.
  - unfold ITree.bind, ITree.subst.
    eapply fintau_tau.
    + compute; rewrite 2!_observe_observe, H; reflexivity.
    + apply IHfintau; auto.
  - eapply fintau_vis; compute.
    rewrite 2!_observe_observe; rewrite H; reflexivity.
Qed.

Lemma itree_fintau_fintau {E A} (t : itree E A) :
  itree_fintau t ->
  fintau t.
Proof.
  intro Hfin.
  punfold Hfin; unfold itree_fintau_ in Hfin.
  destruct (observe t) eqn:Ht.
  - eapply fintau_ret; eauto.
  - inversion Hfin; subst; eapply fintau_tau; eauto.
  - eapply fintau_vis; eauto.
Qed.

Lemma itree_fintau_bind' {E A B} (t : itree E A) (f : A -> itree E B) :
  itree_fintau t ->
  (forall x, itree_fintau (f x)) ->
  itree_fintau (x <- t;; f x).
Proof.
  revert t f.
  pcofix CH; intros t f H0 H1.
  punfold H0; unfold itree_fintau_ in H0.
  pstep; unfold itree_fintau_.
  compute.
  rewrite 2!_observe_observe.
  destruct (observe t) eqn:Ht.
  - specialize (H1 r0).
    eapply itree_fintau_impl in H1.
    + punfold H1.
    + intros ? [].
  - inversion H0; subst.
    destruct_upaco.
    constructor.
    + right; apply CH; auto.
    + apply fintau_bind; auto.
      intro x; apply itree_fintau_fintau; auto.
  - inversion H0; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst.
    constructor; intro x.
    specialize (H2 x); destruct_upaco; right; apply CH; auto.
Qed.

Instance Proper_itree_reachable {E A P} : Proper (eq_itree eq ==> iff) (@itree_reachable E A P).
Proof.
  intros x y Heq; split; intro H.
  - revert Heq. revert y.
    induction H; intros z Heq.
    + punfold Heq; unfold eqit_ in Heq; rewrite H0 in Heq.
      inversion Heq; subst; try congruence.
      eapply itree_reachable_ret; eauto.
    + punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      destruct_upaco.
      eapply itree_reachable_tau; eauto.
    + punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H4; subst.
      eapply itree_reachable_vis; eauto.
      specialize (REL y); unfold id in REL.
      destruct_upaco.
      apply IHitree_reachable; eauto.
  - revert Heq. revert x.
    induction H; intros z Heq.
    + punfold Heq; unfold eqit_ in Heq; rewrite H0 in Heq.
      inversion Heq; subst; try congruence.
      eapply itree_reachable_ret; eauto.
    + punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      destruct_upaco.
      eapply itree_reachable_tau; eauto.
    + symmetry in Heq; punfold Heq; unfold eqit_ in Heq; rewrite H in Heq.
      inversion Heq; subst; try congruence.
      apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H4; subst.
      eapply itree_reachable_vis; eauto.
      specialize (REL y); unfold id in REL.
      destruct_upaco.
      apply IHitree_reachable; eauto.
      symmetry; eauto.
Qed.

Instance Proper_ret_reachable {E I R} : Proper (eq_itree eq ==> iff) (@ret_reachable E I R).
Proof. apply Proper_itree_reachable. Qed.

Lemma ret_reachable_bind {E A B C} (t : itree E (A + (B + C))) (k : A -> itree E (B + C)) :
  itree_reachable (fun x => match x with
                         | inr (inr _) => True
                         | _ => False
                         end) t ->
  ret_reachable (lr <- t;; match lr with
                          | inl l => k l
                          | inr r => Ret r
                          end).
Proof.
  unfold ret_reachable.
  intro H.
  induction H.
  - destruct x; try contradiction.
    destruct s; try contradiction.
    econstructor.
    2: { compute; rewrite 2!_observe_observe, H0; reflexivity. }
    apply I.
  - eapply itree_reachable_tau; eauto.
    compute; rewrite 2!_observe_observe, H; reflexivity.
  - eapply itree_reachable_vis.
    + compute; rewrite 2!_observe_observe, H; reflexivity.
    + apply IHitree_reachable.
Qed.

Lemma itree_reachable_bind' {E A B} (t : itree E (A + B)) (k : A -> itree E B) :
  itree_reachable (fun x => match x with
                         | inr _ => True
                         | _ => False
                         end) t ->
  itree_reachable (const True) (lr <- t;; match lr with
                                      | inl l => k l
                                      | inr r => Ret r
                                      end).
Proof.
  unfold ret_reachable.
  intro H.
  induction H.
  - destruct x; try contradiction.
    econstructor.
    2: { compute; rewrite 2!_observe_observe, H0; reflexivity. }
    apply I.
  - eapply itree_reachable_tau; eauto.
    compute; rewrite 2!_observe_observe, H; reflexivity.
  - eapply itree_reachable_vis.
    + compute; rewrite 2!_observe_observe, H; reflexivity.
    + apply IHitree_reachable.
Qed.

Lemma ret_reachable_iter {E A B} (k : unit -> itree E (unit + (A + B))) :
  itree_reachable (fun x => match x with
                         | inr (inr _) => True
                         | _ => False
                         end) (k tt) ->
  ret_reachable (ITree.iter k tt).
Proof. rewrite unfold_iter; apply ret_reachable_bind. Qed.

Lemma ret_reachable_iter' {E R} (k : unit -> itree E (unit + R)) :
  itree_reachable (fun x => match x with
                         | inr _ => True
                         | _ => False
                         end) (k tt) ->
  itree_reachable (const True) (ITree.iter k tt).
Proof. rewrite unfold_iter; apply itree_reachable_bind'. Qed.

Lemma ret_reachable_bind' {E A} (t : itree E (nat + A)) n :
  ret_reachable t ->
  itree_reachable
    (fun x : unit + (nat + A) => match x with
                                 | inr (inr _) => True
                                 | _ => False
                                 end)
    (x <- t;;
     match x with
     | inl n0 => if PeanoNat.Nat.eqb n0 n then Ret (inl tt) else Ret (inr (inl n0))
     | inr y => Ret (inr (inr y))
     end).
Proof.
  intro H; induction H; subst.
  - destruct x; try contradiction.
    eapply itree_reachable_ret.
    2: { compute; rewrite 2!_observe_observe, H0; reflexivity. }
    apply I.
  - eapply itree_reachable_tau; eauto.
    compute; rewrite 2!_observe_observe, H; reflexivity.
  - eapply itree_reachable_vis.
    + compute; rewrite 2!_observe_observe, H; reflexivity.
    + apply IHitree_reachable.
Qed.
                  
Lemma leaf_reachable'_ret_reachable {A : Type} (t : tree A) :
  leaf_reachable' t ->
  ret_reachable (unbiased_tree_to_itree t).
Proof.
  induction 1; simpl.
  - econstructor.
    2: reflexivity.
    apply I.
  - eapply itree_reachable_vis with (y:=true).
    + reflexivity.
    + apply IHleaf_reachable'.
  - eapply itree_reachable_vis with (y:=false).
    + reflexivity.
    + apply IHleaf_reachable'.
  - apply ret_reachable_iter.
    apply ret_reachable_bind'; auto.
Qed.

Lemma itree_reachable_fintau {E A} P (t : itree E A) :
  itree_reachable P t ->
  fintau t.
Proof.
  induction 1.
  - econstructor; eauto.
  - eapply fintau_tau; eauto.
  - eapply fintau_vis; eauto.
Qed.

Lemma itree_reachable_impl {E A} (P Q : A -> Prop) (t : itree E A) :
  (forall x, P x -> Q x) ->
  itree_reachable P t ->
  itree_reachable Q t.
Proof.
  intros Himpl H; induction H.
  - eapply itree_reachable_ret; eauto.
  - eapply itree_reachable_tau; eauto.
  - eapply itree_reachable_vis; eauto.
Qed.

Lemma itree_reachable_n_bind {E A} (t : itree E (nat + A)) (n : nat) :
  itree_reachable (fun x => match x with
                         | inl m => m <> n
                         | _ => False
                         end) t ->
  itree_reachable (fun x => match x with
                         | inl _ => False
                         | inr _ => True
                         end)
                  (x <- t;;
                   match x with
                   | inl n1 => if n1 =? n then Ret (inl tt) else Ret (inr (inl n1))
                   | inr y => Ret (inr (inr y))
                   end).
Proof.
  induction 1.
  - destruct x; try contradiction.
    eapply itree_reachable_ret.
    2: { compute; rewrite 2!_observe_observe, H0.
         apply Nat.eqb_neq in H; compute in H; rewrite H; reflexivity. }
    apply I.
  - eapply itree_reachable_tau; eauto.
    compute; rewrite 2!_observe_observe, H; reflexivity.
  - eapply itree_reachable_vis.
    { compute; rewrite 2!_observe_observe, H; reflexivity. }
    apply IHitree_reachable.
Qed.

Lemma itree_reachable_n_bind' {E A} (t : itree E (nat + A)) (n k : nat) :
  k <> n ->
  itree_reachable (fun x => match x with
                         | inl m => m = k
                         | _ => False
                         end) t ->
  itree_reachable (fun x => match x with
                         | inl _ => False
                         | inr _ => True
                         end)
                  (x <- t;;
                   match x with
                   | inl n1 => if n1 =? n then Ret (inl tt) else Ret (inr (inl n1))
                   | inr y => Ret (inr (inr y))
                   end).
Proof.
  intros Hneq H. revert Hneq. revert n.
  induction H; intros n Hneq.
  - destruct x; subst; try contradiction.
    eapply itree_reachable_ret.
    2: { compute; rewrite 2!_observe_observe, H0.
         apply Nat.eqb_neq in Hneq; compute in Hneq; rewrite Hneq; reflexivity. }
    apply I.
  - eapply itree_reachable_tau; eauto.
    compute; rewrite 2!_observe_observe, H; reflexivity.
  - eapply itree_reachable_vis.
    { compute; rewrite 2!_observe_observe, H; reflexivity. }
    apply IHitree_reachable; auto.
Qed.

Lemma itree_reachable_bind {E A B} (t : itree E (unit + (A + B))) k P :
  itree_reachable (fun x => match x with
                         | inl _ => False
                         | inr y => P y
                         end) t ->
  itree_reachable P
    (lr <- t;; match lr with
              | inl l => k l
              | inr r => Ret r
              end).
Proof.
  induction 1.
  - destruct x; try contradiction.
    eapply itree_reachable_ret; eauto.
    compute; rewrite 2!_observe_observe, H0; reflexivity.
  - eapply itree_reachable_tau; eauto.
    compute; rewrite 2!_observe_observe, H; reflexivity.
  - eapply itree_reachable_vis.
    { compute; rewrite 2!_observe_observe, H; reflexivity. }
    apply IHitree_reachable.
Qed.

Lemma itree_reachable_iter {E A B} (k : unit -> itree E (unit + (A + B))) P :
  itree_reachable (fun x => match x with
                         | inr y => P y
                         | _ => False
                         end) (k tt) ->
  itree_reachable P (ITree.iter k tt).
Proof. rewrite unfold_iter; apply itree_reachable_bind. Qed.

Lemma itree_reachable_n_bind'' {E A} (t : itree E (nat + A)) (f : unit -> itree E (nat + A)) (k n : nat) :
  k <> n ->
  itree_reachable (fun x => match x with
                         | inl m => m = k
                         | inr _ => False
                         end) t ->
  itree_reachable (fun x => match x with
                         | inl m => m = k
                         | inr _ => False
                         end)
                  (lr <-
                   (x <- t;;
                    match x with
                    | inl n0 => if n0 =? n then Ret (inl tt) else Ret (inr (inl n0))
                    | inr y => Ret (inr (inr y))
                    end);;
                   match lr with
                   | inl l => f l
                   | inr r => Ret r
                   end).
Proof.
  intros Hneq H.
  revert Hneq. revert n.
  induction H; intros n Hneq.
  - destruct x; try contradiction; subst.
    eapply itree_reachable_ret.
    2: { compute; rewrite 3!_observe_observe, H0.
         apply Nat.eqb_neq in Hneq; compute in Hneq; rewrite Hneq.
         reflexivity. }
    reflexivity.
  - eapply itree_reachable_tau.
    { compute; rewrite 3!_observe_observe, H.
      reflexivity. }
    apply IHitree_reachable; auto.
  - eapply itree_reachable_vis.
    { compute; rewrite 3!_observe_observe, H.
      reflexivity. }
    apply IHitree_reachable; auto.
Qed.

Lemma itree_reachable_n_iter {E A} (t : itree E (nat + A)) k n :
  k <> n ->
  itree_reachable (fun x => match x with
                         | inl m => m = k
                         | inr _ => False
                         end) t ->
  itree_reachable (fun x => match x with
                         | inl m => m = k
                         | inr _ => False
                         end)
    (ITree.iter
       (fun _ : unit =>
        x <- t;;
        match x with
        | inl n0 => if n0 =? n then Ret (inl tt) else Ret (inr (inl n0))
        | inr y => Ret (inr (inr y))
        end) tt).
Proof.
  intros Hneq H.
  rewrite unfold_iter.
  apply itree_reachable_n_bind''; auto.
Qed.

Lemma fail_reachable'_itree_reachable {A} (t : tree A) (k : nat) :
  not_bound_in k t ->
  fail_reachable' k t ->
  itree_reachable (fun x => match x with
                         | inl m => m = k
                         | inr _ => False
                         end) (unbiased_tree_to_itree t).
Proof.
  intros Hnotbound H.
  revert Hnotbound.
  induction H; simpl; intros Hnotbound.
  - eapply itree_reachable_ret; try reflexivity.
    apply eq_refl.
  - inversion Hnotbound; subst.
    eapply itree_reachable_vis with (y:=true); try reflexivity.
    apply IHfail_reachable'; auto.
  - inversion Hnotbound; subst.
    eapply itree_reachable_vis with (y:=false); try reflexivity.
    apply IHfail_reachable'; auto.
  - inversion Hnotbound; subst.
    apply itree_reachable_n_iter; auto.
Qed.

Lemma kdfg {A} (t : tree A) (k n : nat) :
  not_bound_in k t ->
  fail_reachable' k t ->
  k <> n ->
  itree_reachable (const True)
                  (ITree.iter
                     (fun _ : unit =>
                        x <- unbiased_tree_to_itree t;;
                        match x with
                        | inl n1 => if n1 =? n then Ret (inl tt) else Ret (inr (inl n1))
                        | inr y => Ret (inr (inr y))
                        end) tt).
Proof.
  intros Hnotbound Hfail Hneq.
  apply ret_reachable_iter'.
  apply itree_reachable_n_bind' with k; auto.
  apply fail_reachable'_itree_reachable; auto.
Qed.

Lemma nondivergent'_itree_fintau {A : Type} (t : tree A) (lbls : list nat) :
  wf_tree t ->
  (forall n, bound_in n t -> ~ In n lbls) ->
  nondivergent' lbls t ->
  itree_fintau (unbiased_tree_to_itree t).
Proof.
  revert lbls.
  induction t; simpl; intros lbls Hwf Hnotin Hnd.
  - pstep; constructor.
  - pstep; constructor.
  - inversion Hnd; subst.
    inversion Hwf; subst.
    pstep; constructor; intros []; left.
    + eapply IHt1; eauto.
      intros n Hbound Hin; eapply Hnotin; eauto; constructor; auto.
    + eapply IHt2; eauto.
      intros n Hbound Hin; eapply Hnotin; eauto; solve[constructor; auto].
  - inversion Hnd; subst.
    inversion Hwf; subst.
    destruct H2 as [Hleaf | [k [Hin Hreach]]].
    + apply itree_fintau_iter.
      * intros _; apply itree_fintau_bind'; eauto.
        -- eapply IHt; eauto.
           intros m Hbound Hin.
           destruct (Nat.eqb_spec n m); subst.
           ++ apply bound_in_not_bound_in in H4; congruence.
           ++ destruct Hin; try congruence.
              eapply Hnotin; eauto; constructor; auto.
        -- intros [m | x].
           ++ destruct (PeanoNat.Nat.eqb m n); pstep; constructor.
           ++ pstep; constructor.
      * intros [].
        eapply itree_reachable_fintau, ret_reachable_iter, ret_reachable_bind'.
        apply leaf_reachable'_ret_reachable, leaf_reachable_leaf_reachable'; auto.
      * intros _.
        eapply itree_reachable_impl.
        2: { apply ret_reachable_bind'.
             apply leaf_reachable'_ret_reachable.
             apply leaf_reachable_leaf_reachable'; auto. }
        intros [? | [? | ?]]; auto.
    + destruct (Nat.eqb_spec k n); subst.
      { exfalso; eapply Hnotin; eauto; constructor. }
      apply itree_fintau_iter.
      * intros _; apply itree_fintau_bind'; eauto.
        -- eapply IHt; eauto.
           intros m Hbound Hin'.
           destruct (Nat.eqb_spec m n); subst.
           ++ apply bound_in_not_bound_in in H4; congruence.
           ++ destruct Hin'; try congruence.
              eapply Hnotin; eauto; constructor; auto.
        -- intros [m | x].
           ++ destruct (PeanoNat.Nat.eqb m n); pstep; constructor.
           ++ pstep; constructor.
      * intros [].
        eapply itree_reachable_fintau.
        eapply kdfg.
        2: { apply fail_reachable_fail_reachable'; eauto. }
        -- apply bound_in_not_bound_in; intro Hbound.
           eapply Hnotin; eauto.
           constructor; auto.
        -- auto.
      * intros [].
        eapply itree_reachable_impl.
        2: {
          eapply itree_reachable_n_bind'; eauto.
          apply fail_reachable'_itree_reachable; auto.
          -- apply bound_in_not_bound_in; intro Hbound.
             eapply Hnotin; eauto.
             constructor; auto.
          -- apply fail_reachable_fail_reachable'; auto. }
        intros [? | [? | ?]]; auto.
Qed.

Lemma itree_reachable_bind'' {E A} (t : itree E (nat + A)) :
  itree_reachable (fun x => match x with
                         | inl _ => False
                         | inr _ => True
                         end) t ->
  itree_reachable (fun x : unit + A => match x with
                                    | inl _ => False
                                    | inr _ => True
                                    end)
                  (x <- t;;
                   match x with
                   | inl _ => ret (inl tt)
                   | inr r => ret (inr r)
                   end).
Proof.
  induction 1.
  - destruct x; try contradiction.
    eapply itree_reachable_ret.
    2: { compute; rewrite 2!_observe_observe, H0; reflexivity. }
    apply I.
  - eapply itree_reachable_tau.
    { compute; rewrite 2!_observe_observe, H; reflexivity. }
    apply IHitree_reachable.
  - eapply itree_reachable_vis.
    { compute; rewrite 2!_observe_observe, H; reflexivity. }
    apply IHitree_reachable.
Qed.

Theorem nondivergent''_itree_fintau {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  nondivergent'' n t ->
  itree_fintau (unbiased_tree_to_itree' t).
Proof.
  intros Hwf Hnotbound Hnd.
  unfold nondivergent'' in Hnd.
  unfold unbiased_tree_to_itree'.
  unfold tie_itree'.
  inversion Hnd; subst.
  apply itree_fintau_iter.
  - intros _.
    apply itree_fintau_bind'.
    + eapply nondivergent'_itree_fintau; eauto.
      intros m Hbound [? | []]; subst.
      apply bound_in_not_bound_in in Hnotbound; congruence.
    + intros []; pstep; constructor.
  - intros [].
    destruct H2 as [Hleaf | [k [Hin Hreach]]].
    + eapply itree_reachable_fintau, ret_reachable_iter', itree_reachable_bind''.
      apply leaf_reachable'_ret_reachable, leaf_reachable_leaf_reachable'; auto.
    + inversion Hin.
  - intros [].
    destruct H2 as [Hleaf | [k [Hin Hreach]]].
    + apply itree_reachable_bind''.
      apply leaf_reachable'_ret_reachable, leaf_reachable_leaf_reachable'; auto.
    + inversion Hin.
Qed.
