Set Implicit Arguments.
Set Contextual Implicit.

(* To install ITree, do:
     opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

Require Import Nat.
Require Import PeanoNat.
Require Import Coq.Classes.Equivalence.
Require Import List.
Import ListNotations.

Local Open Scope equiv_scope.
Local Open Scope program_scope.

Require Import itree_regular.
Require Import misc.
Require Import nondivergent.
Require Import order.
Require Import regular.

Lemma seq_one_exists_nil {A : Type} (l : nat -> option (list A)) :
  l === seq_one [] ->
  exists i : nat, l i = Some [].
Proof.
  intros [H0 [f [g H1]]]; exists (f O).
  replace (Some []) with (seq_one (@nil A) O) by reflexivity.
  symmetry; eapply H1; intros HC; inversion HC.
Qed.

Lemma seq_union_exists_l {A : Type} (s s1 s2 : nat -> option (list A)) (i : nat) (x : list A) :
  s1 i = Some x ->
  s === seq_union s1 s2 ->
  exists j : nat, s j = Some x.
Proof.
  intros Heq [H0 [f [g H1]]].
  exists (f (i * 2)).
  assert (H: ~ seq_union s1 s2 (i * 2) === zero).
  { unfold seq_union; intros HC.
    rewrite PeanoNat.Nat.mod_mul, PeanoNat.Nat.div_mul in HC; auto.
    unfold equiv, zero in HC; simpl in HC; congruence. }
  apply H1 in H. destruct H as [_ H].
  unfold seq_union in H.
  rewrite PeanoNat.Nat.mod_mul, PeanoNat.Nat.div_mul in H; auto.
  rewrite <- Heq; auto.
Qed.

Lemma seq_union_exists_r {A : Type} (s s1 s2 : nat -> option (list A)) (i : nat) (x : list A) :
  s2 i = Some x ->
  s === seq_union s1 s2 ->
  exists j : nat, s j = Some x.
Proof.
  intros Heq [H0 [f [g H1]]].
  exists (f (i * 2 + 1)).
  assert (H: ~ seq_union s1 s2 (i * 2 + 1) === zero).
  { unfold seq_union; intros HC.
    rewrite Nat.add_comm, Nat.mod_add, Nat.div_add in HC; auto.
    unfold equiv, zero in HC; simpl in HC; congruence. }
  apply H1 in H. destruct H as [_ H].
  unfold seq_union in H.
  rewrite Nat.add_comm, Nat.mod_add, Nat.div_add in H; auto.
  rewrite <- Heq, Nat.add_1_r; auto.
Qed.

Lemma fintau_exists_some {A} (t : itree unbiasedE A) P s x bs :
  (forall (t : itree unbiasedE A) (l : nat -> option (list bool)) (P : A -> Prop),
         itree_fintau t ->
         itree_lang P t l -> in_itree_lang P t bs -> exists i : nat, l i = Some bs) ->
  fintau t ->
  itree_fintau t ->
  itree_lang P t s ->
  in_itree_lang P t (x :: bs) ->
  exists i : nat, s i = Some (x :: bs).
Proof.
  intros IH Hfin; revert IH s.
  induction Hfin; intros IH s Hfintau Hlang Hin.
  - punfold Hlang; unfold itree_lang_ in Hlang.
    punfold Hin; unfold in_itree_lang_ in Hin.
    punfold Hfintau; unfold itree_fintau_ in Hfintau.
    rewrite H in Hlang; rewrite H in Hin.
    inversion Hlang; subst.
    + inversion Hin; congruence.
    + inversion Hin; subst.
  - punfold Hlang; unfold itree_lang_ in Hlang.
    punfold Hin; unfold in_itree_lang_ in Hin.
    punfold Hfintau; unfold itree_fintau_ in Hfintau.
    rewrite H in Hlang; rewrite H in Hin; rewrite H in Hfintau.
    inversion Hlang; inversion Hin; inversion Hfintau; subst.
    repeat destruct_upaco.
    assert (exists i, s1 i = Some (x :: bs)).
    { apply IHHfin; auto. }
    destruct H0 as [i H0].
    eapply seq_bijection_upto_0_exists_some; eauto.
  - punfold Hlang; unfold itree_lang_ in Hlang.
    punfold Hin; unfold in_itree_lang_ in Hin.
    punfold Hfintau; unfold itree_fintau_ in Hfintau.
    rewrite H in Hlang; rewrite H in Hin; rewrite H in Hfintau.
    destruct e.
    inversion Hlang; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H0; subst.
    inversion Hfintau; subst.
    destruct e0.
    apply Eqdep.EqdepTheory.inj_pair2 in H5; subst; clear H5.
    apply Eqdep.EqdepTheory.inj_pair2 in H6; subst.
    inversion Hin; subst.
    + apply Eqdep.EqdepTheory.inj_pair2 in H0; subst.
      repeat destruct_upaco.
      assert (exists i, s1 i = Some bs).
      { eapply IH; eauto.
        specialize (H4 true); destruct_upaco; auto. }
      destruct H0 as [i H0].
      eapply seq_union_exists_l with (i0:=i); eauto.
      unfold compose; rewrite H0; reflexivity.
    + apply Eqdep.EqdepTheory.inj_pair2 in H0; subst.
      repeat destruct_upaco.
      assert (exists i, s2 i = Some bs).
      { eapply IH; eauto.
        specialize (H4 false); destruct_upaco; auto. }
      destruct H0 as [i H0].
      rewrite seq_union_comm in H3.
      eapply seq_union_exists_l with (i0:=i); eauto.
      unfold compose; rewrite H0; reflexivity.
Qed.
  
Lemma fintau_exists_nil {A} (t : itree unbiasedE A) P s :
  fintau t ->
  itree_lang P t s ->
  in_itree_lang P t [] ->
  exists i : nat, s i = Some [].
Proof.
  intro Hfin; revert s.
  induction Hfin; intros s Hlang Hin.
  - punfold Hlang; unfold itree_lang_ in Hlang.
    punfold Hin; unfold in_itree_lang_ in Hin.
    rewrite H in Hlang; rewrite H in Hin.
    inversion Hlang; subst.
    + inversion Hin; congruence.
    + apply seq_one_exists_nil; auto.
  - punfold Hlang; unfold itree_lang_ in Hlang.
    punfold Hin; unfold in_itree_lang_ in Hin.
    rewrite H in Hlang; rewrite H in Hin.
    inversion Hlang; subst.
    inversion Hin; subst.
    repeat destruct_upaco.
    assert (exists i, s1 i = Some []).
    { apply IHHfin; auto. }
    destruct H0 as [i H0].
    eapply seq_bijection_upto_0_exists_some; eauto.
  - punfold Hlang; unfold itree_lang_ in Hlang.
    punfold Hin; unfold in_itree_lang_ in Hin.
    rewrite H in Hlang; rewrite H in Hin.
    inversion Hin; subst.
Qed.

Lemma itree_lang_in_itree_lang_exists {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
      (l : nat -> option (list bool)) (bs : list bool) :
  itree_fintau t ->
  itree_lang P t l ->
  in_itree_lang P t bs ->
  exists i, l i = Some bs.
Proof.
  revert t l P.
  induction bs; intros t l P Htau Hlang Hin.
  - punfold Hin; unfold in_itree_lang_ in Hin.
    punfold Htau; unfold itree_fintau_ in Htau.
    punfold Hlang; unfold itree_lang_ in Hlang.
    destruct (observe t).
    + inversion Hin; subst.
      inversion Hlang; subst; try congruence.
      apply seq_one_exists_nil; auto.
    + inversion Htau; subst.
      inversion Hlang; subst.
      inversion Hin; subst.
      repeat destruct_upaco.
      eapply fintau_exists_nil; eauto.
      rewrite <- H3; auto.
    + inversion Hin.
  - punfold Hin; unfold in_itree_lang_ in Hin.
    punfold Htau; unfold itree_fintau_ in Htau.
    punfold Hlang; unfold itree_lang_ in Hlang.
    destruct (observe t).
    + inversion Hin.
    + inversion Htau; subst.
      inversion Hlang; subst.
      inversion Hin; subst.
      repeat destruct_upaco.
      eapply fintau_exists_some; eauto.
      rewrite <- H3; auto.
    + destruct e.
      inversion Hlang; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H; subst.
      inversion Htau; subst.
      destruct e0; apply Eqdep.EqdepTheory.inj_pair2 in H5; subst; clear H4.
      inversion Hin; subst; apply Eqdep.EqdepTheory.inj_pair2 in H;
        subst; repeat destruct_upaco.
      * eapply IHbs in H5; eauto.
        -- destruct H5 as [i H5].
           eapply seq_union_exists_l; eauto.
           unfold compose; rewrite H5; reflexivity.
        -- specialize (H3 true); destruct_upaco; auto.
      * eapply IHbs in H5; eauto.
        -- destruct H5 as [i H5].
           eapply seq_union_exists_r; eauto.
           unfold compose; rewrite H5; reflexivity.
        -- specialize (H3 false); destruct_upaco; auto.
Qed.

Lemma itree_lang_in_itree_lang {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
      (l : nat -> option (list bool)) (bs : list bool) (i : nat) :
    itree_fintau t ->
    itree_lang P t l ->
    l i = Some bs ->
    in_itree_lang P t bs.
Proof.
  revert t l bs i.
  pcofix CH; intros t l bs i Htau Hlang Hl.
  punfold Htau; unfold itree_fintau_ in Htau.
  punfold Hlang; unfold itree_lang_ in Hlang.
  pstep; unfold in_itree_lang_.
  destruct (observe t).
  - inversion Hlang; subst; try solve[inversion Hl].
    eapply seq_one_inv with (i0:=i) in H1. destruct H1; try congruence.
    rewrite Hl in H; inversion H; subst; constructor; auto.
  - inversion Htau; subst.
    inversion Hlang; subst.
    repeat destruct_upaco.
    constructor. right.
    assert (exists i, s1 i = Some bs).
    { eapply seq_bijection_upto_0_exists_some; eauto; symmetry; auto. }
    destruct H as [j H].
    eapply CH; eauto.
  - destruct e.
    inversion Htau; subst.
    destruct e0.
    apply Eqdep.EqdepTheory.inj_pair2 in H2; subst; clear H1.
    inversion Hlang; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst.
    repeat destruct_upaco.
    apply seq_union_inv with (i0:=i) in H3.
    unfold compose in H3.
    destruct H3 as [? | [j [H3 | H3]]]; try congruence; rewrite Hl in H3.
    + destruct (s1 j) eqn:Hj; inversion H3; subst.
      constructor; right; eapply CH; eauto.
      specialize (H0 true); destruct_upaco; auto.
    + destruct (s2 j) eqn:Hj; inversion H3; subst.
      constructor; right; eapply CH; eauto.
      specialize (H0 false); destruct_upaco; auto.
Qed.

Lemma itree_fintau_in_itree_lang_iff_exists_some {A : Type}
      (t : itree unbiasedE A) (P : A -> Prop) (l : nat -> option (list bool)) :
    itree_fintau t ->
    itree_lang P t l ->
    forall bs, in_itree_lang P t bs <-> exists i, l i = Some bs.
Proof.
  intros Htau Hlang bs; split; intro H.
  - eapply itree_lang_in_itree_lang_exists; eauto.
  - destruct H; eapply itree_lang_in_itree_lang; eauto.
Qed.

Lemma itree_fintau_itree_lang_iff {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
      (l1 l2 : nat -> option (list bool)) :
  itree_fintau t ->
  itree_lang P t l1 ->
  itree_lang P t l2 ->
  forall bs, (exists i, l1 i = Some bs) <-> (exists j, l2 j = Some bs).
Proof.
  intros Htau Hl1 Hl2 bs.
  apply itree_fintau_in_itree_lang_iff_exists_some with (bs0:=bs) in Hl1; auto.
  apply itree_fintau_in_itree_lang_iff_exists_some with (bs0:=bs) in Hl2; auto.
  intuition.
Qed.

Theorem itree_fintau_itree_lang_unique {A : Type} (t : itree unbiasedE A) (P : A -> Prop)
        (l1 l2 : nat -> option (list bool)) :
  itree_fintau t ->
  itree_lang P t l1 ->
  itree_lang P t l2 ->
  seq_nodup l1 ->
  seq_nodup l2 ->
  l1 === l2.
Proof.
  intros Htau Hl1 Hl2 Hnodupl1 Hnodupl2.
  eapply seq_nodup_iff_bijection; auto.
  eapply itree_fintau_itree_lang_iff; eauto.
Qed.
