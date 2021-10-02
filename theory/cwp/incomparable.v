Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import List.

Require Import axioms.
Require Import borel.
Require Import misc.
Require Import order.
Require Import regular.
Require Import tree.

Import ListNotations.
Local Open Scope program_scope.

Lemma seq_incomparable''_seq_incomparable' {A : Type} (s : nat -> option (list A)) :
  seq_incomparable'' s ->
  seq_incomparable' s.
Proof. unfold seq_incomparable'', seq_incomparable'; intuition. Qed.

Lemma seq_incomparable_seq_product {A : Type} (s1 s2 : nat -> option (list A)) :
  seq_incomparable s1 ->
  seq_incomparable s2 ->
  seq_incomparable (seq_product MonoidList s1 s2).
Proof.
  intros Hs1 Hs2 i j x y Hneq H0 H1.
  unfold seq_product in *.
  destruct (nat_f i) eqn:Hi.
  destruct (nat_f j) eqn:Hj.
  destruct (s1 n) eqn:Hn, (s2 n0) eqn:Hn0, (s1 n1) eqn:Hn1, (s2 n2) eqn:Hn2;
    inversion H0; inversion H1; subst.
  destruct (Nat.eqb_spec n n1); subst.
  - rewrite Hn in Hn1; inversion Hn1; subst.
    destruct (Nat.eqb_spec n0 n2); subst.
    + rewrite Hn0 in Hn2; inversion Hn2; subst.
      rewrite <- Hi in Hj; apply nat_f_inj in Hj; congruence.
    + apply incomparable_app_r; eapply Hs2; eauto.
  - apply incomparable_app_l; eapply Hs1; eauto.
Qed.

Fixpoint option_seq {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | None :: l' => None
  | Some x :: l' => match option_seq l' with
                  | None => None
                  | Some l'' => Some (x :: l'')
                  end
  end.

Lemma option_seq_app {A : Type} (l1 l2 : list (option A)) :
  option_seq (l1 ++ l2) =
  match (option_seq l1, option_seq l2) with
  | (Some l1', Some l2') => Some (l1' ++ l2')
  | (_, _) => None
  end.
Proof.
  revert l2; induction l1; intros l2; simpl.
  - destruct (option_seq l2); auto.
  - destruct a; auto; rewrite IHl1.
    destruct (option_seq l1), (option_seq l2); reflexivity.
Qed.

Lemma nat_iter_product {A : Type} s1 s2 n k x :
  Nat.iter n (fun f' : nat -> option (list A) => seq_product MonoidList f' s2) s1 k = Some x ->
  (exists i y, s1 i = Some y /\
          exists js z, length js = n /\
                  option_map (@concat _) (option_seq (map s2 js)) = Some z /\
                  x = y ++ z) \/
  (exists j y, s2 j = Some y /\ exists z, x = y ++ z).
Proof.
  revert s1 s2 k x.
  induction n; simpl; intros s1 s2 k x H.
  - left; exists k, x; split; auto;
      exists nil, nil; repeat split; auto; rewrite app_nil_r; reflexivity.
  - unfold seq_product in H.
    destruct (nat_f k).
    unfold option_mult in H. simpl in H.
    destruct (Nat.iter n
                       (fun (f' : nat -> option (list A)) (n : nat) =>
                          let (i, j) := nat_f n in
                          match f' i with
                          | Some l => match s2 j with
                                     | Some r => Some (l ++ r)
                                     | None => None
                                     end
                          | None => None
                          end) s1 n0) eqn:Hiter.
    + apply IHn in Hiter.
      destruct Hiter as [[i [y [H0 [js [z [H1 [H2 H3]]]]]]] | [j [y [H0 [z H1]]]]]. subst.
      * destruct (s2 n1) eqn:Hn1; inversion H; subst; clear H.
        left; exists i, y; split; auto.
        exists (js ++ [n1]), (z ++ l); repeat split.
        -- rewrite app_length; apply Nat.add_1_r.
        -- rewrite map_app. simpl.
           rewrite option_seq_app.
           destruct (option_seq (map s2 js)); inversion H2; subst.
           rewrite Hn1; simpl; rewrite concat_app; simpl; rewrite app_nil_r; reflexivity.
        -- rewrite app_assoc; reflexivity.
      * destruct (s2 n1) eqn:Hn1; inversion H; subst; clear H.
        right; exists j, y; split; auto.
        exists (z ++ l0); rewrite app_assoc; reflexivity.
    + inversion H.
Qed.

Lemma seqs_incomparable'_seq_reps {A : Type} `{EqType A} (s1 s2 : nat -> option (list A)) :
  seqs_incomparable s1 s2 ->
  seqs_incomparable' (seq_reps MonoidList s1) s2.
Proof.
  unfold seqs_incomparable, seqs_incomparable'.
  intros Hinc i j.
  unfold seq_reps, seq_flatten, seq_reps_n, seq_product_n.
  destruct (nat_f i) eqn:Hi.
  destruct n.
  - destruct n0.
    + left; reflexivity.
    + right; intros ? ? H'; inversion H'.
  - right; intros x y H0 H1.
    apply nat_iter_product in H0.
    simpl in H0.
    destruct H0 as [[i' [y' [H0 [js [z' [H1' [H2 H3]]]]]]] | [j' [y' [H0 [z H1']]]]]; subst.
    + destruct i'; inversion H0; subst; simpl; clear H0.
      destruct (option_seq (map s1 js)) eqn:Hjs; inversion H1'; subst; clear H1'.
      * destruct js; inversion H3; subst; clear H3.
        destruct l.
        -- simpl in Hjs.
           destruct (s1 n1) eqn:Hn1; try solve[inversion Hjs].
           destruct (option_seq (map s1 js)); inversion Hjs.
        -- inversion Hjs; subst; clear Hjs.
           destruct (s1 n1) eqn:Hn1.
           ++ destruct (option_seq (map s1 js)); inversion H3; subst; clear H3.
              inversion H2; subst.
              symmetry; apply incomparable_app_l'.
              symmetry; eapply Hinc; eauto.
           ++ inversion H3.
      * inversion H2.
    + symmetry; eapply incomparable_app_l'.
      symmetry; eapply Hinc; eauto.
Qed.

Lemma seq_reps_concat {A : Type} (s : nat -> option (list A)) (n : nat) (x : list A) :
  seq_reps MonoidList s n = Some x ->
  exists l : list (list A), x = concat l /\ forall y, In y l -> exists j, s j = Some y.
Proof.
  unfold seq_reps, seq_flatten, seq_reps_n, seq_product_n; simpl.
  intro H0.
  destruct (nat_f n); clear n.
  revert H0.
  revert s x n1.
  induction n0; simpl; intros s x n1 H0.
  - destruct n1; inversion H0; subst; clear H0.
    exists []; split; auto; intros ? [].
  - unfold seq_product in H0.
    destruct (nat_f n1).
    destruct (Nat.iter n0
            (fun (f' : nat -> option (list A)) (n : nat) =>
             let (i, j) := nat_f n in option_mult MonoidList (f' i) (s j)) 
            (seq_one []) n) eqn:Hiter;
      destruct (s n2) eqn:Hn2; inversion H0; subst.
    apply IHn0 in Hiter.
    destruct Hiter as [l' [? Hiter]]; subst.
    exists (l' ++ [l0]); split.
    + rewrite concat_app; simpl; rewrite app_nil_r; reflexivity.
    + intros y Hin.
      apply in_app_or in Hin; destruct Hin as [Hin | Hin]; auto.
      destruct Hin as [? | []]; subst.
      exists n2; auto.
Qed.

Lemma nat_iter_product_concat {A : Type} (s : nat -> option (list A)) :
  forall n k x, Nat.iter n (fun f' : nat -> option (list A) => seq_product MonoidList f' s)
                    (seq_one (Monoid.monoid_unit MonoidList)) k = Some x ->
           exists ls, length ls = n /\ x = concat ls /\ forall l, In l ls -> exists j, s j = Some l.
Proof.
  intro n; revert s.
  induction n; simpl; intros s k x H.
  - destruct k; inversion H; subst; clear H.
    exists []; repeat split; auto; intros i [].
  - unfold seq_product in H.
    destruct (nat_f k) eqn:Hk.
    destruct (Nat.iter n
                       (fun (f' : nat -> option (list A)) (n : nat) =>
                          let (i, j) := nat_f n in option_mult MonoidList (f' i) (s j)) 
                       (seq_one []) n0) eqn:Hiter;
      destruct (s n1) eqn:Hn1; inversion H; subst.
    apply IHn in Hiter.
    destruct Hiter as [ls [? [Hlen Hiter]]]; subst.
    exists (ls ++ [l0]); repeat split.
    + rewrite app_length; apply Nat.add_1_r.
    + rewrite concat_app; simpl; rewrite app_nil_r; reflexivity.
    + intros l Hin.
      apply in_app_or in Hin; destruct Hin as [Hin | Hin].
      * apply Hiter; auto.
      * destruct Hin as [? | []]; subst.
        eexists; eauto.
Qed.

Lemma nat_iter_n_incomparable {A : Type} `{EqType A}
      (s1 s2 : nat -> option (list A)) (n i j : nat) (x y : list A) :
  i <> j ->
  seq_incomparable s1 ->
  seq_incomparable s2 ->
  Nat.iter n (fun f' : nat -> option (list A) => seq_product MonoidList f' s2) s1 i = Some x ->
  Nat.iter n (fun f' : nat -> option (list A) => seq_product MonoidList f' s2) s1 j = Some y ->
  incomparable x y.
Proof.
  revert s1 s2 i j x y.
  induction n; simpl; intros s1 s2 i j x y Hneq H0 H1 H2 H3.
  - eapply H0; eauto.
  - unfold seq_product in *.
    destruct (nat_f i) eqn:Hi, (nat_f j) eqn:Hj.
    destruct (Nat.iter n
            (fun (f' : nat -> option (list A)) (n : nat) =>
               let (i, j) := nat_f n in option_mult MonoidList (f' i) (s2 j)) s1 n0)
             eqn:Hiter0;
      destruct (Nat.iter n
            (fun (f' : nat -> option (list A)) (n : nat) =>
               let (i, j) := nat_f n in option_mult MonoidList (f' i) (s2 j)) s1 n2)
               eqn:Hiter1;
      destruct (s2 n1) eqn:Hn1, (s2 n3) eqn:Hn3;
      inversion H2; inversion H3; subst.
    destruct (Nat.eqb_spec n0 n2); subst.
    + rewrite Hiter0 in Hiter1; inversion Hiter1; subst.
      destruct (Nat.eqb_spec n1 n3); subst.
      * rewrite <- Hi in Hj; apply nat_f_inj in Hj; congruence.
      * apply incomparable_app_r; eapply H1; eauto.
    + eapply IHn in Hiter0; eauto.
      apply incomparable_app_l; symmetry; auto.
Qed.

Lemma incomparable_concat_prefix {A : Type} `{EqType A} (ls1 ls2 : list (list A)) :
  (forall x y, In x ls1 -> In y ls2 -> x <> y -> incomparable x y) ->
  incomparable (concat ls1) (concat ls2) \/ is_prefix ls1 ls2 \/ is_prefix ls2 ls1.
Proof.
  revert ls2; induction ls1; intros ls2 Hinc.
  - right; left; constructor.
  - simpl.
    destruct ls2; simpl.
    + right; right; constructor.
    + destruct (eqb_spec a l); subst.
      * destruct (IHls1 ls2) as [H0 | [H0 | H0]].
        -- intros x y Hx Hy Hneq; apply Hinc; auto; right; auto.
        -- left; apply incomparable_app_r; auto.
        -- right; left; constructor; auto.
        -- right; right; constructor; auto.
      * left; apply incomparable_app_l; apply Hinc; auto; left; auto.
Qed.

Lemma seq_incomparable_product_reps {A : Type} `{EqType A} (s1 s2 : nat -> option (list A)) :
  seq_incomparable s1 ->
  seq_incomparable s2 ->
  seqs_incomparable s1 s2 ->
  seq_incomparable (seq_product MonoidList (seq_reps MonoidList s1) s2).
Proof.
  intros Hs1 H0 H1 i j x y Hneq H2 H3.
  unfold seq_product in *.
  destruct (nat_f i) eqn:Hi.
  destruct (nat_f j) eqn:Hj.
  destruct (Nat.eqb_spec n n1); subst.
  - destruct (seq_reps MonoidList s1 n1) eqn:Hn;
      destruct (seq_reps MonoidList s1 n1) eqn:Hn1;
      destruct (s2 n0) eqn:Hn0, (s2 n2) eqn:Hn2;
      inversion H2; inversion H3; inversion Hn; subst.
    apply incomparable_app_r.
    destruct (Nat.eqb_spec n0 n2); subst.
    + rewrite <- Hi in Hj; apply nat_f_inj in Hj; congruence.
    + eapply H0; eauto.
  - clear H0. (* shouldn't need this here *)
    destruct (seq_reps MonoidList s1 n) eqn:Hn;
      destruct (seq_reps MonoidList s1 n1) eqn:Hn1;
      destruct (s2 n0) eqn:Hn0, (s2 n2) eqn:Hn2;
      inversion H2; inversion H3; subst.
    unfold seq_reps, seq_reps_n, seq_product_n, seq_flatten in *.
    destruct (nat_f n) eqn:Hn'.
    destruct (nat_f n1) eqn:Hn1'.
    destruct (Nat.eqb_spec n4 n6); subst.
    + destruct (Nat.eqb_spec n5 n7); subst.
      * rewrite <- Hn' in Hn1'; apply nat_f_inj in Hn1'; congruence.
      * (* lengths are the same but the element index is different, so
           l and l0 must be incomparable. *)    
        apply incomparable_app_l.
        eapply nat_iter_n_incomparable.
        4: eauto.
        eauto. apply seq_incomparable_seq_one. auto. auto.
    + (* lengths are different so either [concat ls1] and [concat ls2]
      are incomparable OR one of ls1 and ls2 is a proper prefix of the
      other and thus the next element of the other is incomparable
      with either l1 or l2.
      E.g., if ls1 is a proper prefix of ls2, then exists ls, ls1 ++
      ls = ls2 so the goal becomes:
      [incomparable (concat ls1 ++ l1) (concat ls1 ++ concat ls ++ l2)
      which follows from:
      [incomparable l1 (concat ls ++ l2)]
      which is true because l1 is incomparable with every element of ls. *)
      apply nat_iter_product_concat in Hn.
      apply nat_iter_product_concat in Hn1.
      destruct Hn as [ls1 [Hlen1 [? Hn]]]; subst.
      destruct Hn1 as [ls2 [Hlen2 [? Hn1]]]; subst.
      destruct (incomparable_concat_prefix ls1 ls2) as [Hls | [Hls | Hls]].
      * intros x y Hx Hy Hinc.
        apply Hn in Hx; apply Hn1 in Hy.
        destruct Hx, Hy.
        destruct (Nat.eqb_spec x0 x1); subst.
        -- rewrite H0 in H4; inversion H4; congruence.
        -- eapply Hs1; eauto.
      * apply incomparable_app_l; auto.
      * apply is_prefix_exists in Hls.
        destruct Hls as [ls ?]; subst.
        rewrite concat_app, <- app_assoc.
        apply incomparable_app_r.
        destruct ls.
        -- rewrite app_nil_r in n8; congruence.
        -- simpl; rewrite <- app_assoc.
           apply incomparable_app_l'.
           symmetry.
           assert (exists j', s1 j' = Some l).
           { apply Hn1; apply in_or_app; right; left; reflexivity. }
           destruct H0 as [j' ?].
           eapply H1; eauto.
      * symmetry.
        apply is_prefix_exists in Hls.
        destruct Hls as [ls ?]; subst.
        rewrite concat_app, <- app_assoc.
        apply incomparable_app_r.
        destruct ls.
        -- rewrite app_nil_r in n8; congruence.
        -- simpl; rewrite <- app_assoc.
           apply incomparable_app_l'.
           symmetry.
           assert (exists j', s1 j' = Some l).
           { apply Hn; apply in_or_app; right; left; reflexivity. }
           destruct H0 as [j' ?].
           eapply H1; eauto.
Qed.

Definition disjoint {A : Type} (f g : A -> bool) : Prop :=
  forall x, match (f x, g x) with
       | (true, true) => False
       | _ => True
       end.

Lemma leaf_reachable_not_nil {A : Type} (t : tree A) (n : nat) :
  leaf_reachable t ->
  forall i : nat,
    RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false))) i <> Some [].
Proof.
  revert n; induction t; simpl; intros m Hleaf i.
  - intro HC; inversion HC.
  - inversion Hleaf.
  - unfold compose, seq_union.
    destruct (i mod 2).
    + destruct (RE_sequence (RE_of_tree_mixed t1 (cotuple (Nat.eqb m) (const false))) (i / 2));
        intro HC; inversion HC.
    + destruct (RE_sequence (RE_of_tree_mixed t2 (cotuple (Nat.eqb m) (const false))) (i / 2));
        intro HC; inversion HC.
  - intro HC.
    unfold seq_product in HC.
    destruct (nat_f i).
    destruct (seq_reps
                MonoidList
                (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false)))) n0)
             eqn:Hn0;
      destruct (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb m) (const false))) n1)
               eqn:Hn1;
      inversion HC; subst; clear HC.
    apply app_nil_inv in H0; destruct H0; subst.
    inversion Hleaf; subst.
    eapply IHt; eauto.
Qed.

Lemma fail_reachable_not_nil {A : Type} (t : tree A) (n m : nat) :
  n <> m ->
  fail_reachable m t ->
  forall i : nat,
    RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false))) i <> Some [].
Proof.
  revert n; induction t; simpl; intros n' Hneq Hfail i.
  - intro HC; inversion HC.
  - inversion Hfail; subst.
    destruct (Nat.eqb_spec n' n); subst; try congruence.
    intro HC; inversion HC.
  - unfold compose, seq_union.
    destruct (i mod 2).
    + destruct (RE_sequence (RE_of_tree_mixed t1 (cotuple (Nat.eqb n') (const false))) (i / 2));
        intro HC; inversion HC.
    + destruct (RE_sequence (RE_of_tree_mixed t2 (cotuple (Nat.eqb n') (const false))) (i / 2));
        intro HC; inversion HC.
  - intro HC.
    unfold seq_product in HC.
    destruct (nat_f i).
    destruct (seq_reps
                MonoidList
                (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false)))) n0)
             eqn:Hn0;
      destruct (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n') (const false))) n1)
               eqn:Hn1;
      inversion HC; subst; clear HC.
    apply app_nil_inv in H0; destruct H0; subst.
    inversion Hfail; subst.
    eapply IHt; eauto.
Qed.

Lemma seqs_incomparable_product_reps {A : Type} `{EqType A}
      (s1 s2 s2' : nat -> option (list A)) :
  seq_incomparable s1 ->
  seqs_incomparable s1 s2 ->
  seqs_incomparable s1 s2' ->
  seqs_incomparable s2 s2' ->
  seqs_incomparable (seq_product MonoidList (seq_reps MonoidList s1) s2)
                    (seq_product MonoidList (seq_reps MonoidList s1) s2').
Proof.
  intros Hs1 Hs1' Hs2' Hs2 i j x y H0 H1.
  unfold seq_product in *.
  destruct (nat_f i) eqn:Hi.
  destruct (nat_f j) eqn:Hj.
  destruct (seq_reps MonoidList s1 n) eqn:Hn;
    destruct (seq_reps MonoidList s1 n1) eqn:Hn1;
    destruct (s2 n0) eqn:Hn0, (s2' n2) eqn:Hn2;
    inversion H0; inversion H1; subst.
  unfold seq_reps, seq_flatten, seq_reps_n, seq_product_n in *.
  destruct (nat_f n) eqn:Hn'.
  destruct (nat_f n1) eqn:Hn1'.
  apply nat_iter_product_concat in Hn.
  apply nat_iter_product_concat in Hn1.
  destruct Hn as [ls1 [? [? Hn]]]; subst.
  destruct Hn1 as [ls2 [? [? Hn1]]]; subst.
  destruct (incomparable_concat_prefix ls1 ls2) as [Hls | [Hls | Hls]].
  - intros x y Hx Hy Hneq.
    apply Hn in Hx.
    apply Hn1 in Hy.
    destruct Hx, Hy.
    destruct (Nat.eqb_spec x0 x1); subst.
    + rewrite H2 in H3; inversion H3; congruence.
    + eapply Hs1; eauto.
  - apply incomparable_app_l; auto.
  - apply is_prefix_exists in Hls.
    destruct Hls as [l ?]; subst.
    rewrite concat_app, <- app_assoc.
    apply incomparable_app_r.
    destruct l; simpl.
    + eapply Hs2; eauto.
    + rewrite <- app_assoc.
      apply incomparable_app_l'.
      symmetry.
      assert (exists j, s1 j = Some l).
      { apply Hn1; apply in_or_app; right; left; auto. }
      destruct H2; eapply Hs1'; eauto.
  - apply is_prefix_exists in Hls.
    destruct Hls as [l ?]; subst.
    rewrite concat_app, <- app_assoc.
    apply incomparable_app_r.
    destruct l; simpl.
    + eapply Hs2; eauto.
    + rewrite <- app_assoc.
      symmetry; apply incomparable_app_l'; symmetry.
      assert (exists j, s1 j = Some l).
      { apply Hn; apply in_or_app; right; left; auto. }
      destruct H2; eapply Hs2'; eauto.
Qed.

Lemma seqs_incomparable_tree_sequence_mixed {A : Type}
      (t : tree A) (lbls : list nat) (f g : nat + A -> bool) :
  wf_tree t ->
  disjoint f g ->
  (forall lbl, bound_in lbl t -> f (inl lbl) = false /\ g (inl lbl) = false) ->
  nondivergent' lbls t ->
  (forall m, bound_in m t -> ~ In m lbls) ->
  seq_incomparable (tree_sequence_mixed t f) /\
  seq_incomparable (tree_sequence_mixed t g) /\
  seqs_incomparable (tree_sequence_mixed t f) (tree_sequence_mixed t g).
Proof.
  revert f g lbls; unfold tree_sequence_mixed, disjoint.
  induction t; simpl; intros f g lbls Hwf Hdisj Hbound Hnd Hnotin.
  - repeat split.
    + destruct (f (inr a)); simpl.
      * apply seq_incomparable_seq_one.
      * apply seq_incomparable_seq_zero.
    + destruct (g (inr a)); simpl.
      * apply seq_incomparable_seq_one.
      * apply seq_incomparable_seq_zero.
    + intros i j x y H0 H1; specialize (Hdisj (inr a)).
      destruct (f (inr a)), (g (inr a));
        try contradiction; inversion H0; inversion H1.
  - repeat split.
    + destruct (f (inl n)); simpl.
      * apply seq_incomparable_seq_one.
      * apply seq_incomparable_seq_zero.
    + destruct (g (inl n)); simpl.
      * apply seq_incomparable_seq_one.
      * apply seq_incomparable_seq_zero.
    + intros i j x y H0 H1; specialize (Hdisj (inl n)).
      destruct (f (inl n)), (g (inl n));
        try contradiction; inversion H0; inversion H1.
  - inversion Hwf; subst.
    inversion Hnd; subst.
    repeat split.
    + unfold seq_union, compose; intros i j x y Hneq H0 H1.
      set (i' := (i / 2)%nat).
      set (j' := (j / 2)%nat).
      fold i' in H0; fold j' in H1.
      destruct (i mod 2) eqn:Hi, (j mod 2) eqn:Hj.
      * destruct (RE_sequence (RE_of_tree_mixed t1 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t1 f) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        assert (H: seq_incomparable (RE_sequence (RE_of_tree_mixed t1 f))).
        { eapply (IHt1 f g); eauto.
          intros lbl Hbound'; apply Hbound; constructor; eauto.
          intros m Hbound'; apply Hnotin; constructor; auto. }
        right; eapply H with (i:=i') (j:=j'); eauto.
        unfold i', j'; intro HC; apply Hneq.
        rewrite <- mod_n_div, <- (mod_n_div i); auto.
      * destruct (RE_sequence (RE_of_tree_mixed t1 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t2 f) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        constructor; congruence.
      * destruct (RE_sequence (RE_of_tree_mixed t2 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t1 f) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        constructor; congruence.
      * destruct (RE_sequence (RE_of_tree_mixed t2 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t2 f) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        assert (H: seq_incomparable (RE_sequence (RE_of_tree_mixed t2 f))).
        { eapply (IHt2 f g); eauto.
          intros lbl Hbound'; apply Hbound; solve[constructor; eauto].
          intros m Hbound'; apply Hnotin; solve[constructor; auto]. }
        right; eapply H with (i:=i') (j:=j'); eauto.
        unfold i', j'; intro HC; apply Hneq.
        destruct (mod_2_dec i); try congruence.
        destruct (mod_2_dec j); try congruence.
        rewrite <- mod_n_div_plus_1, <- (mod_n_div_plus_1 i); auto.
    + unfold seq_union, compose; intros i j x y Hneq H0 H1.
      set (i' := (i / 2)%nat).
      set (j' := (j / 2)%nat).
      fold i' in H0; fold j' in H1.
      destruct (i mod 2) eqn:Hi, (j mod 2) eqn:Hj.
      * destruct (RE_sequence (RE_of_tree_mixed t1 g) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t1 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        assert (H: seq_incomparable (RE_sequence (RE_of_tree_mixed t1 g))).
        { eapply (IHt1 f g); eauto.
          intros lbl Hbound'; apply Hbound; constructor; eauto.
          intros m Hbound'; apply Hnotin; solve[constructor; auto]. }
        right; eapply H with (i:=i') (j:=j'); eauto.
        unfold i', j'; intro HC; apply Hneq.
        rewrite <- mod_n_div, <- (mod_n_div i); auto.
      * destruct (RE_sequence (RE_of_tree_mixed t1 g) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t2 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        constructor; congruence.
      * destruct (RE_sequence (RE_of_tree_mixed t2 g) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t1 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        constructor; congruence.
      * destruct (RE_sequence (RE_of_tree_mixed t2 g) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t2 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        assert (H: seq_incomparable (RE_sequence (RE_of_tree_mixed t2 g))).
        { eapply (IHt2 f g); eauto.
          intros lbl Hbound'; apply Hbound; solve[constructor; eauto].
          intros m Hbound'; apply Hnotin; solve[constructor; auto]. }
        right; eapply H with (i:=i') (j:=j'); eauto.
        unfold i', j'; intro HC; apply Hneq.
        destruct (mod_2_dec i); try congruence.
        destruct (mod_2_dec j); try congruence.
        rewrite <- mod_n_div_plus_1, <- (mod_n_div_plus_1 i); auto.
    + unfold seq_union, compose; intros i j x y H0 H1.
      inversion Hwf; subst.
      unfold seq_union, compose in *.
      set (i' := (i / 2)%nat).
      set (j' := (j / 2)%nat).
      fold i' in H0; fold j' in H1.
      destruct (i mod 2) eqn:Hi, (j mod 2) eqn:Hj.
      * destruct (RE_sequence (RE_of_tree_mixed t1 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t1 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        right; eapply IHt1; eauto.
        intros lbl Hbound'; apply Hbound; constructor; auto.
        intros m Hbound'; apply Hnotin; solve[constructor; auto].
      * destruct (RE_sequence (RE_of_tree_mixed t1 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t2 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        constructor; congruence.
      * destruct (RE_sequence (RE_of_tree_mixed t2 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t1 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        constructor; congruence.
      * destruct (RE_sequence (RE_of_tree_mixed t2 f) i') eqn:Hi';
          destruct (RE_sequence (RE_of_tree_mixed t2 g) j') eqn:Hj';
          inversion H0; inversion H1; subst.
        right; eapply IHt2; eauto.
        intros lbl Hbound'; apply Hbound; solve[constructor; auto].
        intros m Hbound'; apply Hnotin; solve[constructor; auto].
  - inversion Hwf; subst.
    inversion Hnd; subst.
    assert (Hincn: seq_incomparable
                     (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false))))).
    { eapply IHt with (f:=const false); eauto.
      - intros ?; simpl; auto.
      - intros lbl Hbound'; unfold const; simpl; split; auto.
        destruct (Nat.eqb_spec n lbl); subst; auto.
        apply bound_in_not_bound_in in H2; congruence.
      - intros m Hbound' HC.
        destruct (Nat.eqb_spec m n); subst.
        + apply bound_in_not_bound_in in H2; congruence.
        + destruct HC; subst; try congruence.
          eapply Hnotin; eauto; constructor; auto. }
    assert (Hincf: seqs_incomparable
                     (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false))))
                     (RE_sequence (RE_of_tree_mixed t f))).
    { eapply IHt; eauto.
      - intros []; simpl; auto.
        destruct (Nat.eqb_spec n n0); subst; auto.
        destruct (Hbound n0 (bound_in_fix1 _ _)) as [H _]; rewrite H; auto.
      - intros lbl Hbound'; simpl.
        destruct (Nat.eqb_spec n lbl); subst; split; auto.
        + apply bound_in_not_bound_in in H2; congruence.
        + apply bound_in_not_bound_in in H2; congruence.
        + apply Hbound; constructor; auto.
      - intros m Hbound' HC.
        destruct (Nat.eqb_spec m n); subst.
        + apply bound_in_not_bound_in in H2; congruence.
        + destruct HC; subst; try congruence.
          eapply Hnotin; eauto; constructor; auto. }
    assert (Hincg: seqs_incomparable
                     (RE_sequence (RE_of_tree_mixed t (cotuple (Nat.eqb n) (const false))))
                     (RE_sequence (RE_of_tree_mixed t g))).
    { eapply IHt; eauto.
      - intros []; simpl; auto.
        destruct (Nat.eqb_spec n n0); subst; auto.
        destruct (Hbound n0 (bound_in_fix1 _ _)) as [_ H]; rewrite H; auto.
      - intros lbl Hbound'; simpl.
        destruct (Nat.eqb_spec n lbl); subst; split; auto.
        + apply bound_in_not_bound_in in H2; congruence.
        + apply bound_in_not_bound_in in H2; congruence.
        + apply Hbound; constructor; auto.
      - intros m Hbound' HC.
        destruct (Nat.eqb_spec m n); subst.
        + apply bound_in_not_bound_in in H2; congruence.
        + destruct HC; subst; try congruence.
          eapply Hnotin; eauto; constructor; auto. }
    repeat split; intros i j x y.
    + intros Hneq H3 H4'.
      eapply seq_incomparable_product_reps in H3; eauto.
      eapply IHt with (f:=const false); eauto.
      * intros ?; simpl; auto.
      * intros lbl Hbound'; unfold const; simpl; split; auto.
        apply Hbound; destruct (Nat.eqb_spec lbl n); subst; constructor; auto.
      * intros m Hbound' HC.
        destruct (Nat.eqb_spec m n); subst.
        -- apply bound_in_not_bound_in in H2; congruence.
        -- destruct HC; subst; try congruence.
           eapply Hnotin; eauto; constructor; auto.
    + intros Hneq H3 H4'.
      eapply seq_incomparable_product_reps in H3; eauto.
      eapply IHt with (g:=const false); eauto.
      * intros ?; simpl; destruct (g x0); auto.
      * intros lbl Hbound'; unfold const; simpl; split; auto.
        apply Hbound; destruct (Nat.eqb_spec lbl n); subst; constructor; auto.
      * intros m Hbound' HC.
        destruct (Nat.eqb_spec m n); subst.
        -- apply bound_in_not_bound_in in H2; congruence.
        -- destruct HC; subst; try congruence.
           eapply Hnotin; eauto; constructor; auto.
    + intros H3 H4'.
      eapply seqs_incomparable_product_reps in H3; eauto.
      eapply IHt; eauto.
      * intros lbl Hbound'; apply Hbound.
        destruct (Nat.eqb_spec lbl n); subst; constructor; auto.
      * intros m Hbound' [? | Hin]; subst.
        -- apply bound_in_not_bound_in in H2; congruence.
        -- eapply Hnotin; eauto.
           destruct (Nat.eqb_spec m n); subst; constructor; auto.
Qed.

Lemma seq_incomparable_tree_sequence_fail {A : Type}
      (t : tree A) (lbls : list nat) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  nondivergent' lbls t ->
  (forall m, bound_in m t -> ~ In m lbls) ->
  seq_incomparable (tree_sequence_fail t n).
Proof.
  intros Hwf Hnotbound Hnd Hnotin.
  rewrite tree_sequence_mixed_fail.
  eapply seqs_incomparable_tree_sequence_mixed with (g := const false); eauto.
  - intros []; simpl; auto; destruct (n =? n0); auto.
  - unfold const; intros lbl Hbound; split; simpl; auto.
    destruct (Nat.eqb_spec n lbl); subst; auto.
    apply bound_in_not_bound_in in Hnotbound; congruence.
Qed.

Lemma seq_incomparable_tree_sequence_f {A : Type}
      (t : tree A) (lbls : list nat) (f : A -> bool) :
  wf_tree t ->
  nondivergent' lbls t ->
  (forall m, bound_in m t -> ~ In m lbls) ->
  seq_incomparable (tree_sequence_f t f).
Proof.
  intros Hwf Hnd Hnotin.
  rewrite tree_sequence_mixed_f.
  eapply seqs_incomparable_tree_sequence_mixed with (g := const false); eauto.
  intros []; simpl; auto; destruct (f a); auto.
Qed.

Lemma seqs_incomparable_tree_sequence_fail_f {A : Type}
      (t : tree A) (lbls : list nat) (f : A -> bool) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  nondivergent' lbls t ->
  (forall m, bound_in m t -> ~ In m lbls) ->
  seqs_incomparable (tree_sequence_fail t n) (tree_sequence_f t f).
Proof.
  intros Hwf Hnotbound Hnd Hnotin.
  rewrite tree_sequence_mixed_fail, tree_sequence_mixed_f.
  eapply seqs_incomparable_tree_sequence_mixed; eauto.
  - intros []; simpl; auto; destruct (n =? n0); auto.
  - unfold const; intros lbl Hbound; split; auto; simpl.
    destruct (Nat.eqb_spec n lbl); subst; auto.
    apply bound_in_not_bound_in in Hnotbound; congruence.
Qed.

Lemma seq_incomparable_tree_sequence {A : Type}
      (t : tree A) (lbls : list nat) (f : A -> bool) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  nondivergent' lbls t ->
  (forall m, bound_in m t -> ~ In m lbls) ->
  seq_incomparable (tree_sequence t f n).
Proof.
  intros Hwf Hnotbound Hnd Hnotin.
  unfold tree_sequence, RE_of_tree; simpl.
  apply seq_incomparable_product_reps.
  - eapply seq_incomparable_tree_sequence_fail; eauto.
  - eapply seq_incomparable_tree_sequence_f; eauto.
  - eapply seqs_incomparable_tree_sequence_fail_f; eauto.
Qed.

Theorem seq_nodup_tree_sequence {A : Type}
      (t : tree A) (lbls : list nat) (f : A -> bool) (n : nat) :
  wf_tree t ->
  not_bound_in n t ->
  nondivergent' lbls t ->
  (forall m, bound_in m t -> ~ In m lbls) ->
  seq_nodup (tree_sequence t f n).
Proof.
  intros Hwf Hnotbound Hnd Hnotin.
  apply seq_incomparable_nodup.
  eapply seq_incomparable_tree_sequence; eauto.
Qed.
