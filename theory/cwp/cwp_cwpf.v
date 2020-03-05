(** The relational and functional specifications of CWP coincide when
    all loops are iid. *)

Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Local Open Scope program_scope.
Import ListNotations.

Require Import cpGCL.
Require Import cwp.
Require Import cwpf_infer.
Require Import geometric.
Require Import order.
Require Import Q.

Open Scope cpGCL_scope.
Open Scope Q_scope.

Lemma wpf_linear c f g st :
  wpf c (fun st => f st + g st) st == wpf c f st + wpf c g st.
Proof.
  revert f g st.
  induction c; intros f g st; simpl.
  - reflexivity.
  - unfold const; lra.
  - reflexivity.
  - unfold compose. rewrite <- IHc1.
    apply Proper_wpf; auto.
    intros ?; apply IHc2.
  - destruct (e st); auto.
  - rewrite IHc1, IHc2. lra.
  - destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) st) 1).
    + rewrite q, Qminus_cancel, 3!Qdiv_0_den; lra.
    + assert (H0: forall a b c, ~ c == 0 -> a / c + b / c == (a + b) / c).
      { intros. field; auto. }
      rewrite H0.
      * rewrite <- IHc. apply Qeq_Qdiv.
        ++ apply Proper_wpf; auto.
           intro x; destruct (e x); lra.
        ++ reflexivity.
      * lra.
  - destruct (e st); lra.
Qed.

Lemma wpf_linear' c (e : exp) f g st :
  wpf c (fun x => if e x then f x else g x) st ==
  wpf c (fun x => if e x then f x else 0) st +
  wpf c (fun x => if e x then 0 else g x) st.
Proof.
  rewrite <- wpf_linear; apply Proper_wpf; auto.
  intro x; destruct (e x); lra.
Qed.

Lemma wpf_strict c f x :
  f ==f const 0 ->
  wpf c f x == 0.
Proof.
  revert f x.
  induction c; simpl; unfold const in *; intros f x Heq; auto; try reflexivity.
  - unfold compose; auto.
  - destruct (e x); auto.
  - rewrite IHc1, IHc2; auto; lra.
  - rewrite IHc.
    + apply Qdiv_0_num.
    + intro y; destruct (e y); auto; reflexivity.
  - destruct (e x); auto; reflexivity.
Qed.

Lemma wpf_bounded c f :
  wf_cpGCL c ->
  (forall x, f x <= 1) ->
  forall x, wpf c f x <= 1.
Proof.
  revert f.
  induction c; intros f Hwf Hle x; simpl; inversion Hwf; subst; auto.
  - unfold const; lra.
  - apply IHc1; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 f H3 Hle x); specialize (IHc2 f H4 Hle x); nra.
  - set (ea := wpf c (fun st => if e st then 0 else f st) x).
    set (eb := wpf c (fun st => if e st then 1 else 0) x).
    assert (eb <= 1).
    { apply IHc; auto.
      intro y; destruct (e y); lra. }
    destruct (Qeq_dec eb 1).
    { rewrite q, Qminus_cancel, Qdiv_0_den; lra. }
    apply ratio_Qle_sum. lra.
    rewrite Qmult_1_r.
    assert (ea <= 1).
    { apply IHc; auto.
      intro y; destruct (e y); auto; lra. }
    assert (H': eb == wpf c (fun x => if e x then const 1 x else 0) x).
    { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
    rewrite H'; clear H'.
    unfold ea.
    rewrite Qplus_comm.
    rewrite <- wpf_linear'.
    apply IHc; auto.
    intro y; destruct (e y); auto.
    unfold const; lra.
  - destruct (e x); auto; lra.
Qed.

Lemma wlpf_linear c f g st :
  wlpf c (fun st => f st + g st) st == wpf c f st + wlpf c g st.
Proof.
  revert f g st.
  induction c; intros f g st; simpl.
  - reflexivity.
  - unfold const; lra.
  - reflexivity.
  - unfold compose. rewrite <- IHc1.
    apply Proper_wlpf; auto.
    intros ?; apply IHc2.
  - destruct (e st); auto.
  - rewrite IHc1, IHc2. lra.
  - destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) st) 1).
    + rewrite Qeq_eq_bool; auto.
      rewrite q, Qminus_cancel, Qdiv_0_den; lra.
    + rewrite Qeq_bool_false; auto.
      assert (H0: forall a b c, ~ c == 0 -> a / c + b / c == (a + b) / c).
      { intros. field; auto. }
      rewrite H0.
      * rewrite <- IHc. apply Qeq_Qdiv.
        ++ apply Proper_wlpf; auto.
           intro x; destruct (e x); lra.
        ++ reflexivity.
      * lra.
  - destruct (e st); lra.
Qed.

Lemma wlpf_linear' c (e : exp) f g st :
  wlpf c (fun st' => if e st' then f st' else g st') st ==
  wpf c (fun st' => if e st' then f st' else 0) st +
  wlpf c (fun st' => if e st' then 0 else g st') st.
Proof.
  rewrite <- wlpf_linear; apply Proper_wlpf; auto.
  intro x; destruct (e x); lra.
Qed.

Lemma wlpf_bounded c f :
  wf_cpGCL c ->
  (forall x, f x <= 1) ->
  forall x, wlpf c f x <= 1.
Proof.
  revert f.
  induction c; intros f Hwf Hle x; simpl; inversion Hwf; subst; auto.
  - unfold const; lra.
  - apply IHc1; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 f H3 Hle x); specialize (IHc2 f H4 Hle x); nra.
  - set (ea := wlpf c (fun st => if e st then 0 else f st) x).
    set (eb := wpf c (fun st => if e st then 1 else 0) x).
    assert (eb <= 1).
    { apply wpf_bounded; auto.
      intro y; destruct (e y); lra. }
    destruct (Qeq_dec eb 1).
    { rewrite q. simpl. lra. }
    rewrite Qeq_bool_false; auto.
    apply ratio_Qle_sum. lra.
    rewrite Qmult_1_r.
    assert (ea <= 1).
    { apply IHc; auto.
      intro y; destruct (e y); auto; lra. }
    assert (H': eb == wpf c (fun x => if e x then const 1 x else 0) x).
    { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
    rewrite H'; clear H'.
    unfold ea.
    rewrite Qplus_comm.
    rewrite <- wlpf_linear'.
    apply IHc; auto.
    intro y; destruct (e y); auto.
    unfold const; lra.
  - destruct (e x); auto; lra.
Qed.

Lemma wpf_expectation c f :
  wf_cpGCL c ->
  expectation f ->
  expectation (wpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hexp; simpl; inversion Hwf; subst; auto.
  - unfold const; intros ?; lra.
  - intros ?; apply Hexp.
  - apply IHc1; auto.
  - intro x; destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - intro x.
    specialize (IHc1 f H3 Hexp x); specialize (IHc2 f H4 Hexp x).
    nra.
  - intro x. simpl.
    assert (wpf c (fun st => if e st then 1 else 0) x <= 1).
    { apply wpf_bounded; auto.
      intro st; destruct (e st); auto; lra. }
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) x) 1).
    + rewrite q, Qminus_cancel, Qdiv_0_den; lra.
    + apply Qle_shift_div_l. lra. rewrite Qmult_0_l. apply IHc; auto.
      intro st; destruct (e st); auto; lra.
  - intro x; destruct (e x); auto; lra.
Qed.

Lemma wlpf_expectation c f :
  wf_cpGCL c ->
  expectation f ->
  expectation (wlpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hexp; simpl; inversion Hwf; subst; auto.
  - unfold const; intros ?; lra.
  - intros ?; apply Hexp.
  - apply IHc1; auto.
  - intro x; destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - intro x.
    specialize (IHc1 f H3 Hexp x); specialize (IHc2 f H4 Hexp x).
    nra.
  - intro x. simpl.
    assert (wpf c (fun st => if e st then 1 else 0) x <= 1).
    { apply wpf_bounded; auto.
      intro st; destruct (e st); auto; lra. }
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) x) 1).
    + apply Qeq_bool_iff in q. rewrite q; lra.
    + rewrite Qeq_bool_false; auto; apply Qle_shift_div_l.
      lra. rewrite Qmult_0_l. apply IHc; auto.
      intro st; destruct (e st); auto; lra.
  - intro x; destruct (e x); auto; lra.
Qed.

Lemma wlpf_bounded_expectation c f :
  wf_cpGCL c ->
  bounded_expectation f ->
  bounded_expectation (wlpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hexp; simpl; inversion Hwf; subst; auto.
  - unfold const; intros ?; lra.
  - intros ?; apply Hexp.
  - apply IHc1; auto.
  - intro x; destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - intro x.
    specialize (IHc1 f H3 Hexp x); specialize (IHc2 f H4 Hexp x).
    nra.
  - intro x. simpl.
    assert (wpf c (fun st => if e st then 1 else 0) x <= 1).
    { apply wpf_bounded; auto.
      intro st; destruct (e st); auto; lra. }
    destruct (Qeq_dec (wpf c (fun st => if e st then 1 else 0) x) 1).
    + apply Qeq_bool_iff in q. rewrite q; lra.
    + rewrite Qeq_bool_false; auto; split.
      * apply Qle_shift_div_l. lra.
        rewrite Qmult_0_l; apply IHc; auto.
        intro st; destruct (e st); auto; lra.
      * admit.
  - intro x; destruct (e x); auto; lra.
Admitted.

Lemma wpf_chain_geometric_series f e c st i :
  iid_wpf e c ->
  wpf (unroll e c i) f st ==
  geometric_series'' (wpf c (fun x => if e x then 0 else f x) st)
                     (wpf c (indicator e) st) i.
Proof.
  intro Hiid; induction i.
  - reflexivity.
  - rewrite Hiid.
    rewrite IHi.
    rewrite Qplus_comm.
    apply geometric_series''_succ.
Qed.

Lemma wlpf_chain_series f e c st i :
  iid_wlpf e c ->
  wlpf (unroll e c i) f st ==
  wlpf_series (wlpf c (fun x => if e x then 0 else f x) st)
              (wpf c (indicator e) st) i.
  (* geometric_series'' (wlpf c (fun x => if e x then 0 else f x) st) *)
  (*                    (wpf c (indicator e) st) i + *)
  (* Qpow (wpf c (indicator e) st) i. *)
Proof.
  unfold wlpf_series; intro Hiid; induction i.
  - reflexivity.
  - rewrite Hiid, IHi, Qplus_comm.
    simpl.
    (* set (a := wlpf c (fun x : St => if e x then 0 else f x) st). *)
    (* set (r := wpf c (indicator e) st). *)
    rewrite Qmult_plus_distr_r, Qplus_assoc, geometric_series''_succ.
    reflexivity.
Qed.

Lemma wf_unroll c e i :
  wf_cpGCL c ->
  wf_cpGCL (unroll e c i).
Proof. induction i; repeat constructor; auto. Qed.

(* Lemma kdfgfsdf c e st : *)
(*   wf_cpGCL c -> *)
(*   wpf c (indicator e) st + wpf c (neg_indicator e) st == 1. *)
(* Admitted. *)

Lemma wpf_monotone c :
  wf_cpGCL c ->
  monotone (wpf c).
Proof.
  induction c; unfold monotone, leq; simpl;
    intros Hwf f g Hleq x; auto; inversion Hwf; subst.
  - lra.
  - apply IHc1; auto; apply IHc2; auto.
  - destruct (e x).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - specialize (IHc1 H3 f g Hleq x).
    specialize (IHc2 H4 f g Hleq x).
    unfold leq in *; simpl in *; nra.
  - specialize (IHc H0).
    cut (wpf c (fun st' : St => if e st' then 0 else f st') x <=
         wpf c (fun st' : St => if e st' then 0 else g st') x).
    { intros.
      destruct (Qeq_dec (wpf c (fun x => if e x then 1 else 0) x) 1).
      { rewrite q, Qminus_cancel, 2!Qdiv_0_den; lra. }
      assert (wpf c (fun x => if e x then 1 else 0) x <= 1).
      { apply wpf_bounded; auto.
        intro y; destruct (e y); lra. }
      apply Qle_Qdiv; auto.
      lra. }
    apply IHc; simpl.
    intro y; destruct (e y); auto; lra.
  - destruct (e x); auto; lra.
Qed.

(* Lemma wpf_decreasing c f x : *)
(*   wpf c f x <= f x. *)
(* Proof. *)
(*   (* revert f x. *) *)
(*   (* induction c; intros f x Hexp; simpl. *) *)
(*   (* - lra. *) *)
(*   (* - apply Hexp. *) *)
(*   (* -  *) *)
(* Admitted. *)

(* Lemma kdfgf c e st : *)
(*   wf_cpGCL c -> *)
(*   (forall f, f ==f indicator e -> wpf c f st == 1) -> *)
(*   (* forall g, g ==f neg_indicator e -> wpf c g st == 0. *) *)
(*   forall f g, expectation g -> (forall x, g x <= if e x then 0 else f x) -> *)
(*          wpf c g st == 0. *)
(* Proof. *)
(*   revert e st. *)
(*   induction c; intros G st Hwf Heq f g Hexp Hle. *)
(*   - simpl in *. *)
(*     specialize (Heq (indicator G) (f_Qeq_refl _)). *)
(*     unfold indicator in *. *)
(*     (* rewrite Heq'. *) *)
(*     specialize (Hle st). *)
(*     destruct (G st). *)
(*     + specialize (Hexp st); lra. *)
(*     + lra. *)
(*   - reflexivity. *)
(*   - simpl in *. admit. *)
(*   - simpl in *. *)
(*     unfold compose in *. *)
(*     inversion Hwf; subst. *)
(*     apply IHc1 with (e:=G) (f:=f); auto. *)
(*     + intros h Hh. *)
(*       specialize (Heq h Hh). *)
(*       assert (Hle': 1 <= wpf c1 h st). *)
(*       { apply Qle_trans with (wpf c1 (wpf c2 h) st). *)
(*         - lra. *)
(*         - apply wpf_monotone; auto. *)
(*           intro s; simpl. *)
(*           apply wpf_decreasing. } *)
(*       assert (wpf c1 h st <= 1). *)
(*       { apply wpf_bounded; auto. *)
(*         intro y. rewrite Hh. unfold indicator. destruct (G y); lra. } *)
(*       lra. *)
(*     + apply wpf_expectation; auto. *)
(*     + intro x; specialize (Hle x). *)
(*       apply Qle_trans with (g x); auto. *)
(*       apply wpf_decreasing. *)
(*   - admit. (* TODO *) *)
(*   - admit. *)
(*   - admit. *)
(*   - simpl in *. *)
(*     specialize (Heq (indicator G) (f_Qeq_refl _)). *)
(*     unfold indicator in Heq. *)
(*     destruct (e st); try lra. *)
(*     specialize (Hle st). destruct (G st). *)
(*     + specialize (Hexp st); lra. *)
(*     + lra. *)
(* Admitted. *)

Lemma asdkdf c (e : exp) st :
  wf_cpGCL c ->
  wpf c (fun x => if e x then 1 else 0) st == 1 ->
  wpf c (fun x => if e x then 0 else 1) st == 0.
Proof.
  unfold indicator.
  set (a := wpf c (fun st : St => if e st then 1 else 0) st).
  set (b := wpf c (fun st : St => if e st then 0 else 1) st).
  intros Hwf Heq.
  cut (a + b <= 1).
  { intros.
    assert (0 <= a).
    { apply wpf_expectation; auto.
      intro y; destruct (e y); lra. }
    assert (0 <= b).
    { apply wpf_expectation; auto.
      intro y; destruct (e y); auto; lra. }
    lra. }
  assert (a == wpf c (fun x => if e x then const 1 x else 0) st).
  { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
  rewrite H. unfold b.
  rewrite <- wpf_linear'.
  apply wpf_bounded; auto.
  intro y; destruct (e y); auto; unfold const; lra.
Qed.

(* Lemma sdfasdfsdkdf c (e : exp) f st : *)
(*   wpf c (fun x => if e x then 1 else 0) st == 0 -> *)
(*   wpf c (fun x => if e x then f x else 0) st == 0. *)
(* Proof. *)


(* Lemma djkifg c f g st : *)
(*   wpf c f st == 0 -> *)
(*   wpf c (fun x => f st * g st) st == 0. *)
(* Proof. *)
(*   revert f g st. *)
(*   induction c; simpl; intros f g st Heq; auto. *)
(*   - rewrite Heq; lra. *)
(*   -  *)


(* Lemma djkifg c (e : exp) f st : *)
(*   wpf c (fun x => if e x then 0 else f x) st == *)
(*   wpf c (fun x => if e x then 0 else 1) st * wpf c f st. *)
(* Proof. *)
  

Lemma sdfasdkdf c (e : exp) f st :
  wpf c (fun x => if e x then 0 else 1) st == 0 ->
  wpf c (fun x => if e x then 0 else f x) st == 0.
Proof.
Admitted.

(* Lemma asdkdfgf c e st f : *)
(*   wf_cpGCL c -> *)
(*   expectation f -> *)
(*   wpf c (indicator e) st == 1 -> *)
(*   wpf c (fun x => if e x then 0 else f x) st == 0. *)
(* Proof. *)
(*   unfold indicator. *)
(*   set (a := wpf c (fun st : St => if e st then 1 else 0) st). *)
(*   set (b := wpf c (fun st : St => if e st then 0 else f st) st). *)
(*   intros Hwf Hexp Heq. *)
(*   cut (a + b <= 1). *)
(*   { intros. *)
(*     assert (0 <= a). *)
(*     { apply wpf_expectation; auto. *)
(*       intro y; destruct (e y); lra. } *)
(*     assert (0 <= b). *)
(*     { apply wpf_expectation; auto. *)
(*       intro y; destruct (e y); auto; lra. } *)
(*     lra. } *)
(*   (* wpf_linear' *) *)
(*   assert (a == wpf c (fun x => if e x then const 1 x else 0) st). *)
(*   { apply Proper_wpf; auto. intro y; destruct (e y); reflexivity. } *)
(*   rewrite H. unfold b. *)
(*   rewrite <- wpf_linear'. *)
(*   apply wpf_bounded; auto. *)
(*   intro y; destruct (e y); auto. *)
  
(*   revert e st f. *)
(*   induction c; simpl; unfold indicator; *)
(*     intros G st f Hwf Heq; inversion Hwf; subst. *)
(*   - intro H; destruct (G st); lra. *)
(*   - intro H; inversion H. *)
(*   - intro H; destruct (G (upd n (e st) st)); lra. *)
(*   - unfold compose. intro H. *)

(*   (* revert e st f. *) *)
(*   (* induction c; simpl; unfold indicator; intros G st f Hwf Heq. *) *)
(*   (* assert (H0: forall x, indicator G x == (if G x then 1 else 0)). *) *)
(*   (* { intros; reflexivity. } *) *)
(*   (* - (* specialize (Heq (indicator G) H0). *) *) *)
(*   (*   (* unfold indicator in Heq. *) *) *)
(*   (*   destruct (G st); lra. *) *)
(*   (* - reflexivity. *) *)
(*   (* - destruct (G (upd n (e st) st)); lra. *) *)
(*   (* - unfold compose in *. *) *)
(*   (*   inversion Hwf; subst. *) *)
(*   (*   apply kdfgf with (e:=G); auto. *) *)
(*   (*   intros. *) *)
(*   (*   rewrite <- Heq. *) *)
(*   (*   apply Proper_wpf; auto. *) *)
(*   (*   intro. rewrite H. unfold indicator. *) *)
(*   (*   apply Heq. *) *)
(*   intros Hwf Hexp Heq. *)
(*   apply kdfgf with (e:=e) (f:=f); auto. *)
(*   - intros g Heq'. *)
(*     rewrite <- Heq. *)
(*     eapply Proper_wpf; auto. *)
(*   - intro x.  *)
(*     destruct (e x); auto; lra. *)
(*   - intro; lra. *)
(* Qed. *)

Lemma asdkdfgf' c e st f :
  wf_cpGCL c ->
  (wpf c (indicator e) st == 1) ->
  wlpf c (fun x => if e x then 0 else f x) st == 0.
Proof.
Admitted.

Lemma wpf_unroll_const_0 c e x i f :
  wf_cpGCL c ->
  iid_wpf e c ->
  expectation f ->
  wpf c (indicator e) x == 1 ->
  wpf (unroll e c i) f x == (const 0) i.
Proof.
  revert c e x f; unfold indicator.
  induction i; intros c e x f Hwf Hiid Hexp Heq; unfold compose, const.
  - reflexivity.
  - rewrite Hiid.
    rewrite IHi; auto.
    unfold const. rewrite Qmult_0_r, Qplus_0_l.
    apply sdfasdkdf; auto.
    apply asdkdf; auto.
Qed.

Lemma wlpf_unroll_const_1 c e x i f :
  wf_cpGCL c ->
  iid_wlpf e c ->
  wpf c (indicator e) x == 1 ->
  wlpf (unroll e c i) f x == (const 1) i.
Proof.
  revert c e x f; unfold indicator.
  induction i; intros c e x f Hwf Hiid Heq; unfold compose, const.
  - reflexivity.
  - rewrite Hiid. rewrite IHi; auto.
    unfold const. rewrite Qmult_1_r.
    rewrite Heq. rewrite asdkdfgf'; auto; lra.
Qed.

(** wp and wpf coincide when every loop in the program is iid. *)
Lemma wp_wpf (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  expectation f ->
  wp c f (wpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hiid Hexp; simpl;
    inversion Hwf; inversion Hiid; subst;
      try solve [econstructor; auto; reflexivity].
  - unfold compose.
    econstructor; auto.
    apply IHc1; auto.
    apply wpf_expectation; auto.
    reflexivity.
  - set (ch := flip wpf f ∘ unroll e c).
    apply wp_while with (ch := ch).
    + reflexivity.
    + intro n.
      eexists. split.
      * apply IHc; auto.
        unfold ch.
        unfold compose, flip.
        apply wpf_expectation; auto.
        apply wf_unroll; auto.
      * intro x. unfold ch. unfold compose. unfold flip.
        simpl. reflexivity.
    + apply supremum_pointwise; intro x.
      assert (Hle: wpf c (indicator e) x <= 1).
      { apply wpf_bounded; auto.
        intro y; unfold indicator; destruct (e y); lra. }
      destruct (Qeq_dec (wpf c (indicator e) x) 1).
      -- unfold indicator in *.
         eapply Proper_supremum_Q.
         rewrite q, Qminus_cancel, Qdiv_0_den; reflexivity.
         intro i. unfold app_chain, flip.
         unfold ch. unfold compose, flip.
         destruct H5; apply wpf_unroll_const_0; auto.
         apply const_supremum.
         intro i; unfold const. apply Qeq_equ; reflexivity.
      -- apply geometric''_supremum.
           ++ apply wpf_expectation; auto.
              intro y; destruct (e y); auto; lra.
           ++ apply wpf_expectation; auto.
              intro y; destruct (e y); auto; lra.
           ++ unfold indicator in *; lra.
           ++ intro i; destruct H5; apply wpf_chain_geometric_series; auto.
Qed.

(** wlp and wlpf coincide when every loop in the program is iid. *)
Lemma wlp_wlpf (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  bounded_expectation f ->
  wlp c f (wlpf c f).
Proof.
  revert f.
  induction c; intros f Hwf Hiid Hexp; simpl;
    inversion Hwf; inversion Hiid; subst; try solve [constructor; reflexivity].
  - unfold compose.
    econstructor; auto.
    apply IHc1; auto.
    apply wlpf_bounded_expectation; auto.
    reflexivity.
  - econstructor; eauto; reflexivity.
  - econstructor; eauto. reflexivity.
  - set (ch := flip wlpf f ∘ unroll e c).
    apply wlp_while with (ch := ch).
    + reflexivity.
    + intro n.
      eexists. split.
      * apply IHc; auto.
        unfold ch.
        unfold compose, flip.
        apply wlpf_bounded_expectation; auto.
        apply wf_unroll; auto.
      * intro x. unfold ch. unfold compose. unfold flip.
        simpl. reflexivity.
    + apply infimum_pointwise; intro x.
      assert (Hle: wpf c (indicator e) x <= 1).
      { apply wpf_bounded; auto.
        intro y; unfold indicator; destruct (e y); lra. }
      destruct (Qeq_dec (wpf c (indicator e) x) 1).
      -- unfold indicator in *.
         eapply Proper_infimum_Q.
         rewrite Qeq_eq_bool. reflexivity. auto.
         intro i. unfold app_chain, ch, flip, compose.
         destruct H5; apply wlpf_unroll_const_1; auto.
         apply const_infimum.
         intro; apply Qeq_equ; reflexivity.
      -- eapply Proper_infimum_Q. rewrite Qeq_bool_false; auto.
         reflexivity. reflexivity.
         apply wlpf_infimum.
         ++ apply wlpf_expectation; auto.
            intro y; destruct (Hexp y); destruct (e y); auto; lra.
         ++ apply wpf_expectation; auto.
            intro y; destruct (Hexp y); destruct (e y); auto; lra.
         ++ unfold indicator in *; lra.
         ++ set (a := wlpf c (fun st' : St => if e st' then 0 else f st') x).
            set (b := wpf c (fun st' : St => if e st' then 1 else 0) x).
            assert (H: b == wpf c (fun y => if e y then const 1 y else 0) x).
            { eapply Proper_wpf; auto. intro y; destruct (e y); reflexivity. }
            rewrite H; clear H.
            rewrite Qplus_comm; unfold a.
            rewrite <- wlpf_linear'.
            apply wlpf_bounded; auto.
            intro y; destruct (Hexp y); destruct (e y); auto; unfold const; lra.
         ++ intro i; destruct H5; apply wlpf_chain_series; auto.
Qed.

Theorem cwp_cwpf (c : cpGCL) (f : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  expectation f ->
  cwp c f (cwpf c f).
Proof.
  intros Hwf Hiid Hexp; unfold cwp.
  exists (wpf c f). exists (wlpf c (const 1)); split.
  - split.
    + apply wp_wpf; auto.
    + apply wlp_wlpf; auto.
      intro; unfold const; lra.
  - reflexivity.
Qed.
