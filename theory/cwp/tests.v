(** Testing functional CWP and compilation+inference on example *)
(*     programs.  *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import FunctionalExtensionality.
Local Open Scope program_scope.

Require Import List.
Import ListNotations.

Require Import compile.
Require Import cpGCL.
Require Import cwp.
Require Import cwp_cwpf.
Require Import geometric.
Require Import infer.
(* Require Import measure. *)
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.
Require Import itree.
Local Open Scope Q_scope.

(** Testing compilation and inference on example programs *)

Definition sample (x : nat) (p : Q) : cpGCL :=
  CChoice p (CAssign x (const true)) (CAssign x (const false)).

Definition goldfish_piranha : cpGCL :=
  sample 0%nat (1#2) ;;;
  CAssign 1%nat (const true) ;;;
  CChoice (1#2) (CAssign 2%nat (fun st => st 0%nat))
                (CAssign 2%nat (fun st => st 1%nat)) ;;;
  CObserve (fun st => eqb (st 2%nat) true).

(* Definition goldfish_piranha_tree : tree St := *)
(*   evalCompile' goldfish_piranha empty. *)

(* Definition gp_tree := reduce_tree (fmap (fun st => st O) goldfish_piranha_tree). *)
(* Definition gp_itree := remove_taus (unbiased_tree_to_itree' gp_tree). *)
(* Definition gp_seq := measure_seq gp_itree id. *)
(* Definition gp_chain := partial_sum gp_seq. *)

(* Definition bits := map (fun b => if b : bool then 1 else 0) ∘ bit_sequences. *)
(* Definition ind := preimageb' gp_itree id ∘ bit_sequences. *)
(* Definition bits_ind := tuple bits ind. *)

(* Eval compute in gp_tree. *)
(* (* Choice (1 # 2) (Leaf true) (Choice (1 # 2) (Fail bool 0) (Leaf false)) *) *)

(* Eval compute in (prefix' gp_itree 10). *)
(* Eval compute in (exists_tau gp_itree 3). *)
(* Eval compute in (walk_path gp_itree [true; false; false] 10). *)

(* Eval compute in (first_n bits_ind 40). *)

(* Eval compute in (filter (fun p => snd p) (first_n bits_ind 40)). *)

(* (* Eval compute in (map (preimageb' gp_itree id) (first_n bit_sequences 10)). *) *)

(* (* Eval compute in (map Qred (first_n (partial_sum fair_coin_chain) 50)). *) *)

(* (* Eval compute in (first_n gp_chain 100). *) *)
(* (* Eval compute in (gp_chain 5000). *) *)


(* Definition ex1_f := fun st => if st O : bool then 1 else 0. *)
(* Example ex1 : infer ex1_f goldfish_piranha_tree == 2#3. *)
(* Proof. reflexivity. Qed. *)
(* Example ex2 : infer ex1_f goldfish_piranha_tree == *)
(*               cwpf goldfish_piranha ex1_f empty. *)
(* Proof. reflexivity. Qed. *)

(* Definition test_abort : cpGCL := *)
(*   CChoice (1#3) (CAssign 0%nat (const true)) CAbort. *)

(* Definition test_abort_tree : tree St := evalCompile' test_abort empty. *)

(* (* Eval compute in (evalCompile' test_abort empty). *) *)

(* Definition ex3_f := fun st => if st O : bool then 1 else 0. *)
(* Example ex3 : infer ex3_f test_abort_tree == 1#3. *)
(* Proof. reflexivity. Qed. *)
(* Example ex4 : infer ex3_f test_abort_tree == cwpf test_abort ex3_f empty. *)
(* Proof. reflexivity. Qed. *)

(* Definition ex5_f := fun st => if st O : bool then 1 else 0. *)
(* Example ex5 : infer ex5_f test_abort_tree == 1#3. *)
(* Proof. reflexivity. Qed. *)
(* Example ex6 : infer ex5_f test_abort_tree == cwpf test_abort ex5_f empty. *)
(* Proof. reflexivity. Qed. *)

(* Definition ex7_f := fun st => if negb (st O) then 1 else 0. *)
(* Example ex7 : infer ex7_f test_abort_tree == 0. *)
(* Proof. reflexivity. Qed. *)
(* Example ex8 : infer ex7_f test_abort_tree == cwpf test_abort ex7_f empty. *)
(* Proof. reflexivity. Qed. *)

(* Example ex9 : infer (const 1) test_abort_tree == 1#3. *)
(* Proof. reflexivity. Qed. *)
(* Example ex10 : infer (const 1) test_abort_tree == *)
(*                cwpf test_abort (const 1) empty. *)
(* Proof. reflexivity. Qed. *)

(* (** infer_f (const 1) yields the probability of terminating. *) *)
(* Example ex11 : infer_f (const 1) test_abort_tree == 1#3. *)
(* Proof. reflexivity. Qed. *)
(* (** infer_f_lib (const 1) always yields 1. *) *)
(* Example ex12 : infer_f_lib (const 1) test_abort_tree == 1. *)
(* Proof. reflexivity. Qed. *)

(* Definition ex13_f := fun st => if st O : bool then 1 else 0. *)
(* Example ex13 : infer ex13_f test_abort_tree == 1#3. *)
(* Proof. reflexivity. Qed. *)
(* Example ex14 : infer ex13_f test_abort_tree == *)
(*                cwpf test_abort ex13_f empty. *)
(* Proof. reflexivity. Qed. *)

(* Definition ex15_c := CChoice (1#2) CSkip CAbort. *)
(* Example ex15 : infer (const 1) (evalCompile' ex15_c empty) == 1#2. *)
(* Proof. reflexivity. Qed. *)
(* Example ex16 : infer (const 1) (evalCompile' ex15_c empty) == *)
(*                cwpf ex15_c (const 1) empty. *)
(* Proof. reflexivity. Qed. *)

(* Definition fair_coin : cpGCL := *)
(*   CAssign 0 (const false) ;;; *)
(*   CAssign 1 (const false) ;;; *)
(*   CWhile (fun st => eqb (st 0%nat) (st 1%nat)) *)
(*          (sample 0%nat (1#3) ;;; sample 1%nat (1#3)). *)

(* Definition fair_coin_tree : tree St := evalCompile' fair_coin empty. *)

(* Definition ex17_f := fun st => if st O : bool then 1 else 0. *)
(* Example ex17 : infer ex17_f fair_coin_tree == 1#2. *)
(* Proof. reflexivity. Qed. *)
(* Example ex18 : infer ex17_f fair_coin_tree == cwpf fair_coin ex17_f empty. *)
(* Proof. reflexivity. Qed. *)

(* (* Definition fair_coin_itree := unbiased_tree_to_itree' fair_coin_tree. *) *)
(* (* Definition fair_coin_chain := measure_chain fair_coin_itree (fun st => st O). *) *)

(* (* Definition bits := map (fun b => if b : bool then 1 else 0) ∘ bit_sequences. *) *)
(* (* Definition ind := preimageb' fair_coin_itree (fun st => st O) ∘ bit_sequences. *) *)
(* (* Definition bits_ind := tuple bits ind. *) *)

(* (* Eval compute in (first_n bits_ind 1000). *) *)

(* (* Eval compute in (map (preimageb' fair_coin_itree (fun st => st O)) *) *)
(* (*                      (first_n bit_sequences 10)). *) *)

(* (* (* Eval compute in (map Qred (first_n (partial_sum fair_coin_chain) 50)). *) *) *)
(* (* Eval compute in (partial_sum fair_coin_chain 100). *) *)



(* Definition two_thirds_loop (x : nat) (z : nat) : cpGCL := *)
(*   CAssign z (const true) ;;; *)
(*     CWhile (fun st => st z) *)
(*            (CChoice (1#2) *)
(*                     (CAssign x (const true) ;;; *)
(*                      CAssign z (const false)) *)
(*                     (CChoice (1#2) *)
(*                              CSkip *)
(*                              (CAssign x (const false) ;;; *)
(*                               CAssign z (const false)))). *)

(* Definition fair_coin_loop : cpGCL := *)
(*   CAssign 0 (const false) ;;; *)
(*   CAssign 1 (const false) ;;; *)
(*   CWhile (fun st => eqb (st 0%nat) (st 1%nat)) *)
(*          (two_thirds_loop 0%nat 2%nat ;;; *)
(*           two_thirds_loop 1%nat 2%nat). *)

(* Definition fair_coin_loop_tree : tree St := evalCompile' fair_coin_loop empty. *)

(* Definition ex19_f := fun st => if st O : bool then 1 else 0. *)
(* Example ex19 : infer ex19_f fair_coin_loop_tree == 1#2. *)
(* Proof. reflexivity. Qed. *)
(* Example ex20 : infer ex19_f fair_coin_loop_tree == *)
(*                cwpf fair_coin_loop ex19_f empty. *)
(* Proof. reflexivity. Qed. *)

(* (* Eval compute in fair_coin_loop_tree. *) *)

(* (* Lemma goldfish_piranha_cwp (f : St -> Q) : *) *)
(* (*   cwp goldfish_piranha (fun st => if st O then 1 else 0) f -> f ==f const (2#3). *) *)
(* (* Proof. *) *)
(* (*   intros (f' & g' & [Hwp Hwlp] & Hf) x. *) *)
(* (*   repeat wp_inversion; repeat wlp_inversion; reflexivity. *) *)
(* (* Qed. *) *)

(* (* Ltac rewrite_equiv := *) *)
(* (*   match goal with *) *)
(* (*   | [ H : forall _ : St, _ == _ |- _ ] => rewrite H; simpl *) *)
(* (*   end. *) *)

(* (** Proving iid-ness of loops and using cwpf to help automate cwp *)
(*   reasoning. *) *)

(* Lemma simple_loop_iid : *)
(*   iid_wpf (const true) (CAssign O (const true)). *)
(* Proof. *)
(*   intros f x i. simpl. *)
(*   unfold compose, const, indicator. rewrite Qmult_1_l, Qplus_0_r. *)
(*   revert x. *)
(*   induction i; intro x. simpl. unfold const. reflexivity. *)
(*   simpl in *; unfold compose; rewrite IHi; reflexivity. *)
(* Qed. *)

(* (** Some properties of upd (requiring funext) *) *)

(* Lemma upd_shadow n x y st : *)
(*   upd n x (upd n y st) = upd n x st. *)
(* Proof. *)
(*   apply functional_extensionality. *)
(*   intro i; unfold upd; simpl. *)
(*   destruct (Nat.eqb_spec i n); subst; reflexivity. *)
(* Qed. *)

(* Lemma upd_eq n st : *)
(*   upd n (st n) st = st. *)
(* Proof. *)
(*   apply functional_extensionality. *)
(*   intro i; unfold upd; destruct (Nat.eqb_spec i n); subst; auto. *)
(* Qed. *)

(* Lemma upd_comm n m x y st : *)
(*   n <> m -> *)
(*   upd n x (upd m y st) = upd m y (upd n x st). *)
(* Proof. *)
(*   intro Hneq. *)
(*   unfold upd. *)
(*   apply functional_extensionality; intro i. *)
(*   destruct (Nat.eqb_spec i n); subst. *)
(*   - destruct (Nat.eqb_spec n m); subst; congruence. *)
(*   - destruct (Nat.eqb_spec i m); subst; congruence. *)
(* Qed. *)

(* Lemma simple_loop2_iid : *)
(*   iid_wpf (fun st => st O) (CChoice (1#2) (CAssign O (const true)) (CAssign O (const false))). *)
(* Proof. *)
(*   intros f x i. simpl. unfold compose, const, indicator. simpl. *)
(*   intro Hx. rewrite Hx. *)
(*   field_simplify_eq. *)
(*   cut (wpf *)
(*          (unroll (fun st : St => st O) *)
(*                  (CChoice (1 # 2) (CAssign 0 (fun _ : St => true)) *)
(*                           (CAssign 0 (fun _ : St => false))) i) f *)
(*          (upd 0 true x) == *)
(*        wpf *)
(*          (unroll (fun st : St => st O) *)
(*                  (CChoice (1 # 2) (CAssign 0 (fun _ : St => true)) *)
(*                           (CAssign 0 (fun _ : St => false))) i) f x). *)
(*   { intros H. rewrite H. clear H. *)
(*     cut (wpf *)
(*            (unroll (fun st : St => st O) *)
(*                    (CChoice (1 # 2) (CAssign 0 (fun _ : St => true)) *)
(*                             (CAssign 0 (fun _ : St => false))) i) f *)
(*            (upd 0 false x) == *)
(*          f (upd 0 false x)). *)
(*     { lra. } *)
(*     destruct i; reflexivity. } *)
(*   revert Hx. revert x. *)
(*   induction i; intros x Hx; simpl. *)
(*   + rewrite Hx. reflexivity. *)
(*   + rewrite Hx. unfold compose. simpl. *)
(*     field_simplify_eq. *)
(*     rewrite IHi; auto. *)
(*     rewrite IHi; auto. *)
(*     rewrite upd_shadow. reflexivity. *)
(* Qed. *)

(* Lemma wpf_unroll_false e c i f st : *)
(*   e st = false -> *)
(*   wpf (unroll e c i) f st == f st. *)
(* Proof. intro He; destruct i; simpl; rewrite He; reflexivity. Qed. *)

(* Lemma wlpf_unroll_false e c i f st : *)
(*   e st = false -> *)
(*   wlpf (unroll e c i) f st == f st. *)
(* Proof. intro He; destruct i; simpl; rewrite He; reflexivity. Qed. *)

(* Lemma upd_1_0_shadow st x y z w : *)
(*   upd 1 x (upd 0 y (upd 1 z (upd 0 w st))) = *)
(*   upd 1 x (upd 0 y st). *)
(* Proof. repeat (rewrite upd_comm; auto; rewrite upd_shadow). Qed. *)

(* Lemma iid_wpf_fair_coin : *)
(*   iid_wpf (fun st : St => eqb (st O) (st (S O))) (sample 0 (1 # 3);;; sample 1 (1 # 3)). *)
(* Proof. *)
(*   intros f x i. simpl. *)
(*   unfold compose, const, indicator; simpl. *)
(*   intro Hx. rewrite Hx. *)
(*   field_simplify_eq. *)
(*   rewrite wpf_unroll_false with (st := upd 1 false (upd 0 true x)); auto. *)
(*   rewrite wpf_unroll_false with (st := upd 1 true (upd 0 false x)); auto. *)
(*   cut (wpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                    (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f *)
(*            (upd 1 true (upd 0 true x)) == *)
(*        wpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                    (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f x). *)
(*   { intro H; rewrite H; clear H. *)
(*     cut (wpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                      (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f *)
(*              (upd 1 false (upd 0 false x)) == *)
(*          wpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                      (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f x). *)
(*     { lra. } *)
(*     revert x Hx. *)
(*     induction i; intros x Hx; simpl. *)
(*     - rewrite Hx; reflexivity. *)
(*     - rewrite Hx. unfold compose, const. *)
(*       field_simplify_eq. *)
(*       rewrite !IHi; auto. *)
(*       rewrite !upd_1_0_shadow; lra. } *)
(*   revert x Hx. *)
(*   induction i; intros x Hx; simpl. *)
(*   - rewrite Hx; reflexivity. *)
(*   - rewrite Hx. unfold compose, const. *)
(*     field_simplify_eq. *)
(*     rewrite !IHi; auto. *)
(*     rewrite !upd_1_0_shadow; lra. *)
(* Qed. *)

(* Lemma iid_wlpf_fair_coin : *)
(*   iid_wlpf (fun st : St => eqb (st O) (st (S O))) (sample 0 (1 # 3);;; sample 1 (1 # 3)). *)
(* Proof. *)
(*   intros f x i. simpl. *)
(*   unfold compose, const, indicator; simpl. *)
(*   intro Hx. rewrite Hx. *)
(*   field_simplify_eq. *)
(*   rewrite wlpf_unroll_false with (st := upd 1 false (upd 0 true x)); auto. *)
(*   rewrite wlpf_unroll_false with (st := upd 1 true (upd 0 false x)); auto. *)
(*   cut (wlpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                     (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f *)
(*             (upd 1 true (upd 0 true x)) == *)
(*        wlpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                     (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f x). *)
(*   { intro H; rewrite H; clear H. *)
(*     cut (wlpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                       (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f *)
(*               (upd 1 false (upd 0 false x)) == *)
(*          wlpf (unroll (fun st : St => Bool.eqb (st O) (st (S O))) *)
(*                       (sample 0 (1 # 3);;; sample 1 (1 # 3)) i) f x). *)
(*     { lra. } *)
(*     revert x Hx. *)
(*     induction i; intros x Hx; simpl. *)
(*     - rewrite Hx; reflexivity. *)
(*     - rewrite Hx. unfold compose, const. *)
(*       field_simplify_eq. *)
(*       rewrite !IHi; auto. *)
(*       rewrite !upd_1_0_shadow; lra. } *)
(*   revert x Hx. *)
(*   induction i; intros x Hx; simpl. *)
(*   - rewrite Hx; reflexivity. *)
(*   - rewrite Hx. unfold compose, const. *)
(*     field_simplify_eq. *)
(*     rewrite !IHi; auto. *)
(*     rewrite !upd_1_0_shadow; lra. *)
(* Qed. *)

(* Lemma wf_fair_coin : wf_cpGCL fair_coin. *)
(* Proof. repeat constructor; lra. Qed. *)

(* Lemma iid_fair_coin : iid_cpGCL fair_coin. *)
(* Proof. *)
(*   repeat constructor. *)
(*   - apply iid_wpf_fair_coin. *)
(*   - apply iid_wlpf_fair_coin. *)
(* Qed. *)

(* Lemma fair_coin_cwp (f : St -> Q) : *)
(*   cwp fair_coin (fun st => if st O then 1 else 0) f -> f ==f const (1#2). *)
(* Proof. *)
(*   intros Hcwp x. *)
(*   transitivity (cwpf fair_coin (fun st => if st O then 1 else 0) x). *)
(*   - eapply cwp_deterministic; eauto. *)
(*     apply cwp_cwpf; auto. *)
(*     + apply wf_fair_coin. *)
(*     + apply iid_fair_coin. *)
(*     + intro y; destruct (y O); lra. *)
(*   - compute. (* :O *) *)
(*     reflexivity. *)
(* Qed. *)

(* Lemma fair_coin_cwp' (f : St -> Q) : *)
(*   expectation f -> *)
(*   cwp fair_coin f (cwpf fair_coin f). *)
(* Proof. *)
(*   intro Hexp; apply cwp_cwpf; auto. *)
(*   - apply wf_fair_coin. *)
(*   - apply iid_fair_coin. *)
(* Qed. *)

(* Lemma fair_coin_cwp'' : *)
(*   cwp fair_coin (fun st => if st O then 1 else 0) *)
(*       (cwpf fair_coin (fun st => if st O then 1 else 0)). *)
(* Proof. *)
(*   apply fair_coin_cwp'. *)
(*   intro x; destruct (x O); lra. *)
(* Qed. *)

(* Eval compute in Qred ∘ cwpf fair_coin (fun st => if st O then 1 else 0). *)

(* Definition fair_coin_noinit : cpGCL := *)
(*   CWhile (fun st => eqb (st 0%nat) (st 1%nat)) *)
(*          (sample 0%nat (1#3) ;;; sample 1%nat (1#3)). *)

(* Lemma fair_coin_noinit_cwp' (f : St -> Q) : *)
(*   expectation f -> *)
(*   cwp fair_coin_noinit f (cwpf fair_coin_noinit f). *)
(* Proof. *)
(*   intro Hexp; apply cwp_cwpf; auto. *)
(*   - repeat constructor; lra. *)
(*   - repeat constructor. *)
(*     + apply iid_wpf_fair_coin. *)
(*     + apply iid_wlpf_fair_coin. *)
(* Qed. *)

(* Lemma fair_coin_noinit_cwp'' : *)
(*   cwp fair_coin_noinit (fun st => if st O then 1 else 0) *)
(*       (cwpf fair_coin_noinit (fun st => if st O then 1 else 0)). *)
(* Proof. *)
(*   apply fair_coin_noinit_cwp'. *)
(*   intro x; destruct (x O); lra. *)
(* Qed. *)

(* Eval compute in Qred (cwpf fair_coin_noinit (fun st => if st O then 1 else 0) *)
(*                            (upd O true (upd (S O) true empty))). *)
