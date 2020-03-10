(** Compilation+inference agrees with relational CWP when all loops
    are iid. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Data.Monads.StateMonad.
Local Open Scope program_scope.

Require Import compile.
Require Import cpGCL.
Require Import cwp.
Require Import cwp_cwpf.
Require Import cwpf_infer.
Require Import infer.
Require Import order.
Require Import Q.
Require Import tree.

Lemma wp_infer (c : cpGCL) (f f' : St -> Q) (n : nat) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  expectation f ->
  wp c f (infer_f f ∘ evalCompile c n).
Proof.
  intros Hwf Hiid Hexp.
  eapply Proper_wp. reflexivity. reflexivity.
  intro; symmetry; apply wpf_infer_f; auto.
  apply wp_wpf; auto.
Qed.

Lemma wlp_infer (c : cpGCL) (f f' : St -> Q) (n : nat) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  bounded_expectation f ->
  wlp c f (infer_f_lib f ∘ evalCompile c n).
Proof.
  intros Hwf Hiid Hexp.
  eapply Proper_wlp. reflexivity. reflexivity.
  intro; symmetry; apply wlpf_infer_f_lib; auto.
  apply wlp_wlpf; auto.
Qed.

(* Theorem cwp_infer (c : cpGCL) (f f' : St -> Q) (n : nat) : *)
(*   wf_cpGCL c -> *)
(*   iid_cpGCL c -> *)
(*   expectation f -> *)
(*   cwp c f (infer f ∘ evalCompile c n). *)
(* Proof. *)
(*   intros Hwf Hiid Hexp. *)
(*   eapply Proper_cwp. reflexivity. reflexivity. *)
(*   intro; symmetry; apply cwpf_infer; auto. *)
(*   apply cwp_cwpf; auto. *)
(* Qed. *)

Theorem cwp_infer (c : cpGCL) (f f' : St -> Q) :
  wf_cpGCL c ->
  iid_cpGCL c ->
  expectation f ->
  cwp c f (infer f ∘ evalCompile' c).
Proof.
  intros Hwf Hiid Hexp.
  eapply Proper_cwp. reflexivity. reflexivity.
  intro; symmetry; apply cwpf_infer; auto.
  apply cwp_cwpf; auto.
Qed.
