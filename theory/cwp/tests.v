Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.

Require Import compile.
Require Import cpGCL.
Require Import cwp.
Require Import infer.
Require Import tree.

(** Testing compilation and inference on example programs *)

Definition sample (x : nat) (p : Q) : cpGCL :=
  CChoice p (CAssign x (const true)) (CAssign x (const false)).

Definition goldfish_piranha : cpGCL :=
  sample 0%nat (1#2) ;;
  CAssign 1%nat (const true) ;;
  CChoice (1#2) (CAssign 2%nat (fun st => st 0%nat))
                (CAssign 2%nat (fun st => st 1%nat)) ;;
  CObserve (fun st => eqb (st 2%nat) true).

Definition goldfish_piranha_tree : tree St :=
  evalCompile' goldfish_piranha empty.

Definition ex1_f := fun st => if st O : bool then 1 else 0.
Example ex1 : infer ex1_f goldfish_piranha_tree == 2#3.
Proof. reflexivity. Qed.
Example ex2 : infer ex1_f goldfish_piranha_tree ==
              cwp_iid goldfish_piranha ex1_f empty.
Proof. reflexivity. Qed.

Definition test_abort : cpGCL :=
  CChoice (1#3) (CAssign 0%nat (const true)) CAbort.

Definition test_abort_tree : tree St := evalCompile' test_abort empty.

(* Eval compute in (evalCompile' test_abort empty). *)

Definition ex3_f := fun st => if st O : bool then 1 else 0.
Example ex3 : infer ex3_f test_abort_tree == 1#3.
Proof. reflexivity. Qed.
Example ex4 : infer ex3_f test_abort_tree == cwp_iid test_abort ex3_f empty.
Proof. reflexivity. Qed.

Definition ex5_f := fun st => if st O : bool then 1 else 0.
Example ex5 : infer ex5_f test_abort_tree == 1#3.
Proof. reflexivity. Qed.
Example ex6 : infer ex5_f test_abort_tree == cwp_iid test_abort ex5_f empty.
Proof. reflexivity. Qed.

Definition ex7_f := fun st => if negb (st O) then 1 else 0.
Example ex7 : infer ex7_f test_abort_tree == 0.
Proof. reflexivity. Qed.
Example ex8 : infer ex7_f test_abort_tree == cwp_iid test_abort ex7_f empty.
Proof. reflexivity. Qed.

Example ex9 : infer (const 1) test_abort_tree == 1#3.
Proof. reflexivity. Qed.
Example ex10 : infer (const 1) test_abort_tree ==
               cwp_iid test_abort (const 1) empty.
Proof. reflexivity. Qed.

(** infer_f (const 1) yields the probability of terminating. *)
Example ex11 : infer_f (const 1) test_abort_tree == 1#3.
Proof. reflexivity. Qed.
(** infer_f_lib (const 1) always yields 1. *)
Example ex12 : infer_f_lib (const 1) test_abort_tree == 1.
Proof. reflexivity. Qed.

Definition ex13_f := fun st => if st O : bool then 1 else 0.
Example ex13 : infer ex13_f test_abort_tree == 1#3.
Proof. reflexivity. Qed.
Example ex14 : infer ex13_f test_abort_tree ==
               cwp_iid test_abort ex13_f empty.
Proof. reflexivity. Qed.

Definition ex15_c := CChoice (1#2) CSkip CAbort.
Example ex15 : infer (const 1) (evalCompile' ex15_c empty) == 1#2.
Proof. reflexivity. Qed.
Example ex16 : infer (const 1) (evalCompile' ex15_c empty) ==
               cwp_iid ex15_c (const 1) empty.
Proof. reflexivity. Qed.

Definition fair_coin : cpGCL :=
  CAssign 0 (const false) ;;
  CAssign 1 (const false) ;;
  CWhile (fun st => eqb (st 0%nat) (st 1%nat))
         (sample 0%nat (1#3) ;; sample 1%nat (1#3)).

Definition fair_coin_tree : tree St := evalCompile' fair_coin empty.

Definition ex17_f := fun st => if st O : bool then 1 else 0.
Example ex17 : infer ex17_f fair_coin_tree == 1#2.
Proof. reflexivity. Qed.
Example ex18 : infer ex17_f fair_coin_tree == cwp_iid fair_coin ex17_f empty.
Proof. reflexivity. Qed.

Definition two_thirds_loop (x : nat) (z : nat) : cpGCL :=
  CAssign z (const true) ;;
    CWhile (fun st => st z)
           (CChoice (1#2)
                    (CAssign x (const true) ;;
                     CAssign z (const false))
                    (CChoice (1#2)
                             CSkip
                             (CAssign x (const false) ;;
                              CAssign z (const false)))).

Definition fair_coin_loop : cpGCL :=
  CAssign 0 (const false) ;;
  CAssign 1 (const false) ;;
  CWhile (fun st => eqb (st 0%nat) (st 1%nat))
         (two_thirds_loop 0%nat 2%nat ;;
          two_thirds_loop 1%nat 2%nat).

Definition fair_coin_loop_tree : tree St := evalCompile' fair_coin_loop empty.

Definition ex19_f := fun st => if st O : bool then 1 else 0.
Example ex19 : infer ex19_f fair_coin_loop_tree == 1#2.
Proof. reflexivity. Qed.
Example ex20 : infer ex19_f fair_coin_loop_tree ==
               cwp_iid fair_coin_loop ex19_f empty.
Proof. reflexivity. Qed.

