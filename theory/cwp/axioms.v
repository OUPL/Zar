(** Try to derive strong LEM from the regular one plus indefinite
    description. *)

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.IndefiniteDescription.

Definition classicT (P : Prop) : {P} + {~ P}.
Proof.
  generalize (classic P); intro Hc.
  generalize (constructive_indefinite_description); intro Hid.
  set (f := fun b => if b : bool then P else ~ P).
  assert (exists b, f b).
  { destruct Hc.
    - exists true; auto.
    - exists false; auto. }
  apply Hid in H.
  destruct H. unfold f in f0.
  destruct x.
  - left; auto.
  - right; auto.
Qed.

(* Require Import Coq.Logic.IndefiniteDescription. *)
Require Import Coq.Logic.ConstructiveEpsilon.

Axiom LPO : forall P : nat -> Prop, (forall n, P n \/ ~ P n) -> (exists n, P n) \/ (~ exists n, P n).

Lemma sumbool_dec (P : Prop) :
  {P} + {~P} ->
  P \/ ~ P.
Proof. intros []; auto. Qed.

Lemma asdf (P : bool -> Prop) :
  (forall b, {P b} + {~ P b}) ->
  {exists b, P b} + {~ exists b, P b}.
Proof.
  intro Hdec.
  destruct (Hdec true).
  - left; exists true; auto.
  - destruct (Hdec false).
    + left; exists false; auto.
    + right. intro HC.
      destruct HC as [[] ?]; congruence.
Qed.

Lemma bool_indefinite_description (P : bool -> Prop) (P_dec : forall b, {P b} + {~ P b}) :
  (exists b, P b) ->
  {b : bool | P b}.
Proof.
  set (f := fun b : bool => if b then 0 else 1).
  set (g := fun n => match n with
                  | O => true
                  | _ => false
                  end).
  apply constructive_indefinite_ground_description with (f:=f) (g:=g); auto.
  intros []; reflexivity.
Qed.

Lemma strong_LPO (P : nat -> Prop) :
  (forall n, {P n} + {~ P n}) ->
  {exists n, P n} + {~ exists n, P n}.
Proof.
  intro Hdec.
  generalize (constructive_indefinite_ground_description
                nat id id (fun x => eq_refl x)).
  intro Hid.
  set (f := fun b : bool => if b then exists n : nat, P n else ~ exists n : nat, P n).
  assert (exists b, f b).
  { destruct (LPO P (fun n => sumbool_dec (P n) (Hdec n))).
    - exists true; auto.
    - exists false; auto. }
  apply bool_indefinite_description in H.
  - admit.
  - intro b. destruct b. simpl.
  assert ({b : bool | f b}).
  { 
  (* pose proof (Hid f  *)
  assert (f_sumbool: forall b, {f b} + {~ f b}).
  { intro b. destruct b; simpl.
Admitted.

(* Lemma strong_LPO (P : nat -> Prop) : *)
(*   (forall n, P n \/ ~ P n) -> *)
(*   {exists n, P n} + {~ exists n, P n}. *)
(* Proof. *)
(*   generalize (constructive_indefinite_ground_description *)
(*                 nat id id (fun x => eq_refl x) P). *)
(*   intro H. *)  
(*   intro Hdec. *)
(*   apply LPO in Hdec. *)
(* Admitted. *)

Ltac destruct_LPO :=
  match goal with
  | [ |- context[if strong_LPO ?x ?y then _ else _] ] =>
    destruct (strong_LPO x y)
  | [ H: context[if strong_LPO ?x ?y then _ else _] |- _] =>
    destruct (strong_LPO x y)
  end.
