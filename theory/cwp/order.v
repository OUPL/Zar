Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.QArith.QArith.
Local Open Scope program_scope.

(* Ordered types *)
Class OType (A : Type) : Type :=
  { leq : relation A
  ; leq_preorder : PreOrder leq
  }.

Instance OType_Reflexive A `{o : OType A} : Reflexive leq.
Proof. destruct o; typeclasses eauto. Qed.

Instance OType_Transitive A `{o : OType A} : Transitive leq.
Proof. destruct o; typeclasses eauto. Qed.


(* Pointed ordered types *)
Class PType (A : Type) `{o : OType A} : Type :=
  { bot : A
  ; bot_le : forall x, leq bot x }.


Program Instance OType_arrow A B {oB : OType B} : OType (A -> B) :=
  {| leq := fun f g => forall x, leq (f x) (g x) |}.
Next Obligation.
  constructor. firstorder.
  intros ?; etransitivity; eauto.
Defined.

Program Instance PType_arrow A B `{p : PType B} : PType (A -> B) :=
  {| bot := const bot |}.
Next Obligation. destruct p as [? H]; apply H. Qed.

Definition equ {A : Type} `{OType A} (x y : A) :=
  leq x y /\ leq y x.

(** f is an ω-chain *)
Definition chain {A : Type} `{o : OType A} (f : nat -> A) : Prop :=
  forall i, leq (f i) (f (S i)).

Definition lower_bound {A B : Type} `{OType B} (x : B) (f : A -> B) :=
  forall y, leq x (f y).

Definition upper_bound {A B : Type} `{OType B} (x : B) (f : A -> B) :=
  forall y, leq (f y) x.

Definition infimum {A B : Type} `{OType B} (inf : B) (f : A -> B) :=
  lower_bound inf f /\ forall x, lower_bound x f -> leq x inf.

Definition supremum {A B : Type} `{OType B} (sup : B) (f : A -> B) :=
  upper_bound sup f /\ forall x, upper_bound x f -> leq sup x.

Lemma supremum_unique {A B : Type} `{o : OType B} (x y : B) (f : A -> B) :
  supremum x f -> supremum y f -> equ x y.
Proof.
  intros [H0 H1] [H2 H3]; split.
  - apply H1; auto.
  - apply H3; auto.
Qed.

Definition monotone {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall x y, leq x y -> leq (f x) (f y).

Lemma monotone_chain {A B : Type} `{OType A} `{OType B} (f : A -> B) (g : nat -> A) :
  monotone f ->
  chain g ->
  chain (f ∘ g).
Admitted.

Definition ratio_chain (f g : nat -> Q) := fun i => f i / g i.

Definition postfix_chain {A : Type} `{o : OType A} (f : nat -> A) (n : nat) : nat -> A :=
  fun i => f (i + n)%nat.

Definition postfix_chain_is_chain {A : Type} `{o : OType A} (f : nat -> A) (n : nat) :
  chain f ->
  chain (postfix_chain f n).
Proof.
  unfold postfix_chain.
  intros Hchain i; revert n; induction i; intro n.
  - apply Hchain.
  - specialize (IHi (S n)); rewrite 2!Nat.add_succ_r in IHi; auto.
Qed.

Lemma chain_0_leq {A : Type} `{o : OType A} (f : nat -> A) (n : nat) :
  chain f ->
  leq (f O) (f n).
Proof.
  destruct o as [? [Hrefl Htrans]].
  induction n; intro Hchain.
  - apply Hrefl.
  - eapply Htrans. apply IHn; auto.
    apply Hchain.
Qed.

Lemma chain_leq {A : Type} `{o : OType A} (f : nat -> A) (n m : nat) :
  chain f ->
  (n <= m)%nat ->
  leq (f n) (f m).
Proof. (* use postfix and chain_0_leq *)
Admitted.

Lemma const_supremum {A : Type} `{o : OType A} (f : nat -> A) (x : A) :
  (* chain f -> *) (* not quite necessary *)
  (exists n0, forall n, (n0 <= n)%nat -> leq (f O) (f n0) /\ equ (f n) x) ->
  supremum x f.
Admitted.

(* x is a fixed point of f *)
Definition fixed_point {A : Type} (x : A) (f : A -> A) :=
  f x = x.

(* x is the least fixed point of f *)
Definition lfp {A : Type} `{OType A} (x : A) (f : A -> A) :=
  fixed_point x f /\ (forall y, fixed_point y f -> leq x y).

Program Instance OType_Q : OType Q :=
  { leq := Qle }.
Next Obligation. Admitted.
