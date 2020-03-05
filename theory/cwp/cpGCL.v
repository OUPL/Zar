(** The cpGCL language and associated definitions. *)

Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.

Definition val := bool.
Definition St : Type := nat -> val.
Definition empty : St := fun _ => false.
Definition upd (x : nat) (v : val) (st : St) : St :=
  fun y => if Nat.eqb y x then v else st y.
Definition exp := St -> val.

Inductive cpGCL : Type :=
| CSkip : cpGCL
| CAbort : cpGCL
| CAssign : nat -> exp -> cpGCL
| CSeq : cpGCL -> cpGCL -> cpGCL
| CIte : exp -> cpGCL -> cpGCL -> cpGCL
| CChoice : Q -> cpGCL -> cpGCL -> cpGCL
| CWhile : exp -> cpGCL -> cpGCL
| CObserve : exp -> cpGCL.

Record prog :=
  { prog_com : cpGCL
  ; prog_query : exp }.

Notation "a ';;' b" := (CSeq a b) (at level 100, right associativity) : cpGCL_scope.
Open Scope cpGCL_scope.

(* TODO: restrictions on reading/writing to variables within
   while-loops to ensure correctness of tree inference. *)
Inductive wf_cpGCL : cpGCL -> Prop :=
| wf_skip : wf_cpGCL CSkip
| wf_abort : wf_cpGCL CAbort
| wf_assign : forall x e, wf_cpGCL (CAssign x e)
| wf_seq : forall c1 c2,
    wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CSeq c1 c2)
| wf_ite : forall e c1 c2,
    wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CIte e c1 c2)
| wf_cchoice : forall p c1 c2,
    0 <= p <= 1 -> wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CChoice p c1 c2)
| wf_while : forall e body, wf_cpGCL body -> wf_cpGCL (CWhile e body)
| wf_observe : forall e, wf_cpGCL (CObserve e).


(** f is an expectation. *)
Definition expectation {A : Type} (f : A -> Q) := forall x, 0 <= f x.

(** f is a bounded expectation. *)
Definition bounded_expectation {A : Type} (f : A -> Q) := forall x, 0 <= f x <= 1.

(* Require Import FunctionalExtensionality. *)

(* Lemma kjfg (e e0 : exp) n x : *)
(*   e (upd n (e0 (upd n (e0 x) x)) (upd n (e0 x) x)) = *)
(*   e (upd n (e0 x) x). *)
(* Proof. *)
(*   f_equal. apply functional_extensionality; intro y. *)
(*   unfold upd.  *)
(*   destruct (Nat.eqb_spec y n). *)

(* Lemma upd_twice (n : nat) (e : exp) (x : St) : *)
(*   (upd n (e (upd n (e x) x)) x) = (upd n (e x) x). *)
(* Proof. *)
(*   apply functional_extensionality; intro y. *)
(*   destruct (e x). unfold upd. *)
(*   destruct (Nat.eqb_spec y n); subst; auto. *)
(* Qed. *)

(* Lemma jkdfgdf (f : bool -> bool) : *)
(*   f = const false \/ f = const true \/ f = id \/ f = negb. *)
(* Proof. *)
(*   destruct (f false) eqn:Hf; destruct (f true) eqn:Ht. *)
(*   - right; left; apply functional_extensionality; intros []; auto. *)
(*   - right; right; right; apply functional_extensionality; intros []; auto. *)
(*   - right; right; left; apply functional_extensionality; intros []; auto. *)
(*   - left; apply functional_extensionality; intros []; auto. *)
(* Qed. *)

(* Local Open Scope program_scope. *)
(* Lemma bool_involutive (f : bool -> bool) : *)
(*   (exists c, f = const c) \/ f ∘ f = id. *)
(* Proof. *)
(*   unfold compose, const. *)
(*   destruct (jkdfgdf f) as [H|[H|[H|H]]]; subst. *)
(*   - left; exists false; auto. *)
(*   - left; exists true; auto. *)
(*   - right; reflexivity. *)
(*   - right. apply functional_extensionality; intros []; auto. *)
(* Qed. *)

(* (* Lemma upd_twice (n : nat) (e : exp) (x : St) : *) *)
(* (*   e (upd n () x) *) *)
(* (* Proof. *) *)
(* (*   apply functional_extensionality; intro y. *) *)
(* (*   destruct (e x). unfold upd. *) *)
(* (*   destruct (Nat.eqb_spec y n); subst; auto. *) *)
(* (* Qed. *) *)

(* Lemma upd_shadow n st z y : *)
(*   upd n y (upd n z st) = upd n y st. *)
(* Proof. *)
(*   apply functional_extensionality; intro x. *)
(*   unfold upd. destruct (Nat.eqb_spec x n); subst; reflexivity. *)
(* Qed. *)

(* (* Lemma upd_ext (st1 st2 : St) (e : exp) : *) *)
(* (*   (forall x, st1 x = st2 x) -> *) *)
(* (*   e st1 = e st2. *) *)
(* (* Proof. *) *)
(* (*   apply functional_extensionality in  *) *)
(* (*   intro Heq.  *) *)
(* (* Qed. *) *)
