(** The conditional probabilistic guarded command language (cpGCL). *)

Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.

(** For now we support only boolean values. *)
Definition val := bool.
(** A program state is a map from identifiers (nat) to values. *)
Definition St : Type := nat -> val.
Definition empty : St := fun _ => false.
Definition upd (x : nat) (v : val) (st : St) : St :=
  fun y => if Nat.eqb y x then v else st y.
(** An expression is a function from program states to values. *)
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

(** A cpGCL command is well-formed when all p values in choice
    commands are valid probabilities. *)
(** NOTE: this could be strengthened to [0 < p < 1] since choice
    commands with p=0 or p=1 are unnecessary and can be eliminated. *)
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

(** f is a bounded expectation (bounded above by 1). *)
Definition bounded_expectation {A : Type} (f : A -> Q) := forall x, 0 <= f x <= 1.

(** Predicate asserting that a command contains no observe
  commands. *)
Inductive no_obs : cpGCL -> Prop :=
| no_obs_skip : no_obs CSkip
| no_obs_abort : no_obs CAbort
| no_obs_assign : forall x e, no_obs (CAssign x e)
| no_obs_seq : forall c1 c2,
    no_obs c1 -> no_obs c2 ->
    no_obs (CSeq c1 c2)
| no_obs_ite : forall e c1 c2,
    no_obs c1 -> no_obs c2 ->
    no_obs (CIte e c1 c2)
| no_obs_choice : forall p c1 c2,
    no_obs c1 -> no_obs c2 ->
    no_obs (CChoice p c1 c2)
| no_obs_while : forall e c,
    no_obs c ->
    no_obs (CWhile e c).
