(** The conditional probabilistic guarded command language (cpGCL). *)

Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.

Require Import order.

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

(* Record prog := *)
(*   { prog_com : cpGCL *)
(*   ; prog_query : exp }. *)

Notation "a ';;;' b" := (CSeq a b) (at level 100, right associativity) : cpGCL_scope.
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

Fixpoint wf_cpGCLb (c : cpGCL) : bool :=
  match c with
  | CSkip => true
  | CAbort => true
  | CAssign _ _ => true
  | CSeq c1 c2 => wf_cpGCLb c1 && wf_cpGCLb c2
  | CIte _ c1 c2 => wf_cpGCLb c1 && wf_cpGCLb c2
  | CChoice p c1 c2 =>
    Qle_bool 0 p && Qle_bool p 1 && wf_cpGCLb c1 && wf_cpGCLb c2
  | CWhile _ body => wf_cpGCLb body
  | CObserve _ => true
  end.

(* wf_cpGCL is decidable. *)
Lemma wf_cpGCLb_spec (c : cpGCL) : reflect (wf_cpGCL c) (wf_cpGCLb c).
Proof.
  induction c; simpl; try solve[repeat constructor].
  - destruct IHc1, IHc2; simpl; repeat constructor; auto;
      intro HC; apply n; inversion HC; auto.
  - destruct IHc1, IHc2; simpl; repeat constructor; auto;
      intro HC; apply n; inversion HC; auto.
  - destruct IHc1, IHc2; simpl.
    + destruct (Qle_bool 0 q) eqn:H0; simpl.
      * destruct (Qle_bool q 1) eqn:H1; simpl; constructor.
        -- constructor; auto; split; apply Qle_bool_iff; auto.
        -- intro HC; inversion HC; subst.
           destruct H4 as [? Hq].
           apply Qle_bool_iff in Hq; congruence.
      * constructor; intro HC; inversion HC; subst.
        destruct H3 as [Hq ?].
        apply Qle_bool_iff in Hq; congruence.
    + rewrite andb_false_r; constructor; intro HC; inversion HC; auto.
    + rewrite andb_false_r; constructor; intro HC; inversion HC; auto.
    + rewrite andb_false_r; constructor; intro HC; inversion HC; auto.
  - destruct IHc; repeat constructor; auto.
    intro HC; inversion HC; auto.
Qed.

(** f is an expectation. *)
Definition expectation {A : Type} (f : A -> Q) := forall x, 0 <= f x.

Definition bounded {A : Type} (f : A -> Q) (b : Q) := forall x, f x <= b.

(** f is a bounded expectation (bounded above by 1). *)
Definition bounded_expectation {A : Type} (f : A -> Q) (b : Q) :=
  forall x, 0 <= f x <= b.

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

Inductive cpGCL_le : cpGCL -> cpGCL -> Prop :=
| le_skip : cpGCL_le CSkip CSkip
| le_abort : forall c, cpGCL_le CAbort c
| le_assign : forall x e, cpGCL_le (CAssign x e) (CAssign x e)
| le_seq : forall c1 c2 c2',
    cpGCL_le c2 c2' ->
    cpGCL_le (CSeq c1 c2) (CSeq c1 c2')
| le_ite: forall e c1 c1' c2 c2',
    cpGCL_le c1 c1' ->
    cpGCL_le c2 c2' ->

    cpGCL_le (CIte e c1 c2) (CIte e c1' c2')
| le_choice: forall p c1 c1' c2 c2',
    cpGCL_le c1 c1' ->
    cpGCL_le c2 c2' ->
    cpGCL_le (CChoice p c1 c2) (CChoice p c1' c2')
| le_while : forall e c,
    cpGCL_le (CWhile e c) (CWhile e c)
| le_observe : forall e,
    cpGCL_le (CObserve e) (CObserve e).

Instance Reflexive_cpGCL_le : Reflexive cpGCL_le.
Proof. intro c; induction c; constructor; auto. Qed.

Instance Transitive_cpGCL_le : Transitive cpGCL_le.
Proof.
  intros c1 c2; revert c1.
  induction c2; intros c1 c3 Hle1 Hle2;
    inversion Hle1; inversion Hle2; subst; auto; constructor;
      try solve[eapply IHc2_1; auto]; eapply IHc2_2; auto.
Qed.

Program Instance OType_cpGCL : OType cpGCL :=
  { leq := cpGCL_le }.
Next Obligation.
  split. apply Reflexive_cpGCL_le. apply Transitive_cpGCL_le.
Qed.
