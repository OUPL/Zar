Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Local Open Scope program_scope.

Require Import Q.


(* Types with decidable equality *)
Class EqType (A : Type) : Type :=
  { eqb : A -> A -> bool
  ; eqb_spec : forall x y, reflect (x = y) (eqb x y)
  }.

Instance EqType_bool : EqType bool :=
  {| eqb := Bool.eqb
   ; eqb_spec := Bool.eqb_spec |}.

Instance EqType_nat : EqType nat :=
  {| eqb := Nat.eqb
   ; eqb_spec := Nat.eqb_spec |}.


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
Qed.

Program Instance OType_nat : OType nat := {| leq := Nat.le |}.

Program Instance OType_list A : OType (list A) :=
  {| leq := fun l1 l2 => forall x, In x l1 -> In x l2 |}.
Next Obligation. split; auto. Qed.

Program Instance OType_Q : OType Q :=
  { leq := Qle }.
Next Obligation. Admitted.

Program Instance PType_arrow A B `{p : PType B} : PType (A -> B) :=
  {| bot := const bot |}.
Next Obligation. destruct p as [? H]; apply H. Qed.

Definition equ {A : Type} `{OType A} (x y : A) :=
  leq x y /\ leq y x.

(** f is an ω-chain *)
Definition chain {A : Type} `{o : OType A} (f : nat -> A) : Prop :=
  forall i, leq (f i) (f (S i)).

(** Apply all functions in a chain to the same argument x. *)
Definition app_chain {A : Type} (ch : nat -> A -> Q) (x : A) : nat -> Q :=
  flip ch x.

Definition cons_chain {A : Type} (x : A) (ch : nat -> A) : nat -> A :=
  fun i => match i with
        | O => x
        | S i' => ch i'
        end.

Definition lower_bound {A B : Type} `{OType B} (x : B) (f : A -> B) :=
  forall y, leq x (f y).

Definition upper_bound {A B : Type} `{OType B} (x : B) (f : A -> B) :=
  forall y, leq (f y) x.

Definition infimum {A B : Type} `{OType B} (inf : B) (f : A -> B) :=
  lower_bound inf f /\ forall x, lower_bound x f -> leq x inf.

Definition supremum {A B : Type} `{OType B} (sup : B) (f : A -> B) :=
  upper_bound sup f /\ forall x, upper_bound x f -> leq sup x.

Lemma infimum_unique {A B : Type} `{o : OType B} (x y : B) (f : A -> B) :
  infimum x f -> infimum y f -> equ x y.
Proof.
  intros [H0 H1] [H2 H3]; split.
  - apply H3; auto.
  - apply H1; auto.
Qed.

Lemma supremum_unique {A B : Type} `{o : OType B} (x y : B) (f : A -> B) :
  supremum x f -> supremum y f -> equ x y.
Proof.
  intros [H0 H1] [H2 H3]; split.
  - apply H1; auto.
  - apply H3; auto.
Qed.

Lemma equ_supremum {A B : Type} `{o : OType B} (x y : B) (f : A -> B) :
  equ x y -> supremum x f -> supremum y f.
Proof.
  intros [H0 H1] [H2 H3]; split; intro z.
  - destruct o as [? [? Htrans]].
    eapply Htrans. apply H2. apply H0.
  - intro Hupper.
    apply H3 in Hupper.
    destruct o as [? [? Htrans]].
    eapply Htrans; eauto.
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

Lemma const_infimum {A : Type} {o : OType A} (f : nat -> A) (x : A) :
  (forall i, equ (f i) x) -> infimum x f.
Admitted.

Lemma const_supremum {A : Type} {o : OType A} (f : nat -> A) (x : A) :
  (forall i, equ (f i) x) -> supremum x f.
Admitted.

Lemma const_supremum' {A : Type} `{o : OType A} (f : nat -> A) (x : A) :
  (exists n0, forall n, (n0 <= n)%nat -> leq (f O) (f n0) /\ equ (f n) x) ->
  supremum x f.
Admitted.

(* x is a fixed point of f *)
Definition fixed_point {A : Type} (x : A) (f : A -> A) :=
  f x = x.

(* x is the least fixed point of f *)
Definition lfp {A : Type} `{OType A} (x : A) (f : A -> A) :=
  fixed_point x f /\ (forall y, fixed_point y f -> leq x y).

Lemma Qeq_equ (x y : Q) :
  x == y <-> equ x y.
Proof.
  split; intro H.
  - split; rewrite H; apply Qle_refl.
  - apply Qle_antisym; apply H.
Qed.

Lemma f_Qeq_equ {A : Type} (f g : A -> Q) :
  f ==f g <-> equ f g.
Proof.
  split; intro H.
  - split; intro x; specialize (H x);
      apply Qeq_equ; rewrite H; apply Qeq_refl.
  - intro x; apply Qeq_equ; split; apply H.
Qed.


Definition converges (g : nat -> Q) (lim : Q) :=
  forall eps,
    0 < eps ->
    exists n0, forall n,
        (n0 <= n)%nat -> Qabs (lim - g n) < eps.

Lemma converges_increasing_ub (g : nat -> Q) (lim : Q) :
  (forall i, g i <= g (S i)) ->
  converges g lim ->
  upper_bound lim g.
Proof.
  unfold converges.
  intros Hle Hc n; simpl.
  destruct (Qlt_le_dec lim (g n)); auto.
  set (eps := g n - lim).
  assert (0 < eps).
  { unfold eps; lra. }
  specialize (Hc eps H); destruct Hc as [n0 Hc].
  specialize (Hc (max n n0) (Nat.le_max_r _ _)).
  rewrite Qabs_Qminus in Hc.
  assert (H0: forall m, (n <= m)%nat -> g n <= g m).
  { intros m Hle'; induction m.
    - inversion Hle'; lra.
    - destruct (Nat.eqb_spec n (S m)); subst.
      + lra.
      + assert (n <= m)%nat. lia.
        apply IHm in H0; eapply Qle_trans; eauto. }
  assert (H1: g n <= g (max n n0)).
  { apply H0. apply Nat.le_max_l. }
  rewrite Qabs_Qminus_Qle in Hc.
  - unfold eps in Hc; lra.
  - lra.
Qed.

Lemma converges_increasing_le_ub (g : nat -> Q) (lim : Q) :
  converges g lim ->
  forall ub, upper_bound ub g -> lim <= ub.
Proof.
  unfold upper_bound; simpl; unfold converges.
  intros Hc ub Hub; destruct (Qlt_le_dec ub lim); auto.
  set (eps := lim - ub).
  assert (Heps: 0 < eps).
  { unfold eps; lra. }
  specialize (Hc eps Heps); destruct Hc as [n0 Hc].
  specialize (Hc n0 (le_refl _)); specialize (Hub n0).
  unfold eps in Hc; rewrite Qabs_Qminus_Qle in Hc; lra.
Qed.

(* If g is monotonically increasing and converges to lim, then lim is
   the supremum of g. *)
Lemma converges_from_below_supremum (g : nat -> Q) (lim : Q) :
  (forall i, g i <= g (S i)) ->
  converges g lim ->
  supremum lim g.
Proof.
  unfold converges.
  intros Hc. split.
  - apply converges_increasing_ub; auto.
  - apply converges_increasing_le_ub; auto.
Qed.

Lemma Proper_converges : Proper (f_Qeq ==> Qeq ==> iff) converges.
Proof.
  intros f g Heq1 x y Heq2.
  unfold converges.
  split; intros Hc eps Heps.
  - destruct (Hc eps Heps) as [n0 Hc'].
    exists n0; intros n Hle; apply Hc' in Hle; rewrite <- Heq2.
    specialize (Heq1 n); rewrite <- Heq1; auto.
  - destruct (Hc eps Heps) as [n0 Hc'].
    exists n0; intros n Hle; apply Hc' in Hle; rewrite Heq2.
    specialize (Heq1 n); rewrite Heq1; auto.
Qed.

(** Not an actual Proper instance because it can be defined more
    generally. Although I guess it doesn't matter. *)
Lemma Proper_supremum_Q : Proper (Qeq ==> @f_Qeq nat ==> iff) supremum.
Proof.
  unfold f_Qeq. intros x y Heq1 f g Heq2. unfold supremum, upper_bound, leq; simpl.
  split; intros [Hub Hlub].
  - split.
    + intro z; rewrite <- Heq1, <- Heq2; auto.
    + intros z Hle; rewrite <- Heq1; apply Hlub; intro w; rewrite Heq2; auto.
  - split.
    + intro z; rewrite Heq1, Heq2; auto.
    + intros z Hle; rewrite Heq1; apply Hlub; intro w; rewrite <- Heq2; auto.
Qed.

(** Given a function f and a chain of functions g, f is the supremum
    of g if forall x, f x is the supremum of g specialized to x. *)
Lemma supremum_pointwise {A : Type} (ch : nat -> A -> Q) (f : A -> Q) :
  (forall x, supremum (f x) (app_chain ch x)) ->
  supremum f ch.
Proof.
  intro Hsup; split.
  - intros ? ?; apply Hsup.
  - intros ? Hub ?; apply Hsup; intros ?; apply Hub.
Qed.

Lemma cons_chain_supremum {A : Type} `{OType A} (x : A) (ch : nat -> A) (sup : A) :
  (forall i, leq x (ch i)) ->
  supremum sup ch ->
  supremum sup (cons_chain x ch).
Proof.
  unfold supremum, upper_bound.
  intros Hleq [Hub Hlub]; split.
  - intro y. destruct y; simpl; auto.
    destruct H as [le [Hrefl Htrans]].
    eapply Htrans. apply (Hleq O). apply Hub.
  - intros ub Hub'. apply Hlub; intro z.
    specialize (Hub' (S z)); apply Hub'.
Qed.
