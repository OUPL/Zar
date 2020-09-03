(** Miscellaneous definitions and lemmas that don't fit anywhere else. *)

Set Implicit Arguments.
Require Import PeanoNat.
Require Import List.
Require Import Coq.micromega.Lia.
Require Import Permutation.
Import ListNotations.

Require Import order.

Definition tuple (A B C : Type) (f : A -> B) (g : A -> C) (x : A) : B*C :=
  (f x, g x).

Definition cotuple {A B C : Type} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition list_max (l : list nat) : nat := fold_right max O l.

Lemma list_max_spec (l : list nat) (x : nat) :
  In x l ->
  (x <= list_max l)%nat.
Proof.
  induction l; intro Hin.
  - inversion Hin.
  - destruct Hin as [H|H]; subst; simpl.
    + apply Nat.le_max_l.
    + etransitivity. apply IHl; auto.
      apply Nat.le_max_r.
Qed.

Lemma list_max_monotone : monotone (list_max).
Proof.
  intros l1 l2; unfold leq; simpl; intro Hleq; unfold Nat.le.
  induction l1; simpl.
  - lia.
  - destruct (Nat.leb_spec a (list_max l1)).
    + rewrite max_r; auto; apply IHl1.
      intros x Hin. apply Hleq. right; auto.
    + rewrite max_l.
      * apply list_max_spec; apply Hleq; left; auto.
      * lia.
Qed.

Lemma NoDup_app {A : Type} (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  NoDup l1.
Proof.
  induction l1; simpl; intro Hnodup.
  - constructor.
  - inversion Hnodup; subst.
    constructor.
    + intro HC. apply H1. apply in_or_app; intuition.
    + apply IHl1; auto.
Qed.

Lemma NoDup_app_comm {A : Type} (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
Proof.
  intro Hnodup.
  apply Permutation_NoDup with (l := l1 ++ l2); auto.
  apply Permutation_app_comm.
Qed.

Lemma seq_cons a b :
  (0 < b)%nat ->
  seq a b = a :: seq (S a) (b-1).
Proof.
  destruct b; simpl; try lia.
  simpl; rewrite Nat.sub_0_r; reflexivity.
Qed.  

Lemma seq_S_n n :
  seq 0 (S n) = seq 0 n ++ [n].
Proof.
  assert (H: (S n = n + 1)%nat).
  { lia. }
  rewrite H.
  apply seq_app.
Qed.

Lemma app_cons_assoc {A : Type} (x : A) (l1 l2 : list A) :
  l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof. rewrite <- app_assoc; reflexivity. Qed.

Lemma seq_app_S b c :
  (0 < c)%nat ->
  seq 0 b ++ seq b c = seq 0 (S b) ++ seq (S b) (c-1).
Proof.
  intro Hlt.
  assert (H: seq b c = b :: seq (S b) (c - 1)).
  { apply seq_cons; auto. }
  rewrite H; clear H. simpl.
  rewrite app_cons_assoc.
  rewrite <- seq_S_n.
  reflexivity.
Qed.

Lemma seq_app' (a b : nat) :
  (a <= b)%nat ->
  seq 0 b = seq 0 a ++ seq a (b-a).
Proof.
  intro Hle.
  assert (H: (b = a + (b - a))%nat).
  { lia. }
  rewrite H at 1.
  apply seq_app.
Qed.

Lemma const_map_repeat {A B : Type} (f : A -> B) (l : list A) (y : B) :
  (forall x, In x l -> f x = y) ->
  map f l = repeat y (length l).
Proof.
  induction l; simpl; intro Hin; auto.
  rewrite Hin, IHl; auto.
Qed.

Lemma nodup_not_equal {A : Type} (x y : A) (l : list A) :
  NoDup (x :: y :: l) ->
  x <> y.
Proof.
  intro Hnodup; inversion Hnodup; subst.
  intro HC; subst; apply H1; left; auto.
Qed.
