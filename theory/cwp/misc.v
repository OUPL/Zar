Set Implicit Arguments.

Require Import PeanoNat.
Require Import List.
Require Import Coq.micromega.Lia.

Require Import order.

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
