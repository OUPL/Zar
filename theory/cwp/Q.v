Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.


(** Definitions *)

Definition sum_Q_list (l : list Q) : Q :=
  fold_right Qplus 0 l.

Fixpoint Qpow (x : Q) (n : nat) :=
  match n with
  | O => 1
  | S n' => x * Qpow x n'
  end.

Definition f_Qeq {A : Type} (f g : A -> Q) := forall x, f x == g x.

Notation "f '==f' g" := (f_Qeq f g) (at level 80, no associativity) : Q_scope.
Local Open Scope Q_scope.


(** Lemmas *)

Lemma Qle_Qdiv_1 (x : Q) : x / 1 == x.
Proof. field. Qed.

Lemma Qdiv_0_num (a : Q) : 0 / a == 0.
Proof. destruct a; destruct Qnum; compute; reflexivity. Qed.

Lemma Qdiv_0_den (a : Q) : a / 0 == 0.
Proof. destruct a; destruct Qnum; compute; reflexivity. Qed.

Lemma Qdiv_1_den (a : Q) : a / 1 == a.
Proof. field. Qed.

Lemma Qminus_cancel (a : Q) : a - a == 0.
Proof. field. Qed.

Lemma Qminus_0_r (a : Q) : a - 0 == a.
Proof. field. Qed.

Lemma not_in_sum_Q_list a l:
  ~ In a l ->
  sum_Q_list (map (fun n : nat => if a =? n then 1 else 0) l) = 0.  
Proof.
  induction l; auto; intro Hnotin.
  simpl.
  destruct (Nat.eqb_spec a a0); subst.
  - exfalso; apply Hnotin; constructor; auto.
  - rewrite IHl; auto.
    intro HC; apply Hnotin; right; auto.
Qed.

Lemma sum_Q_list_map_plus {A : Type} (f g : A -> Q) (l : list A) :
  sum_Q_list (map (fun x => f x + g x) l) ==
  sum_Q_list (map f l) + sum_Q_list (map g l).
Proof. induction l; simpl; lra. Qed.

Lemma sum_Q_list_map_mult_scalar {A : Type} (a : Q) (f : A -> Q) (l : list A) :
  sum_Q_list (map (fun x => a * f x) l) ==
  a * sum_Q_list (map f l).
Proof. induction l; simpl; lra. Qed.

Lemma sum_Q_list_map_div_scalar {A : Type} (a : Q) (f : A -> Q) (l : list A) :
  0 < a ->
  sum_Q_list (map (fun x => f x / a) l) ==
  sum_Q_list (map f l) / a.
Proof.
  intro H0; induction l; simpl. field. lra.
  rewrite IHl. field. lra.
Qed.

Lemma Qeq_Qdiv (a b c d : Q) :
  a == c -> b == d -> a / b == c / d.
Proof. intros H0 H1; rewrite H0, H1; reflexivity. Qed.

Lemma Qeq_Qminus (a b c d : Q) :
  a == c -> b == d -> a - b == c - d.
Proof. intros; lra. Qed.

Lemma sum_Q_list_l (f : nat -> Q) (n m : nat) :
  f n + sum_Q_list (map f (seq (S n) m)) ==
  sum_Q_list (map f (seq n (S m))).
Proof. reflexivity. Qed.

Lemma sum_Q_list_r (f : nat -> Q) (n m : nat) :
  sum_Q_list (map f (seq n m)) + f (n + m)%nat ==
  sum_Q_list (map f (seq n (S m))).
Proof.
  revert n. induction m; intro n.
  - simpl. ring_simplify. rewrite plus_comm. reflexivity.
  - simpl in *.
    assert (n + (S m) = S n + m)%nat.
    { lia. }
    rewrite H.
    specialize (IHm (S n)).
    rewrite <- IHm; field.
Qed.

Lemma sum_Q_list_distr {A : Type} (l : list A) (f : A -> Q) (q : Q) :
  q * sum_Q_list (map f l) == sum_Q_list (map (fun x => q * f x) l).
Proof.
  induction l; simpl.
  - field.
  - rewrite <- IHl; field.
Qed.

Lemma sum_Q_list_proper {A : Type} (f g : A -> Q) (l : list A) :
  f ==f g ->
  sum_Q_list (map f l) == sum_Q_list (map g l).
Proof.
  unfold f_Qeq; intros Heq; induction l; simpl; try reflexivity.
  rewrite IHl, Heq; reflexivity.
Qed.

Lemma sum_Q_list_succ f n m :
  sum_Q_list (map f (seq (S m) n)) ==
  sum_Q_list (map (fun i => f (S i)) (seq m n)).
Proof.
  revert m; induction n; intro m; simpl; try rewrite IHn; reflexivity.
Qed.

Lemma sum_Q_list_Qpow a r n m :
  sum_Q_list (map (fun x : nat => r * (a * Qpow r x)) (seq m n)) ==
  sum_Q_list (map (fun x : nat => a * Qpow r x) (seq (S m) n)).
Proof.
  rewrite sum_Q_list_succ; apply sum_Q_list_proper;
    intros; simpl; intros ?; field.
Qed.

Lemma Qeq_respects_eq {A : Type} (f : A -> Q) (x y : A) :
  x = y ->
  f x == f y.
Proof. intro; subst; reflexivity. Qed.

Instance f_Qeq_Reflexive {A : Type} : Reflexive (@f_Qeq A).
Proof. intros ? ?; reflexivity. Qed.

Lemma f_Qeq_refl {A : Type} (f : A -> Q) :
  f ==f f.
Proof. intros ?; apply Qeq_refl. Qed.

Lemma f_Qeq_trans {A : Type} (f g h : A -> Q) :
  f ==f g -> g ==f h -> f ==f h.
Proof. unfold f_Qeq; intros Hfg Hgh ?; rewrite Hfg; apply Hgh. Qed.

Lemma f_Qeq_symm {A : Type} (f g : A -> Q) :
  f ==f g -> g ==f f.
Proof. unfold f_Qeq; intros Hfg ?; rewrite Hfg; apply Qeq_refl. Qed.

Lemma Qabs_Qminus_Qle a b :
  b <= a -> Qabs (a - b) == a - b.
Proof. intros; apply Qabs_case; lra. Qed.

Lemma Qpow_nonnegative a n :
  0 <= a ->
  0 <= Qpow a n.
Proof. intros; induction n; simpl; nra. Qed.

Instance Proper_Qpow : Proper (Qeq ==> eq ==> Qeq) Qpow.
Proof.
  intros x y Heq1 n m Heq2; subst.
  induction m; simpl.
  - reflexivity.
  - rewrite IHm, Heq1; reflexivity.
Qed.
Lemma Qlem_1 a b c :
  ~ c == 0 -> a / c == b -> a == b * c.
Proof.
  intros H0 H1; apply (Qmult_inj_l _ _ _ H0) in H1.
  rewrite Qmult_div_r in H1; auto; lra.
Qed.

Lemma Qlem_2 a b :
  a / (1 - b) == 1 -> a + b == 1.
Proof.
  intro H0.
  destruct (Qeq_dec b 1).
  - rewrite q in H0.
    rewrite Qminus_cancel, Qdiv_0_den in H0. inversion H0.
  - apply Qlem_1 in H0; lra.
Qed.

Lemma sum_Q_list_map_const_0 {A : Type} (l : list A) :
  sum_Q_list (map (const 0) l) == 0.
Proof.
  unfold const. induction l; simpl; try rewrite IHl; reflexivity.
Qed.

Lemma convex_l (p x y : Q) :
  0 < p -> p < 1 ->
  0 <= x <= 1 ->
  0 <= y <= 1 ->
  p * x + (1 - p) * y == 1 ->
  x == 1.
Proof. intros. nra. Qed.

Lemma convex_r (p x y : Q) :
  0 < p -> p < 1 ->
  0 <= x <= 1 ->
  0 <= y <= 1 ->
  p * x + (1 - p) * y == 1 ->
  y == 1.
Proof. intros. nra. Qed.

Lemma sum_Q_list_nonnegative l :
  (forall x, In x l -> 0 <= x) ->
  0 <= sum_Q_list l.
Proof.
  induction l; intro Hle; simpl.
  - lra.
  - assert (0 <= sum_Q_list l).
    { apply IHl; intros x Hin; apply Hle; right; auto. }
    specialize (Hle a (in_eq _ _)); lra.
Qed.
