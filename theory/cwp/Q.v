(** Things pertaining to rational numbers. *)

Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope program_scope.


(** Definitions *)

Definition sum_Q_list (l : list Q) : Q :=
  fold_right Qplus 0 l.

Definition sum_Q_list' (l : list Q) : Q :=
  fold_right (compose Qred ∘ Qplus) 0 l.

Fixpoint Qpow (x : Q) (n : nat) :=
  match n with
  | O => 1
  | S n' => x * Qpow x n'
  end.

(* Definition f_Qeq {A : Type} (f g : A -> Q) := forall x, f x == g x. *)
(* Notation "f '==f' g" := (f_Qeq f g) (at level 80, no associativity) : Q_scope. *)
(* Local Open Scope Q_scope. *)

Definition f_Qeq {A : Type} (f g : A -> Q) := forall x, f x == g x.
Notation "f '==f' g" := (forall x, f x == g x) (at level 80, no associativity) : Q_scope.
Local Open Scope Q_scope.

Fixpoint first_n {A : Type} (f : nat -> A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => first_n f n' ++ [f n']
  end.

Definition partial_sum (f : nat -> Q) (n : nat) : Q :=
  sum_Q_list (first_n f (S n)).

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

Lemma Qle_Qdiv (a b c : Q) :
  a <= b -> 0 <= c -> a / c <= b / c.
Proof.
  intros H0 H1.
  destruct (Qeq_dec c 0).
  - rewrite q; rewrite 2!Qdiv_0_den; lra.
  - apply Qle_shift_div_l. lra. 
    assert (a / c * c == a).
    { field; auto. }
    rewrite H; auto.
Qed.

Lemma Qle_Qdiv' (a b c : Q) :
  0 < c -> a / c <= b / c -> a <= b.
Proof.
  intros H0 H1.
  assert (a / c * c <= b / c * c).
  { nra. }
  assert (a / c * c == a).
  { field; auto. lra. }
  assert (b / c * c == b).
  { field; auto. lra. }
  lra.
Qed.

Lemma Qlt_Qdiv (a b c : Q) :
  a < b -> 0 < c -> a / c < b / c.
Proof.
  intros H0 H1.
  apply Qlt_shift_div_l; auto.
  assert (a / c * c == a).
  { field; lra. }
  rewrite H; auto.
Qed.

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
    intros; simpl; field.
Qed.

Lemma Qeq_respects_eq {A : Type} (f : A -> Q) (x y : A) :
  x = y ->
  f x == f y.
Proof. intro; subst; reflexivity. Qed.

Instance f_Qeq_Reflexive {A : Type} : Reflexive (@f_Qeq A).
Proof. intros ? ?; reflexivity. Qed.

Instance f_Qeq_Symmetric {A : Type} : Symmetric (@f_Qeq A).
Proof. intros f g Hfg x; symmetry; auto. Qed.

Instance f_Qeq_Transitive {A : Type} : Transitive (@f_Qeq A).
Proof. intros f g h Hfg Hgh x; etransitivity; eauto. Qed.

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

Lemma sum_Q_list_app (l1 l2 : list Q) :
  sum_Q_list (l1 ++ l2) == sum_Q_list l1 + sum_Q_list l2.
Proof.
  unfold sum_Q_list; rewrite fold_right_app; induction l1; simpl; lra.
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

Lemma Qeq_bool_false a b :
  ~ a == b ->
  Qeq_bool a b = false.
Proof.
  intros Hneq; destruct (Qeq_bool a b) eqn: H; auto.
  exfalso; apply Hneq; apply Qeq_bool_iff; auto.
Qed.

Lemma Qlt_Qplus_Qdiv2 a b c :
  a < c/(2#1) ->
  b < c/(2#1) ->
  a + b < c.
Proof.
  intros Ha Hb.
  assert (c == c/(2#1) + c/(2#1)).
  { field. }
  rewrite H; lra.
Qed.

Lemma ratio_Qle_sum a b c :
  b < 1 ->
  a / (1 - b) <= c <-> a + b * c <= c.
Proof.
  intro H0; split; intro H1.
  - cut (a <= c - b * c).
    { lra. }
    cut (a <= c * (1 - b)).
    { lra. }
    cut (a / (1-b) <= c * (1-b) / (1-b)).
    { intro H2. apply Qle_Qdiv' in H2; lra. }
    apply Qle_shift_div_l. lra.
    apply Qmult_le_compat_r; auto; lra.
  - apply Qle_shift_div_r; lra.
Qed.

(** Misc lemmas *)

Lemma Q_lem1 a b c d :
  (a#c) * (b#d) = (a*b#c*d).
Proof. reflexivity. Qed.

Lemma Q_lem2 a b c :
  (a#c) + (b#c) == (a+b#c).
Proof.
  rewrite 3!Qmake_Qdiv.
  rewrite inject_Z_plus. field.
  intros HC; inversion HC.
Qed.

Lemma Q_lem3 (a b c : nat) :
  (c <> 0)%nat ->
  (1 # 2) * (Z.of_nat a # Pos.of_nat c) +
  (1 # 2) * (Z.of_nat b # Pos.of_nat c) ==
  Z.of_nat (a + b) # Pos.of_nat (c + c).
Proof.
  intro H0.
  rewrite 2!Q_lem1.
  rewrite 2!Z.mul_1_l.
  rewrite Nat2Z.inj_add.
  assert (H1: (c + c = 2 * c)%nat). lia.
  rewrite H1. clear H1.
  rewrite Nat2Pos.inj_mul; auto.
  apply Q_lem2.
Qed.

Lemma Q_lem4 (a b c : Q) :
  0 < b -> 0 < c ->
  (a / c) / (b / c) == a / b.
Proof. intros H0 H1; field; split; nra. Qed.

Lemma Qdiv_Qmake (a b : Z) (c d : positive) :
  (0 < b)%Z ->
  (a # c) / (b # d) == (a * Zpos d # Z.to_pos b * c).
Proof. intro Hlt; unfold Qeq; destruct b; simpl; lia. Qed.

Lemma Q_lem5 (a : Z) (b : nat) (c : positive) :
  (0 < b)%nat ->
  (a # c) / (Z.of_nat b # c) == a # Pos.of_nat b.
Proof.
  intro H0.
  rewrite 3!Qmake_Qdiv.
  rewrite Q_lem4.
  - cut (inject_Z (Z.of_nat b) == inject_Z (Z.pos (Pos.of_nat b))).
    { intro H1. rewrite H1. reflexivity. }
    cut (Z.pos (Pos.of_nat b) = Z.of_nat b).
    { intro H. rewrite H. reflexivity. }
    clear c. clear a.
    assert (H: b = Pos.to_nat (Pos.of_nat b)).
    { rewrite Nat2Pos.id; lia. }
    rewrite H at 2.
    rewrite positive_nat_Z; reflexivity.
  - assert (H: 0 == inject_Z 0).
    { reflexivity. }
    rewrite H, <- Zlt_Qlt; lia.
  - assert (H: 0 == inject_Z 0).
    { reflexivity. }
    rewrite H, <- Zlt_Qlt; lia.
Qed.

Lemma Q_lem6 a b :
  1 - (a # b) == Zpos b - a # b.
Proof.
  unfold Qeq; destruct a; simpl.
  - reflexivity.
  - rewrite Pos.mul_1_r; reflexivity.
  - lia.
Qed.

Lemma Z_pos_of_nat (n : nat) :
  (0 < n)%nat ->
  Z.pos (Pos.of_nat n) = Z.of_nat n.
Proof.
  intro Hlt.
  unfold Z.of_nat.
  destruct n. lia.
  rewrite Pos.of_nat_succ; reflexivity.
Qed.

Lemma Z_to_pos_of_nat (n : nat) :
  Z.to_pos (Z.of_nat n) = Pos.of_nat n.
Proof.
  unfold Pos.of_nat.
  destruct n. reflexivity.
  simpl.
  induction n. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma Qmake_1 (n : nat) :
  (1 <= n)%nat ->
  Z.of_nat n # Pos.of_nat n == 1.
Proof.
  intro Hle.
  unfold Qeq. simpl.
  rewrite Z.mul_1_r.
  rewrite Z_pos_of_nat; auto.
Qed.

Lemma Q_neq_0 (z : Z) :
  z <> Z0 ->
  ~ (z # 1) == 0.
Proof. intros Hz HC; inversion HC; lia. Qed.

Lemma sum_Q_list_repeat_0 (n : nat) :
  sum_Q_list (repeat 0 n) == 0.
Proof. induction n; simpl; lra. Qed.
