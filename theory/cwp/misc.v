(** Miscellaneous definitions and lemmas that don't fit anywhere else. *)

Set Implicit Arguments.
Require Import PeanoNat.
Require Import Nat.
Require Import List.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith.
Require Import Permutation.
Require Import ExtLib.Structures.Monoid.

From ITree Require Import ITree.
From Paco Require Import paco.

Import ListNotations.

Ltac destruct_upaco :=
  match goal with
  | [ H: context[upaco1 _ bot1 _] |- _] =>
    destruct H as [H | H]; try solve[inversion H]
  | [ H: context[upaco2 _ bot2 _ _] |- _] =>
    destruct H as [H | H]; try solve[inversion H]
  end.

Lemma _observe_observe {A : Type} {E : Type -> Type} (t : itree E A) :
  _observe t = observe t.
Proof. reflexivity. Qed.

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

Inductive is_prefix {A : Type} : list A -> list A -> Prop :=
| is_prefix_nil : forall l2,
    is_prefix nil l2
| is_prefix_cons : forall x l1 l2,
    is_prefix l1 l2 ->
    is_prefix (x :: l1) (x :: l2).

Instance Reflexive_is_prefix {A : Type} : Reflexive (@is_prefix A).
Proof. intro x; induction x; constructor; auto. Qed.

Instance Transitive_is_prefix {A : Type} : Transitive (@is_prefix A).
Proof.
  intros xs ys zs.
  revert xs zs.
  induction ys; intros xs zs H0 H1.
  - inversion H0; subst; constructor.
  - inversion H0; subst.
    + constructor.
    + inversion H1; subst.
      constructor; apply IHys; auto.
Qed.

Fixpoint prefix {A : Type} (f : nat -> A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => prefix f n' ++ [f n']
  end.

Fixpoint prefix_aux {A : Type} (f : nat -> A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => f n' :: prefix_aux f n'
  end.

Definition prefix' {A : Type} (f : nat -> A) (n : nat) : list A :=
  rev (prefix_aux f n).

Lemma prefix_prefix' {A : Type} (f : nat -> A) (n : nat) :
  prefix f n = prefix' f n.
Proof.
  unfold prefix'.
  induction n; auto; simpl.
  rewrite IHn; auto.
Qed.

Definition drop {A : Type} (f : nat -> A) (n : nat) : nat -> A :=
  fun i => f (i + n)%nat.

Definition slice {A : Type} (f : nat -> A) (n m : nat) : list A :=
  prefix (drop f n) m.

Definition slice' {A : Type} (f : nat -> A) (n m : nat) : list A :=
  match n with
  | O => prefix f m
  | S n' => prefix (fun i => f (S i)) m
  end.

Lemma length_prefix {A : Type} (f : nat -> A) (n : nat) :
  length (prefix f n) = n.
Proof.
  induction n; simpl; auto.
  rewrite app_length; simpl; lia.
Qed.

Lemma drop_O {A : Type} (f : nat -> A) :
  forall i, drop f O i = f i.
Proof. intro i; unfold drop; rewrite plus_0_r; reflexivity. Qed.

Definition ext {A B : Type} (f g : A -> B) : Prop :=
  forall x, f x = g x.

Lemma Proper_prefix {A : Type} : Proper (@ext nat A ==> eq ==> eq) prefix.
Proof.
  intros f g Hext ? n ?; subst.
  induction n; simpl; auto.
  rewrite IHn, Hext; reflexivity.
Qed.

Lemma slice_O {A : Type} (f : nat -> A) (n : nat) :
  slice f O n = prefix f n.
Proof. apply Proper_prefix; auto; intro i; apply drop_O. Qed.

Lemma is_prefix_app {A : Type} (l1 l2 : list A) :
  is_prefix l1 (l1 ++ l2).
Proof. induction l1; constructor; auto. Qed.

Lemma prefix_is_prefix {A : Type} (f : nat -> A) (n m : nat) :
  (n <= m)%nat ->
  is_prefix (prefix f n) (prefix f m).
Proof.
  revert n. induction m; simpl; intros n Hle.
  - assert (n = O). lia. subst. constructor.
  - destruct (Nat.eqb_spec n (S m)); subst.
    + reflexivity.
    + assert (H: (n <= m)%nat).
      { lia. }
      apply IHm in H.
      etransitivity; eauto.
      apply is_prefix_app.
Qed.

Lemma is_prefix_exists {A : Type} (l1 l2 : list A) :
  is_prefix l1 l2 <-> exists l, l1 ++ l = l2.
Proof.
  split; intro H.
  - induction H.
    + exists l2; reflexivity.
    + destruct IHis_prefix as [l IH]; subst.
      exists l; reflexivity.
  - destruct H as [l ?]; subst; apply is_prefix_app.
Qed.

Inductive list_rel {A B : Type} (R : A -> B -> Prop) : list A -> list B -> Prop :=
| list_rel_nil : list_rel R [] []
| list_rel_cons : forall x y xs ys,
    R x y ->
    list_rel R xs ys ->
    list_rel R (x :: xs) (y :: ys).

Lemma list_rel_app {A B : Type}
      (R : A -> B -> Prop) (l1 l2 : list A) (l3 l4 : list B) :
  list_rel R l1 l3 /\ list_rel R l2 l4 -> list_rel R (l1 ++ l2) (l3 ++ l4).
Proof.
  revert l2 l3 l4.
  induction l1; intros l2 l3 l4 [H0 H1];
    inversion H0; subst; simpl; try constructor; auto.
Qed.

Lemma list_rel_prefix {A B : Type}
      (f : nat -> A) (g : nat -> B) (R : A -> B -> Prop) (n : nat) :
  (forall i, R (f i) (g i)) ->
  list_rel R (prefix f n) (prefix g n).
Proof.
  induction n; intro Hrel; simpl.
  - constructor.
  - apply list_rel_app; split; auto.
    constructor; auto; constructor.
Qed.

Instance Reflexive_list_rel {A : Type} (R : A -> A -> Prop) `{Reflexive A R}
  : Reflexive (list_rel R).
Proof.
  intro l; induction l; constructor; auto.
Qed.

Instance Symmetric_list_rel {A : Type} (R : A -> A -> Prop) `{Symmetric A R}
  : Symmetric (list_rel R).
Proof.
  intros l1 l2 Hrel; induction Hrel; constructor; auto.
Qed.

Instance Transitive_list_rel {A : Type} (R : A -> A -> Prop) `{Transitive A R}
  : Transitive (list_rel R).
Proof.
  intros l1 l2; revert l1; induction l2; intros l1 l3 Hrel12 Hrel23;
    inversion Hrel12; inversion Hrel23; subst;
      constructor; auto; etransitivity; eauto.
Qed.

(** Only requires the relation to be reflexive for elements appearing
    in the list. *)
Lemma list_rel_reflexive {A : Type} (l : list A) (R : A -> A -> Prop) :
  (forall x, In x l -> R x x) ->
  list_rel R l l.
Proof. induction l; simpl; intro Hrefl; constructor; auto. Qed.

Fixpoint first_n {A : Type} (f : nat -> A) (n : nat) : list A :=
  match n with
  | O => []
  | S n' => first_n f n' ++ [f n']
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => range n' ++ [n']
  end.

Lemma range_seq (n : nat) :
  range n = seq 0 n.
Proof.
  induction n; auto; rewrite seq_S; simpl; rewrite IHn; reflexivity.
Qed.

Definition first_n' {A : Type} (f : nat -> A) (n : nat) : list A :=
  map f (range n).

Lemma first_n_first_n' {A : Type} (f : nat -> A) (n : nat) :
  first_n f n = first_n' f n.
Proof.
  induction n; unfold first_n'; simpl; auto.
  rewrite IHn. unfold first_n'.
  rewrite map_app; reflexivity.
Qed.

Lemma NoDup_range (n : nat) :
  NoDup (range n).
Proof. rewrite range_seq; apply seq_NoDup. Qed.

Lemma is_prefix_map {A B : Type} (l1 l2 : list A) (f : A -> B) :
  is_prefix l1 l2 ->
  is_prefix (map f l1) (map f l2).
Proof. induction 1; constructor; auto. Qed.

Lemma is_prefix_range (n m : nat) :
  (n <= m)%nat ->
  is_prefix (range n) (range m).
Proof.
  induction 1.
  - reflexivity.
  - etransitivity; eauto; apply is_prefix_app. 
Qed.

Lemma is_prefix_first_n {A : Type} (f : nat -> A) (n m : nat) :
  (n <= m)%nat ->
  is_prefix (first_n f n) (first_n f m).
Proof.
  rewrite 2!first_n_first_n'.
  intro Hle. apply is_prefix_map.
  apply is_prefix_range; auto.
Qed.

Lemma in_first_n {A : Type} (s : nat -> A) (x : A) (n : nat) :
  In x (first_n s n) ->
  exists i, (i <= n)%nat /\ s i = x.
Proof.
  induction n; simpl; intros Hin; try contradiction.
  apply in_app_or in Hin; destruct Hin.
  - destruct (IHn H) as [i [Hle Heq]].
    exists i; split; auto.
  - destruct H; try contradiction; subst.
    exists n; split; auto.
Qed.

Lemma fst_divmod (n : nat) :
  fst (divmod n 1 0 1) = (n / 2)%nat.
Proof. reflexivity. Qed.

Lemma mod_2_dec (n : nat) :
  n mod 2 = 0%nat \/ n mod 2 = 1%nat.
Proof.
  assert (n mod 2 < 2)%nat.
  { apply Nat.mod_upper_bound; auto. }
  lia.
Qed.

Lemma mod_2_succ (n : nat) :
  n mod 2 = 0%nat -> (S n) mod 2 = 1%nat.
Proof.
  intro H0; simpl in *.
  generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  generalize (Nat.divmod_spec n 1 0 0 (Nat.le_0_l _)).
  intro H2; destruct (Nat.divmod n 1 0 0); destruct H2 as [H2 H3].
  simpl in *; destruct n3; lia.
Qed.

Lemma mod_2_pred (n : nat) :
  n mod 2 = 1%nat -> (pred n) mod 2 = 0%nat.
Proof.
  intro H0; simpl in *.
  generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  generalize (Nat.divmod_spec (pred n) 1 0 1 (Nat.le_refl _)).
  intro H2; destruct (Nat.divmod (pred n) 1 0 1); destruct H2 as [H2 H3].
  simpl in *; destruct n3; lia.
Qed.

Lemma mod_2_nonzero (n : nat) :
  n mod 2 = 1%nat -> (0 < n)%nat.
Proof.
  intro H0; simpl in *.
  generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  simpl in *; lia.
Qed.

Lemma mod_2_div_succ (n : nat) :
  n mod 2 = 0%nat -> (n / 2)%nat = (S n / 2)%nat.
Proof.
  intro H0; simpl in *.
  generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  generalize (Nat.divmod_spec n 1 0 0 (Nat.le_0_l _)).
  intro H2; destruct (Nat.divmod n 1 0 0); destruct H2 as [H2 H3].
  simpl in *; destruct n1, n3; lia.
Qed.

Lemma mod_2_div_pred (n : nat) :
  n mod 2 = 1%nat -> (n / 2)%nat = (pred n / 2)%nat.
Proof.
  intro H0; simpl in *.
  generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  generalize (Nat.divmod_spec (pred n) 1 0 1 (Nat.le_refl _)).
  intro H2; destruct (Nat.divmod (pred n) 1 0 1); destruct H2 as [H2 H3].
  simpl in *; destruct n1, n3; lia.
Qed.

Lemma mod_n_div (n : nat) :
  n mod 2 = 0%nat ->
  (2 * (n / 2))%nat = n.
Proof.
  simpl; generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  simpl in *; destruct n1; lia.
Qed.

Lemma mod_n_div_plus_1 (n : nat) :
  n mod 2 = 1%nat ->
  (2 * (n / 2) + 1)%nat = n.
Proof.
  simpl; generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  simpl in *; destruct n1; lia.
Qed.

Lemma mod_2_div_mul_pred (n : nat) :
  n mod 2 = 1%nat ->
  (n / 2 * 2)%nat = pred n.
Proof.
  simpl; generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  simpl in *; destruct n1; lia.
Qed.

Lemma mod_2_S_O (i n : nat) :
  i mod 2 = S n -> n = O.
Proof. intro Hmod; destruct (mod_2_dec i); congruence. Qed.

Lemma mod_2_S_O' (i n : nat) :
  i mod 2 = S n -> i mod 2 = 1%nat.
Proof. intro Hmod; destruct (mod_2_dec i); congruence. Qed.

Lemma existsb_in (n : nat) (ns : list nat) :
  existsb (Nat.eqb n) ns = true <-> In n ns.
Proof.
  split; intro H.
  - induction ns.
    + unfold existsb in H; congruence.
    + simpl in *; apply orb_prop in H; destruct H.
      * apply Nat.eqb_eq in H; left; auto.
      * right; apply IHns; auto.
  - induction ns.
    + inversion H.
    + destruct H; subst; simpl.
      * rewrite Nat.eqb_refl; reflexivity.
      * rewrite IHns; auto; apply orb_true_r.
Qed.

Lemma existsb_not_in (n : nat) (ns : list nat) :
  existsb (Nat.eqb n) ns = false <-> ~ In n ns.
Proof.
  split; intro H.
  - intro HC; apply existsb_in in HC; congruence.
  - destruct (existsb (Nat.eqb n) ns) eqn:Hn; auto.
    apply existsb_in in Hn; congruence.
Qed.

Lemma existsb_false_forall {A : Type} (P : A -> bool) (l : list A) :
  existsb P l = false ->
  forall x, In x l -> P x = false.
Proof.
  induction l; intros H0 x Hin.
  - inversion Hin.
  - simpl in *.
    destruct Hin as [? | Hin]; subst.
    + destruct (P x); simpl in H0; congruence.
    + destruct (P a); simpl in H0; try congruence.
      eapply IHl in H0; eauto.
Qed.

Lemma app_nil_inv {A : Type} (l1 l2 : list A) :
  l1 ++ l2 = nil ->
  l1 = nil /\ l2 = nil.
Proof. intro H; destruct l1; auto; inversion H. Qed.

Lemma inj_spec {A B : Type} (f : A -> B) (g : B -> A) :
  (forall x, g (f x) = x) ->
  forall x y, f x = f y -> x = y.
Proof.
  intros H0 x y H1.
  rewrite <- (H0 x), <- (H0 y), H1, H0; reflexivity.
Qed.

Lemma surj_spec {A B : Type} (f : A -> B) (g : B -> A) :
  (forall x, f (g x) = x) ->
  forall y, exists x, f x = y.
Proof. intros H0 y; exists (g y); auto. Qed.

Lemma odd_div_add (n : nat) :
  n mod 2 = 1%nat ->
  (n / 2 + n / 2 + 1)%nat = n.
Proof.
  intro Hmod; simpl in *.
  generalize (Nat.divmod_spec n 1 0 1 (Nat.le_refl _)).
  intro H; destruct (Nat.divmod n 1 0 1); destruct H as [H H1].
  simpl in *; lia.
Qed.

Definition option_mult {A : Type} (M : Monoid A) (x y : option A) : option A :=
  match (x, y) with
  | (Some l, Some r) => Some (monoid_plus M l r)
  | _ => None
  end.

Lemma option_mult_unit_r {A : Type} (M : Monoid A) (x : option A) :
  option_mult M x None = None.
Proof. destruct x; auto. Qed.

Lemma option_mult_assoc {A : Type} {M : Monoid A} (L : MonoidLaws M) (x y z : option A) :
  option_mult M (option_mult M x y) z = option_mult M x (option_mult M y z).
Proof.
  destruct x; destruct y; destruct z; auto.
  unfold option_mult; simpl; f_equal; apply monoid_assoc.
Qed.
