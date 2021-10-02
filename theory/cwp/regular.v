Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Require Import Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import ExtLib.Structures.Monoid.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Import ListNotations.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.

Require Import axioms.
Require Import borel.
Require Import infer.
Require Import ix_tree.
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.
Require Import semiring.

Ltac none_zero :=
  match goal with
  | [ H: context[~ None === zero] |- _] =>
    unfold zero in H; simpl in H; congruence
  end.

Definition injection {A B : Type} (f : A -> B) : Prop :=
  exists g : B -> A, (forall x, g (f x) = x).

Definition bijection {A B : Type} (f : A -> B) : Prop :=
  exists g : B -> A, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

Definition seq_perm {A : Type} (s1 s2 : nat -> A) : Prop :=
  exists f : nat -> nat, bijection f /\ forall i, s1 i = s2 (f i).

Definition seq_subset {A : Type} (f g : nat -> A) : Prop :=
  forall i, exists j, f i = g j.

Class HasZero (A : Type) : Type := { zero : A }.
Instance HasZeroQ : HasZero Q := { zero := 0 }.
Instance HasZeroOption {A : Type} : HasZero (option A) := { zero := None }.

(** Membership predicate for sequences. *)
Definition seq_in {A : Type} (x : A) (s : nat -> A) : Prop :=
  exists i, s i = x.

(** Nonzero membership predicate for sequences. *)
Definition seq_in' {A : Type} `{HasZero A} (x : A) (s : nat -> A) : Prop :=
  x <> zero /\ exists i, s i = x.

Definition seq_nonzero {A : Type} `{HasZero A} (s : nat -> A) : Prop :=
  exists i, s i <> zero.

Definition seq_injection {A : Type} (s1 s2 : nat -> A) : Prop :=
  exists f : nat -> nat, injection f /\ forall i, s1 i = s2 (f i).

Definition seq_bijection {A : Type} (s1 s2 : nat -> A) : Prop :=
  exists f : nat -> nat, bijection f /\ forall i, s1 i = s2 (f i).

Definition seq_injection_upto_0 {A : Type} `{HasZero A} `{Equivalence A} (s1 s2 : nat -> A) : Prop :=
  exists f g : nat -> nat, (forall i, ~ s1 i === zero -> g (f i) = i /\ s1 i === s2 (f i)).

Definition seq_bijection_upto_0 {A : Type} `{HasZero A} `{Equivalence A} (s1 s2 : nat -> A) : Prop :=
  seq_injection_upto_0 s1 s2 /\ seq_injection_upto_0 s2 s1.

Definition seq_nodup {A : Type} `{HasZero A} `{Equivalence A} (s : nat -> A) : Prop :=
  forall i j x, ~ x === zero -> s i = x -> s j = x -> i = j.

Lemma seq_nodup_reify_injection {A : Type} (s1 s2 : nat -> option A) :
  seq_nodup s1 ->
  (forall i, exists j, s1 i <> zero -> s1 i = s2 j) ->
  (forall j, exists i, s2 j <> zero -> s1 i = s2 j) ->
  seq_injection_upto_0 s1 s2.
Proof.
  intros Hs1 Hf Hg.
  apply choice in Hf.
  apply choice in Hg.
  destruct Hf as [f Hf].
  destruct Hg as [g Hg].
  exists f, g; intros i Hnz; split.
  - unfold seq_nodup in *.
    unfold equiv, zero in *; simpl in *.
    assert (s1 i = s2 (f i)).
    { apply Hf; auto. }
    specialize (Hg (f i)).
    assert (s1 (g (f i)) = s2 (f i)).
    { apply Hg; intro HC; rewrite <- H in HC; congruence. }
    eapply Hs1; eauto.
    rewrite H0; auto.
  - apply Hf; auto.
Qed.

Lemma seq_nodup_iff_bijection {A : Type} `{Equivalence A} (s1 s2 : nat -> option A) :
  seq_nodup s1 ->
  seq_nodup s2 ->
  (forall x, (exists i, s1 i === Some x) <-> (exists j, s2 j === Some x)) ->
  seq_bijection_upto_0 s1 s2.
Proof.
  intros Hs1 Hs2 Hiff.
  split.
  - apply seq_nodup_reify_injection; auto.
    + intros i.
      destruct (s1 i) eqn:Hi.
      * specialize (Hiff a).
        assert (Hj: exists j, s2 j = Some a).
        { apply Hiff; exists i; auto. }
        destruct Hj as [j Hj].
        exists j; intro; auto.
      * unfold equiv, zero; simpl; exists O; congruence.
    + intro j.
      destruct (s2 j) eqn:Hj.
      * specialize (Hiff a).
        assert (H': exists j, s1 j = Some a).
        { apply Hiff; exists j; auto. }
        destruct H' as [i Heq].
        exists i; intro Hnz; auto.
      * exists O; unfold zero; simpl; congruence.
  - apply seq_nodup_reify_injection; auto.
    + intros j.
      destruct (s2 j) eqn:Hj.
      * specialize (Hiff a).
        assert (Hi: exists i, s1 i = Some a).
        { apply Hiff; exists j; auto. }
        destruct Hi as [i Hi].
        exists i; intro; auto.
      * unfold equiv, zero; simpl; exists O; congruence.
    + intro j.
      destruct (s1 j) eqn:Hj.
      * specialize (Hiff a).
        assert (H': exists j, s2 j = Some a).
        { apply Hiff; exists j; auto. }
        destruct H' as [i Heq].
        exists i; intro Hnz; auto.
      * exists O; unfold zero; simpl; congruence.
Qed.

Definition seq_no_unit {A : Type} (M : Monoid A) (s : nat -> option A) : Prop :=
  forall i, s i <> Some (monoid_unit M).

Definition seq_incomparable {A : Type} (s : nat -> option (list A)) : Prop :=
  forall i j x y, i <> j -> s i = Some x -> s j = Some y -> incomparable x y.

Definition seq_incomparable' {A : Type} (s : nat -> option (list A)) : Prop :=
  forall i j, s i = Some [] \/ s j = Some [] \/
         forall x y, i <> j -> s i = Some x -> s j = Some y -> incomparable x y.

Definition seq_incomparable'' {A : Type} (s : nat -> option (list A)) : Prop :=
  (forall i j, s i = Some [] -> s j = Some [] -> i = j) /\
  (forall i j, s i = Some [] \/ s j = Some [] \/
          forall x y, i <> j -> s i = Some x -> s j = Some y -> incomparable x y).

Definition seqs_incomparable {A : Type} (s1 s2 : nat -> option (list A)) : Prop :=
  forall i j x y, s1 i = Some x -> s2 j = Some y -> incomparable x y.

Definition seqs_incomparable' {A : Type} (s1 s2 : nat -> option (list A)) : Prop :=
  forall i j, s1 i = Some [] \/ (forall x y, s1 i = Some x -> s2 j = Some y -> incomparable x y).

Definition table_incomparable {A : Type} (tbl : nat -> nat -> option (list A)) : Prop :=
  forall i j k l x y,
    (i, j) <> (k, l) -> tbl i j = Some x -> tbl k l = Some y -> incomparable x y.

Lemma seq_incomparable_nodup {A : Type} `{EqType A} (s : nat -> option (list A)) :
  seq_incomparable s ->
  seq_nodup s.
Proof.
  intros Hinc i j [l|] Hnz H0 H1.
  - unfold seq_incomparable in Hinc.
    destruct (Nat.eqb_spec i j); auto.
    specialize (Hinc i j l l n H0 H1).
    apply incomparable_not_comparable in Hinc.
    exfalso; apply Hinc. apply is_prefix_comparable; left; reflexivity.
  - unfold equiv, zero in Hnz; simpl in Hnz; congruence.
Qed.

Instance Reflexive_seq_bijection {A : Type} : Reflexive (@seq_bijection A).
Proof. repeat (exists id; intuition). Qed.

Instance Symmetric_seq_bijection {A : Type} : Symmetric (@seq_bijection A).
Proof.
  intros s1 s2 [f [[g [Hgf Hfg]] Heq]].
  exists g. split; firstorder.
  rewrite Heq, Hfg; reflexivity.
Qed.

Instance Reflexive_seq_bijection_upto_0 {A : Type} `{HasZero A} `{Equivalence A}
  : Reflexive (@seq_bijection_upto_0 A _ _ _).
Proof. intro s; split; exists id, id; unfold id; intuition. Qed.

Instance Symmetric_seq_bijection_upto_0 {A : Type} `{HasZero A} `{Equivalence A}
  : Symmetric (@seq_bijection_upto_0 A _ _ _).
Proof.
  intros s1 s2 [[f [g H12]] [h [k H21]]]; split.
  - exists h, k; auto.
  - exists f, g; auto.
Qed.

Instance Transitive_seq_bijection_upto_0 {A : Type} `{HasZero A} `{Equivalence A}
  : Transitive (@seq_bijection_upto_0 A _ _ _).
Proof.
  intros s1 s2 s3 [[a [b H12]] [c [d H21]]] [[e [f H23]] [g [h H32]]].
  split.
  - exists (e ∘ a), (b ∘ f).
    intros i Hnz.
    specialize (H12 i Hnz). destruct H12 as [H1 H2].
    assert (Hnz': ~ s2 (a i) === zero).
    { rewrite <- H2; auto. }
    specialize (H23 (a i) Hnz'). destruct H23 as [H3 H4].
    unfold compose. split.
    + rewrite H3, H1; reflexivity.
    + rewrite H2, H4; reflexivity.
  - exists (c ∘ g), (h ∘ d).
    intros i Hnz.
    specialize (H32 i Hnz). destruct H32 as [H1 H2].
    assert (Hnz': ~ s2 (g i) === zero).
    { rewrite <- H2; auto. }
    specialize (H21 (g i) Hnz'). destruct H21 as [H3 H4].
    unfold compose. split.
    + rewrite H3, H1. reflexivity.
    + rewrite H2, H4; reflexivity.
Qed.

Program Instance Equivalence_seq_bijection_upto_0 {A : Type} `{HasZero A} `{Equivalence A}
  : Equivalence (@seq_bijection_upto_0 A _ _ _).

Instance OType_seq {A : Type} `{HasZero A} `{Equivalence A} : OType (nat -> A) :=
  {| leq := seq_bijection_upto_0 |}.

Lemma leq_sup {A : Type} `{OType A} (s1 s2 : nat -> A) (sup : A) :
  (forall i, exists j, leq (s1 i) (s2 j)) ->
  (forall i, exists j, leq (s2 i) (s1 j)) ->
  supremum sup s1 -> supremum sup s2.
Proof.
  intros H0 H1 [Hlub Hub]; split.
  - intro i; destruct (H1 i) as [j Hj]; etransitivity; eauto.
  - intros x Hx; apply Hub; intro i.
    destruct (H0 i) as [j Hj]; etransitivity; eauto.
Qed.

Lemma seq_bijection_injection {A : Type} (s1 s2 : nat -> A) :
  seq_bijection s1 s2 ->
  seq_injection s1 s2.
Proof. firstorder. Qed.

Lemma seq_bijection_injection_upto_0 (s1 s2 : nat -> Q) :
  seq_bijection_upto_0 s1 s2 ->
  seq_injection_upto_0 s1 s2.
Proof. firstorder. Qed.

Definition sub_perm {A : Type} (l1 l2 : list A) : Prop :=
  exists l, Permutation (l1 ++ l) l2.

Lemma sub_perm_sum_Q_list (l1 l2 : list Q) :
  (forall x, In x l2 -> 0 <= x) ->
  sub_perm l1 l2 ->
  sum_Q_list l1 <= sum_Q_list l2.
Proof.
  intros Hle [l Hperm].
  assert (sum_Q_list (l1 ++ l) <= sum_Q_list l2).
  { unfold sum_Q_list. rewrite fold_right_permutation; eauto; try lra.
    - apply Qplus_comp.
    - apply Qplus_comm.
    - apply Qplus_assoc. }
  rewrite sum_Q_list_app in H.
  assert (0 <= sum_Q_list l).
  { apply sum_Q_list_nonnegative; auto.
    intros x Hin.
    apply Hle.
    eapply Permutation_in; eauto.
    apply in_or_app; right; auto. }
  lra.
Qed.

Lemma Permutation_in_Qeq (x : Q) (l1 l2 : list Q) :
  Permutation l1 l2 -> In x l1 -> exists y, x == y /\ In y l2.
Proof.
  intro Hperm. revert x. induction Hperm; simpl; intros ? Hin; try solve[firstorder].
  apply IHHperm1 in Hin; destruct Hin as [y [Hxy Hin]].
  apply IHHperm2 in Hin; destruct Hin as [z [Hyz Hin]].
  exists z; intuition; lra.
Qed.

Lemma sub_perm_map_Qred_sum_Q_list (l1 l2 : list Q) :
  (forall x, In x l2 -> 0 <= x) ->
  sub_perm (map Qred l1) (map Qred l2) ->
  sum_Q_list l1 <= sum_Q_list l2.
Proof.
  intros Hle [l Hperm].
  assert (sum_Q_list (map Qred l1 ++ l) <= sum_Q_list (map Qred l2)).
  { unfold sum_Q_list. rewrite fold_right_permutation; eauto; try lra.
    - apply Qplus_comp.
    - apply Qplus_comm.
    - apply Qplus_assoc. }
  rewrite sum_Q_list_app in H.
  rewrite 2!sum_Q_list_map_Qred in H.
  assert (0 <= sum_Q_list l).
  { apply sum_Q_list_nonnegative; auto.
    intros x Hin.
    assert (Hin': In x (map Qred l1 ++ l)).
    { apply in_or_app; auto. }
    eapply Permutation_in_Qeq in Hin'; eauto.
    destruct Hin' as [y [Heq Hin']].
    apply in_map_iff in Hin'.
    destruct Hin' as [z [Heq' Hin']].
    rewrite Heq, <- Heq', Qred_correct.
    apply Hle; auto. }
  lra.
Qed.

Lemma sub_perm_nil {A : Type} (l : list A) :
  sub_perm [] l.
Proof. exists l; apply Permutation_refl. Qed.

Lemma Permutation_filter {A : Type} (f : A -> bool) (l1 l2 : list A) :
  Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
Proof.
  induction 1; simpl.
  - constructor.
  - destruct (f x); auto.
  - destruct (f y) eqn:Hy.
    + destruct (f x) eqn:Hx.
      * constructor.
      * constructor. reflexivity.
    + reflexivity.
  - etransitivity; eauto.
Qed.

Lemma Permutation_filter_partition {A : Type} (f : A -> bool) (l : list A) :
  Permutation (filter f l ++ filter (negb ∘ f) l) l.
Proof.
  induction l.
  - reflexivity.
  - unfold compose; simpl.
    destruct (f a); simpl.
    + constructor; auto.
    + etransitivity.
      * symmetry; apply Permutation_middle.
      * constructor; auto.
Qed.

Lemma filter_andb {A : Type} (f g : A -> bool) (l : list A) :
  filter (fun x => f x && g x) l = filter f (filter g l).
Proof.
  induction l; simpl; auto.
  destruct (f a) eqn:Hf; simpl.
  - destruct (g a); simpl; auto; rewrite Hf, IHl; reflexivity.
  - destruct (g a); simpl; auto; rewrite Hf; auto.
Qed.

Lemma permutation_filter_app {A : Type} (f g : A -> bool) (l : list A) :
  (forall x, In x l -> f x = negb (g x)) ->
  Permutation (filter (fun x => f x || g x) l) (filter f l ++ filter g l).
Proof.
  induction l; simpl; intro Hneg; auto.
  destruct (f a) eqn:Hf; simpl.
  - rewrite Hneg in Hf.
    + apply negb_true_iff in Hf.
      rewrite Hf; constructor; auto.
    + left; reflexivity.
  - rewrite Hneg in Hf.
    + apply negb_false_iff in Hf.
      rewrite Hf; etransitivity.
      2: { apply Permutation_middle. }
      constructor; auto.
    + left; reflexivity.
Qed.

Lemma map_compose {A B C : Type} (f : A -> B) (g : B -> C) (l : list A) :
  map (g ∘ f) l = map g (map f l).
Proof.
  unfold compose; induction l; auto; simpl; rewrite IHl; auto.
Qed.

Lemma filter_nil {A : Type} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) ->
  filter f l = [].
Proof.
  induction l; simpl; intro Hin; auto.
  rewrite Hin; auto.
Qed.

Lemma nodup_incl_permutation (l1 l2 : list nat) :
  NoDup l1 ->
  NoDup l2 ->
  incl l1 l2 ->
  Permutation l1 (filter (fun k => existsb (Nat.eqb k) l1) l2).
Proof.
  intros Hnodup1 Hnodup2 Hincl.
  apply NoDup_Permutation_bis; auto.
  - apply NoDup_incl_length.
    + apply NoDup_filter; auto.
    + intros x Hin.
      apply filter_In in Hin.
      destruct Hin.
      apply existsb_in; auto.
  - intros x Hin.
    apply filter_In; intuition.
    apply existsb_in; auto.
Qed.

Lemma in_range_list_max (l : list nat) (n : nat) :
  In n l ->
  In n (range (S (list_max l))).
Proof.
  intro Hin.
  rewrite range_seq. apply in_seq.
  split; try lia; simpl.
  assert (H: (list_max l <= list_max l)%nat).
  { reflexivity. }
  apply list_max_le in H.
  rewrite Forall_forall in H.
  apply H in Hin; lia.
Qed.

Lemma injection_injective {A B : Type} (f : A -> B) (x y : A) :
  injection f ->
  f x = f y ->
  x = y.
Proof.
  intros [g Hgf] Heq.
  rewrite <- (Hgf x), <- (Hgf y), Heq; reflexivity.
Qed.

Lemma seq_injection_sub_perm {A : Type} (s1 s2 : nat -> A) :
  seq_injection s1 s2 ->
  forall i, exists j, sub_perm (first_n s1 i) (first_n s2 j).
Proof.
  intros [f [[g Hgf] Heq]] i.
  unfold sub_perm.
  set (ixs := map f (range i)).
  set (j := S (list_max ixs)).
  exists j.
  exists (map s2 (filter (fun k => negb (existsb (Nat.eqb k) ixs)) (range j))).
  rewrite 2first_n_first_n'.
  unfold first_n'.
  assert (Permutation (map s1 (range i))
                      (map s2 (filter (fun k => existsb (Nat.eqb k) ixs) (range j)))).
  { transitivity (map (s2 ∘ f) (range i)).
    - erewrite map_ext; eauto.
    - rewrite map_compose.
      apply Permutation_map.
      unfold ixs, j.
      apply nodup_incl_permutation.
      + apply FinFun.Injective_map_NoDup.
        * intros ? ?; apply injection_injective; exists g; auto.
        * rewrite range_seq. apply seq_NoDup.
      + rewrite range_seq; apply seq_NoDup.
      + intros n Hin.
        apply in_range_list_max; auto. }
  etransitivity.
  rewrite Permutation_app_comm.
  eapply Permutation_app_head; eauto.
  rewrite <- map_app.
  apply Permutation_map.
  set (pred := fun k => existsb (Nat.eqb k) ixs).
  replace (fun k => negb (existsb (Nat.eqb k) ixs)) with (negb ∘ pred) by reflexivity.
  rewrite Permutation_app_comm.
  apply Permutation_filter_partition.
Qed.

Lemma seq_injection_partial_sum (s1 s2 : nat -> Q) :
  (forall i, 0 <= s2 i) ->
  seq_injection s1 s2 ->
  forall i, exists j, partial_sum s1 i <= partial_sum s2 j.
Proof.
  intros Hnonneg Hinj.
  intro i. unfold partial_sum.
  apply seq_injection_sub_perm with (i0:=i) in Hinj.
  destruct Hinj as [j Hsubperm].
  exists j; apply sub_perm_sum_Q_list; auto.
  intros x Hin. apply in_first_n in Hin.
  destruct Hin as [? [? ]]; subst; auto.
Qed.

Definition filter_zeroes : list Q -> list Q :=
  filter (negb ∘ Qeq_bool 0).

Lemma filter_zeroes_sum_Q_list (l : list Q) :
  sum_Q_list (filter_zeroes l) == sum_Q_list l.
Proof.
  induction l; simpl; try lra.
  unfold compose. destruct (Qeq_bool 0 a) eqn:Ha; simpl; try lra.
  apply Qeq_bool_iff in Ha; lra.
Qed.

Lemma filter_zeroes_map {A : Type} (f : A -> Q) (l : list A) :
  filter_zeroes (map f l) = map f (filter (fun x => negb (Qeq_bool 0 (f x))) l).
Proof.
  induction l; simpl; auto.
  unfold compose.
  destruct (negb (Qeq_bool 0 (f a))); simpl; auto; rewrite IHl; auto.
Qed.

Lemma andb_impl_eq {A : Type} (f g : A -> bool) :
  (forall x, f x = true -> g x = true) ->
  forall x, f x && g x = f x.
Proof. intros H x; destruct (f x) eqn:Hf; simpl; auto. Qed.

Lemma NoDup_injective {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intro H. induction 1; simpl.
  - constructor.
  - constructor.
    + intro HC. apply in_map_iff in HC.
      destruct HC as [y [Heq Hin]].
      assert (Hneq: y <> x).
      { intro HC; subst; congruence. }
      specialize (H y x (in_cons _ _ _ Hin) (in_eq _ _) Hneq); congruence.
    + apply IHNoDup; firstorder.
Qed.

Lemma seq_injection_upto_0_sub_perm (s1 s2 : nat -> Q) :
  seq_injection_upto_0 s1 s2 ->
  forall i, exists j, sub_perm (map Qred (filter_zeroes (first_n s1 i)))
                     (map Qred (filter_zeroes (first_n s2 j))).
Proof.
  intros [f [g Hgf]] i.
  unfold sub_perm.
  set (nz_ixs := (filter (fun k => negb (Qeq_bool 0 (s1 k))) (range i))).
  set (f_ixs := map f nz_ixs).
  set (j := S (list_max f_ixs)).
  exists j.
  exists (map (Qred ∘ s2) (filter (fun k => negb (Qeq_bool 0 (s2 k)) &&
                                    negb (existsb (Nat.eqb k) f_ixs)) (range j))).
  rewrite 2first_n_first_n'.
  unfold first_n'.
  assert (Permutation (map (Qred ∘ s1) nz_ixs)
                      (map (Qred ∘ s2) (filter (fun k => existsb (Nat.eqb k) f_ixs) (range j)))).
  { transitivity (map (Qred ∘ s2 ∘ f) nz_ixs).
    - erewrite map_ext_in; eauto.
      intros k Hin; unfold nz_ixs in Hin.
      apply filter_In in Hin; destruct Hin as [H0 H1].
      apply negb_true_iff, Qeq_bool_neq in H1; firstorder.
      unfold compose; apply Qred_complete.
      unfold equiv in Hgf.
      apply Hgf; unfold zero; simpl; lra.
    - rewrite map_compose.
      apply Permutation_map.
      unfold nz_ixs, j.
      apply nodup_incl_permutation.
      + apply NoDup_injective.
        * intros x y Hinx Hiny Hneq HC.
          assert (Hx: ~ s1 x == 0).
          { apply filter_In in Hinx; destruct Hinx as [_ Hinx].
            apply negb_true_iff in Hinx.
            apply Qeq_bool_neq in Hinx. lra. }
          assert (Hy: ~ s1 y == 0).
          { apply filter_In in Hiny; destruct Hiny as [_ Hiny].
            apply negb_true_iff in Hiny.
            apply Qeq_bool_neq in Hiny. lra. }
          apply Hgf in Hx; apply Hgf in Hy.
          destruct Hx as [Hx _]; destruct Hy as [Hy _].
          apply Hneq. rewrite <- Hx, <- Hy.
          rewrite HC; reflexivity.
        * unfold nz_ixs.
          apply NoDup_filter.
          rewrite range_seq. apply seq_NoDup.
      + rewrite range_seq; apply seq_NoDup.
      + intros n Hin.
        apply in_range_list_max; auto. }
  rewrite 2!map_compose in H.
  unfold nz_ixs in H; etransitivity.
  rewrite Permutation_app_comm; eapply Permutation_app_head.
  rewrite filter_zeroes_map; apply H.
  rewrite filter_zeroes_map.
  rewrite <- 2!map_compose.
  rewrite <- map_app.
  apply Permutation_map.
  assert (filter (fun k : nat => existsb (Nat.eqb k) f_ixs) (range j) =
          filter (fun k : nat => negb (Qeq_bool 0 (s2 k)) && existsb (Nat.eqb k) f_ixs) (range j)).
  { apply filter_ext; intro k.
    unfold f_ixs, nz_ixs.
    rewrite andb_comm; symmetry.
    set (p := fun x => existsb (Nat.eqb x) (map f (filter (fun k0 : nat => negb (Qeq_bool 0 (s1 k0))) (range i)))).
    set (q := fun x => negb (Qeq_bool 0 (s2 x))).
    replace (existsb (Nat.eqb k) (map f (filter (fun k0 : nat => negb (Qeq_bool 0 (s1 k0))) (range i))))
      with (p k) by reflexivity.
    replace (negb (Qeq_bool 0 (s2 k))) with (q k) by reflexivity.
    apply andb_impl_eq.
    unfold p, q; intros x Hpx.
    apply existsb_in, in_map_iff in Hpx.
    destruct Hpx as [y [H0 H1]]. subst.
    apply filter_In in H1; destruct H1 as [H1 H2].
    apply negb_true_iff, Qeq_bool_neq in H2.
    apply negb_true_iff, Qeq_bool_false.
    apply Qnot_eq_sym in H2.
    destruct (Hgf y H2) as [H3 H4].
    rewrite <- H4. lra. }
  rewrite H0; clear H0.
  rewrite 2!filter_andb, <- filter_app.
  apply Permutation_filter.
  set (pred := fun k => existsb (Nat.eqb k) f_ixs).
  replace (fun k => negb (existsb (Nat.eqb k) f_ixs)) with (negb ∘ pred) by reflexivity.
  rewrite Permutation_app_comm.
  apply Permutation_filter_partition.
Qed.

Lemma seq_injection_upto_0_partial_sum (s1 s2 : nat -> Q) :
  (forall i, 0 <= s2 i) ->
  seq_injection_upto_0 s1 s2 ->
  forall i, exists j, partial_sum s1 i <= partial_sum s2 j.
Proof.
  intros Hnonneg Hinj.
  intro i. unfold partial_sum.
  apply seq_injection_upto_0_sub_perm with (i:=i) in Hinj.
  destruct Hinj as [j Hsubperm].
  exists j; rewrite <- filter_zeroes_sum_Q_list.
  cut (sum_Q_list (first_n s2 j) ==
       sum_Q_list (filter_zeroes (first_n s2 j))).
  { intro Heq; rewrite Heq; clear Heq.
    apply sub_perm_map_Qred_sum_Q_list; auto.
    intros x Hin.
    apply filter_In in Hin. destruct Hin as [H0 H1].
    apply in_first_n in H0.
    destruct H0 as [? [? ]]; subst; auto. }
  rewrite filter_zeroes_sum_Q_list; reflexivity.
Qed.

Lemma seq_bijection_supremum (s1 s2 : nat -> Q) (sup : Q) :
  (forall i, 0 <= s1 i) ->
  (forall i, 0 <= s2 i) ->
  seq_bijection s1 s2 ->
  supremum sup (partial_sum s1) ->
  supremum sup (partial_sum s2).
Proof.
  intros Hbij ? ?; apply leq_sup;
    apply seq_injection_partial_sum, seq_bijection_injection;
    auto; symmetry; auto.
Qed.

Lemma seq_bijection_upto_0_supremum (s1 s2 : nat -> Q) (sup : Q) :
  (forall i, 0 <= s1 i) ->
  (forall i, 0 <= s2 i) ->
  seq_bijection_upto_0 s1 s2 ->
  supremum sup (partial_sum s1) ->
  supremum sup (partial_sum s2).
Proof.
  intros Hbij ? ?; apply leq_sup;
    apply seq_injection_upto_0_partial_sum, seq_bijection_injection_upto_0;
    auto; symmetry; auto.
Qed.

Definition MonoidList {A : Type} : Monoid (list A) :=
  {| monoid_plus := fun x y => app x y
   ; monoid_unit := [] |}.

Program Instance MonoidLawsList {A : Type} : MonoidLaws (@MonoidList A).
Next Obligation. intros ? ? ?; rewrite app_assoc; reflexivity. Qed.
Next Obligation. intro; reflexivity. Qed.
Next Obligation. intro; apply app_nil_r. Qed.

Hint Resolve MonoidLawsList : typeclass_instances.

(*** Operations on sequences. *)

Definition seq_one {A : Type} (x : A) (i : nat) : option A :=
  match i with
  | O => Some x
  | _ => None
  end.

Definition seq_zero {A : Type} : nat -> option A := const None.

(** Interleave two infinite sequences together. *)
Definition seq_union {A : Type} (f g : nat -> A) (i : nat) : A :=
  match modulo i 2 with
  | O => f (div i 2)
  | _ => g (div i 2)%nat
  end.

(** Flatten a sequence of sequences via the bijection from nat to nat*nat. *)
Definition seq_flatten {A : Type} (f : nat -> nat -> A) (n : nat) : A :=
  let (i, j) := nat_f n in f i j.

Definition seq_union' {A : Type} (f g : nat -> option A) : nat -> option A :=
  seq_flatten (fun i j => match i with
                       | O => f j
                       | S O => g j
                       | _ => None
                       end).

(** Split a sequence into a sequence of sequences (inverse of flatten). *)
Definition seq_split {A : Type} (f : nat -> A) (i j : nat) : A :=
  let n := nat_g (i, j) in f n.

(** Cartesian product of two monoid sequences. *)
Definition seq_product {A : Type} (M : Monoid A) (f g : nat -> option A) (n : nat)
  : option A :=
  let (i, j) := nat_f n in option_mult M (f i) (g j).

(** seq_product f g n i is the ith element of f . g^n. E.g.,

   0      1      2
0  f 0,   f 1,   f 2, ...
1  fg 0,  fg 1,  fg 2, ...
2  fgg 0, fgg 1, fgg 2, ...
...
*)
(** I.e., seq_product f g n is the nth cartesian product with base
    sequence f, taking the product with g on the right each time.  *)
Definition seq_product_n {A : Type} (M : Monoid A) (f g : nat -> option A) (n : nat)
  : nat -> option A :=
  Nat.iter n (fun f' => seq_product M f' g) f.

(* ((f . g) . g) ... *)
Fixpoint seq_product_n' {A : Type} (M : Monoid A) (f g : nat -> option A) (n : nat)
  : nat -> option A :=
  match n with
  | O => f
  | S n' => seq_product M (seq_product_n' M f g n') g
  end.

Lemma seq_product_n_seq_product_n' {A : Type} (M : Monoid A) (f g : nat -> option A) (n i : nat) :
  seq_product_n M f g n i = seq_product_n' M f g n i.
Proof.
  revert i; induction n; simpl; intro i; try reflexivity.
  unfold seq_product.
  destruct (nat_f i).
  rewrite IHn; reflexivity.
Qed.

(* ... (g . (g . f)) *)
Fixpoint seq_product_n'' {A : Type} (M : Monoid A) (f g : nat -> option A) (n : nat)
  : nat -> option A :=
  match n with
  | O => f
  | S n' => seq_product M g (seq_product_n'' M f g n')
  end.

(** seq_reps_n f n i is:

   0    1    2
0  {ϵ},    {},    {}, ...
1  ϵf 0,  ϵf 1,  ϵf 2, ...
2  ϵff 0, ϵff 1, ϵff 2, ...
...
*)

(** I.e., seq_reps_n f n is the nth cartesian product with {ϵ} as the
    base and f on the right. So,
    seq_reps_n f 0 = {ϵ},
    seq_reps_n f 1 = f,
    seq_reps_n f 2 = ff,
    etc.
*)
Definition seq_reps_n {A : Type} (M : Monoid A) (f : nat -> option A) (n : nat)
  : nat -> option A :=
  seq_product_n M (seq_one (monoid_unit M)) f n.

Definition seq_reps_n' {A : Type} (M : Monoid A) (f : nat -> option A) (n : nat)
  : nat -> option A :=
  seq_product_n'' M (seq_one (monoid_unit M)) f n.

Definition seq_reps_n_plus {A : Type} (M : Monoid A) (f : nat -> option A) (n : nat)
  : nat -> option A :=
  seq_product_n M f f n.

Definition seq_reps_n_plus' {A : Type} (M : Monoid A) (f : nat -> option A) (n : nat)
  : nat -> option A :=
  seq_product_n'' M f f n.

(** Sequence containing all finite repetitions of elements of the
    argument sequence. The flattening (big union) of all nth cartesian
    products of f (with {ϵ} base). *)
Definition seq_reps {A : Type} (M : Monoid A) (f : nat -> option A) : nat -> option A :=
  seq_flatten (seq_reps_n M f).

Definition seq_reps' {A : Type} (M : Monoid A) (f : nat -> option A) : nat -> option A :=
  seq_flatten (seq_reps_n' M f).

Definition seq_reps_plus {A : Type} (M : Monoid A) (f : nat -> option A) : nat -> option A :=
  seq_flatten (seq_reps_n_plus M f).

Definition seq_reps_plus' {A : Type} (M : Monoid A) (f : nat -> option A) : nat -> option A :=
  seq_flatten (seq_reps_n_plus' M f).  

Fixpoint option_mult_list {A : Type} (M : Monoid A) (l : list (option A)) : option A :=
  match l with
  | [] => Some (monoid_unit M)
  | x :: l' => option_mult M x (option_mult_list M l')
  end.

(*** Sequence facts. *)

Lemma seq_bijection_compose {A B : Type} (f : A -> B) (s1 s2 : nat -> A) :
  seq_bijection s1 s2 ->
  seq_bijection (f ∘ s1) (f ∘ s2).
Proof.
  intros [g [[g' [Hg'g Hgg']] Heq]].
  unfold compose.
  exists g; firstorder.
  rewrite Heq; auto.
Qed.

Lemma singleton_seq_none {A : Type} (x : A) (i : nat) :
  (0 < i)%nat -> seq_one x i = None.
Proof. intro Hlt; destruct i; try lia; reflexivity. Qed.

Lemma singleton_seq_nonzero {A : Type} (x : A) (i : nat) :
  ~ seq_one x i = None ->
  i = O.
Proof. destruct i; auto; intro HC; exfalso; apply HC; reflexivity. Qed.

(** seq_union is correct. *)
Lemma seq_union_spec {A : Type} (f g : nat -> A) (x : A) :
  ((exists i, f i = x) \/ (exists j, g j = x)) <-> exists i, seq_union f g i = x.
Proof.
  split.
  - unfold seq_union; intros [[i Hf] | [i Hg]].
    + exists (2*i)%nat.
      rewrite mult_comm, Nat.mod_mul; try lia.
      rewrite Nat.div_mul; try lia; auto.
    + exists (2*i + 1)%nat.
      rewrite Nat.add_mod; try lia.
      rewrite mult_comm; rewrite Nat.mod_mul; try lia.
      rewrite plus_0_l.
      assert (H: ((i * 2 + 1) / 2 = i)%nat).
      { rewrite plus_comm.
        rewrite Nat.div_add; auto. }
      rewrite H; auto.
  - intros [i Hunion].
    unfold seq_union in Hunion.
    destruct (i mod 2); firstorder.
Qed.

Instance Proper_seq_in' {A : Type} `{HasZero A}
  : Proper (eq ==> seq_bijection_upto_0 ==> iff) seq_in'.
Proof.
  intros x y ? s1 s2 Heq; subst.
  unfold seq_in'.
  split; intros [Hnz [i Hin]]; split; auto.
  - destruct Heq as [[f [g Hinj]] _].
    exists (f i); rewrite <- Hin in Hnz.
    apply Hinj in Hnz; subst; intuition.
  - destruct Heq as [_ [f [g Hinj]]].
    exists (f i); rewrite <- Hin in Hnz.
    apply Hinj in Hnz; subst; intuition.
Qed.

Lemma seq_bijection_upto_0_zero {A : Type} (s : nat -> option A) :
  seq_bijection_upto_0 s seq_zero ->
  s = seq_zero.
Proof.
  intros [[f [f' H0]] [g [g' H1]]].
  simpl in *; unfold equiv in *.
  apply functional_extensionality; intro n.
  specialize (H0 n); specialize (H1 n).
  destruct (s n) eqn:Hn.
  - assert (H2: Some a <> None).
    { congruence. }
    apply H0 in H2; destruct H2; rewrite H2; reflexivity.
  - reflexivity.
Qed.

(*** Sequence identities. *)

Lemma seq_flatten_compose {A B : Type} `{OType B}
      (f : A -> B) (rows : nat -> nat -> A) :
  equ (f ∘ seq_flatten rows) (seq_flatten (fun i j => f (rows i j))).
Proof.
  unfold compose, seq_flatten.
  split; intro j; simpl; destruct (nat_f j); reflexivity.
Qed.

Lemma seq_flatten_const_None {A : Type} :
  seq_flatten (const (const (@None A))) = seq_zero.
Proof.
  extensionality i.
  unfold const, seq_flatten.
  destruct (nat_f i); reflexivity.
Qed.

Lemma seq_product_zero_l {A : Type} (M : Monoid A) (s : nat -> option A) :
  seq_product M seq_zero s = seq_zero.
Proof.
  extensionality i.
  unfold const, seq_product, option_mult.
  destruct (nat_f i); reflexivity.
Qed.

Lemma seq_product_zero_r {A : Type} (M : Monoid A) (s : nat -> option A) :
  seq_product M s seq_zero = seq_zero.
Proof.
  extensionality i.
  unfold const, seq_product, option_mult.
  destruct (nat_f i); destruct (s _); reflexivity.
Qed.

Lemma seq_union_seq_union' {A : Type} (s1 s2 : nat -> option A) :
  seq_union s1 s2 === seq_union' s1 s2.
Proof.
  unfold seq_union, seq_union', seq_flatten.
  set (f := fun n => nat_g (n mod 2, n / 2)%nat).
  set (g := fun n => let (i, j) := nat_f n in
                  match i with
                  | O => (2 * j)%nat
                  | _ => (2 * j + 1)%nat
                  end).
  split.
  - exists f, g; unfold f, g.
    intros i Hnz; split.
    + rewrite nat_f_g.
      destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod.
      * apply mod_n_div; auto.
      * apply mod_n_div_plus_1; auto.
    + rewrite nat_f_g.
      destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod; reflexivity.
  - exists g, f; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      destruct n.
      * rewrite Nat.mul_comm, Nat.mod_mul, Nat.div_mul; auto.
        rewrite <- Hi, nat_g_f; reflexivity.
      * destruct n.
        -- rewrite Nat.add_comm, Nat.mul_comm, Nat.mod_add, Nat.div_add; auto.
           simpl; rewrite <- Hi, nat_g_f; reflexivity.
        -- unfold zero, equiv in Hnz; simpl in Hnz; congruence.
    + destruct (nat_f i) eqn:Hi.
      destruct n.
      * rewrite Nat.mul_comm, Nat.mod_mul, Nat.div_mul; auto; reflexivity.
      * destruct n.
        -- rewrite Nat.add_comm, Nat.mul_comm, Nat.mod_add, Nat.div_add; auto.
           reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
Qed.

Instance Proper_seq_union (A : Type) `{HasZero A}
  : Proper (seq_bijection_upto_0 ==> seq_bijection_upto_0 ==> seq_bijection_upto_0) (@seq_union A).
Proof.
  intros s1 s1' [[a [b H0]] [c [d H1]]] s2 s2' [[e [f H2]] [g [h H3]]]; split.
  - exists (fun n => match n mod 2 with
             | O => (a (n / 2) * 2)%nat
             | _ => (e (n / 2) * 2 + 1)%nat
             end).
    exists (fun n => match n mod 2 with
             | O => (b (n / 2) * 2)%nat
             | _ => (f (n / 2) * 2 + 1)%nat
             end).
    intros i Hnz; split.
    + destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod.
      * rewrite Nat.mod_mul, Nat.div_mul; auto.
        unfold seq_union in Hnz; rewrite Hmod in Hnz.
        destruct (H0 _ Hnz) as [Hba _].
        rewrite Hba, Nat.mul_comm; apply mod_n_div; auto.
      * rewrite Nat.add_comm, Nat.mod_add, Nat.add_1_r; auto.
        replace (1 mod 2) with 1%nat by reflexivity.
        rewrite <- mod_2_div_succ.
        -- rewrite Nat.div_mul; auto.
           unfold seq_union in Hnz; rewrite Hmod in Hnz.
           destruct (H2 _ Hnz) as [Hfe _].
           rewrite Hfe, mod_2_div_mul_pred; auto.
           destruct i; simpl in *; congruence.
        -- apply Nat.mod_mul; auto.
    + unfold seq_union in *.
      destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod; rewrite Hmod in Hnz.
      * rewrite Nat.mod_mul, Nat.div_mul; auto; apply H0; auto.
      * rewrite Nat.add_comm, Nat.mod_add; auto.
        replace (1 mod 2) with 1%nat by reflexivity.
        rewrite <- mod_2_div_succ.
        -- rewrite Nat.div_mul; auto.
           apply H2; auto.
        -- apply Nat.mod_mul; auto.
  - exists (fun n => match n mod 2 with
             | O => (c (n / 2) * 2)%nat
             | _ => (g (n / 2) * 2 + 1)%nat
             end).
    exists (fun n => match n mod 2 with
             | O => (d (n / 2) * 2)%nat
             | _ => (h (n / 2) * 2 + 1)%nat
             end).
    intros i Hnz; split.
    + destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod.
      * rewrite Nat.mod_mul, Nat.div_mul; auto.
        unfold seq_union in Hnz; rewrite Hmod in Hnz.
        destruct (H1 _ Hnz) as [Hba _].
        rewrite Hba, Nat.mul_comm; apply mod_n_div; auto.
      * rewrite Nat.add_comm, Nat.mod_add, Nat.add_1_r; auto.
        replace (1 mod 2) with 1%nat by reflexivity.
        rewrite <- mod_2_div_succ.
        -- rewrite Nat.div_mul; auto.
           unfold seq_union in Hnz; rewrite Hmod in Hnz.
           destruct (H3 _ Hnz) as [Hfe _].
           rewrite Hfe, mod_2_div_mul_pred; auto.
           destruct i; simpl in *; congruence.
        -- apply Nat.mod_mul; auto.
    + unfold seq_union in *.
      destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod; rewrite Hmod in Hnz.
      * rewrite Nat.mod_mul, Nat.div_mul; auto; apply H1; auto.
      * rewrite Nat.add_comm, Nat.mod_add; auto.
        replace (1 mod 2) with 1%nat by reflexivity.
        rewrite <- mod_2_div_succ.
        -- rewrite Nat.div_mul; auto.
           apply H3; auto.
        -- apply Nat.mod_mul; auto.
Qed.

Instance Proper_seq_union' {A : Type}
  : Proper (seq_bijection_upto_0 ==> seq_bijection_upto_0 ==> seq_bijection_upto_0) (@seq_union' A).
Proof.
  intros ? ? H0 ? ? H1; rewrite <- 2!seq_union_seq_union', H0, H1; reflexivity.
Qed.

(* TODO: this really proves seq_union' is associative -- factor out
into separate lemma and prove this by equivalence of seq_union and
seq_union'. *)
Lemma seq_union_assoc {A : Type} (a b c : nat -> option A) :
  seq_union (seq_union a b) c === seq_union a (seq_union b c).
Proof.
  rewrite seq_union_seq_union'.
  symmetry; rewrite seq_union_seq_union'.
  cut (seq_union' a (seq_union' b c) === seq_union' (seq_union a b) c).
  { intro H. rewrite <- H.
    eapply Proper_seq_union'. reflexivity.
    apply seq_union_seq_union'. }
  cut (seq_union' a (seq_union' b c) === seq_union' (seq_union' a b) c).
  { intro H.
    rewrite H.
    eapply Proper_seq_union'. 
    - rewrite seq_union_seq_union'; reflexivity.
    - reflexivity. }
  symmetry; unfold seq_union', seq_flatten.
  set (f := fun n => let (i, n') := nat_f n in
                  match i with
                  | O => let (j, k) := nat_f n' in
                        match j with
                        | O => nat_g (O, k)
                        | S O => nat_g (S O, nat_g (O, k))
                        | _ => O
                        end
                  | S O => nat_g (S O, nat_g (S O, n'))
                  | _ => O
                  end).
  set (g := fun n => let (i, n') := nat_f n in
                  match i with
                  | O => nat_g (O, nat_g (O, n'))
                  | S O => let (j, k) := nat_f n' in
                          match j with
                          | O => nat_g (O, nat_g (S O, k))
                          | S O => nat_g (S O, k)
                          | _ => O
                          end
                  | _ => O
                  end).
  split.
  - exists f, g; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi; destruct (nat_f n0) eqn:Hn0.
      destruct n1; destruct n.
      * rewrite nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g, <- Hi, nat_g_f; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
      * destruct n1.
        -- rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
      * destruct n.
        -- rewrite 2!nat_f_g, <- Hi, nat_g_f; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
    + destruct (nat_f i) eqn:Hi; destruct (nat_f n0) eqn:Hn0.
      destruct n1, n.
      * rewrite nat_f_g; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
      * destruct n1.
        -- rewrite 2!nat_f_g; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
      * destruct n.
        -- rewrite 2!nat_f_g; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
  - exists g, f; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi; destruct (nat_f n0) eqn:Hn0.
      destruct n1; destruct n.
      * rewrite 2!nat_f_g, <- Hi, nat_g_f; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
      * rewrite 2!nat_f_g, <- Hi, nat_g_f; reflexivity.
      * destruct n1; destruct n;
          try solve [unfold equiv, zero in Hnz; simpl in Hnz; congruence].
        rewrite nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
    + destruct (nat_f i) eqn:Hi; destruct (nat_f n0) eqn:Hn0.
      destruct n.
      * rewrite 2!nat_f_g; reflexivity.
      * destruct n1, n.
        -- rewrite 2!nat_f_g; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
        -- destruct n1.
           ++ rewrite nat_f_g; reflexivity.
           ++ unfold equiv, zero in Hnz; simpl in Hnz; congruence.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
Qed.

Lemma seq_union_comm {A : Type} (a b : nat -> option A) :
  seq_union a b === seq_union b a.
Proof.
  set (f := fun n => match n mod 2 with
                  | O => (n + 1)%nat
                  | S _ => (n - 1)%nat
                  end).
  assert (Hf: forall n, f (f n) = n).
  { unfold f; intro n.
    destruct (mod_2_dec n).
    + rewrite H, Nat.add_1_r.
      apply mod_2_succ in H; rewrite H; lia.
    + rewrite H.
      assert (H1: (n - 1) mod 2 = 0%nat).
      { apply mod_2_pred in H; rewrite Nat.sub_1_r; auto. }
      apply mod_2_nonzero in H.
      rewrite H1; lia. }
  split; exists f, f; intros i Hnz; split; auto; clear Hf.
  - unfold seq_union in *; unfold f.
    destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod.
    + rewrite <- Nat.add_mod_idemp_l; auto.
      rewrite Nat.add_comm, Hmod, Nat.add_0_r.
      replace (1 mod 2) with 1%nat; auto.
      rewrite Nat.add_1_r, <- mod_2_div_succ; auto; reflexivity.
    + rewrite Nat.sub_1_r, mod_2_pred; auto.
      rewrite mod_2_div_pred; auto; reflexivity.
  - unfold seq_union in *; unfold f.
    destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod.
    + rewrite <- Nat.add_mod_idemp_l; auto.
      rewrite Nat.add_comm, Hmod, Nat.add_0_r.
      replace (1 mod 2) with 1%nat; auto.
      rewrite Nat.add_1_r, <- mod_2_div_succ; auto; reflexivity.
    + rewrite Nat.sub_1_r, mod_2_pred; auto.
      rewrite mod_2_div_pred; auto; reflexivity.
Qed.

Lemma seq_union_zero_l {A : Type} (a : nat -> option A) :
  seq_union seq_zero a === a.
Proof.
  unfold seq_union; split.
  - exists (fun i => i / 2)%nat, (fun i => i * 2 + 1)%nat.
    intros i Hnz; split.
    + destruct (mod_2_dec i) as [Hmod | Hmod]; rewrite Hmod in Hnz.
      * unfold seq_zero, const, equiv, zero in Hnz; simpl in Hnz; congruence.
      * rewrite Nat.mod_eq in Hmod; auto; lia.
    + destruct (i mod 2).
      * unfold seq_zero, const, equiv, zero in Hnz; simpl in Hnz; congruence.
      * reflexivity.
  - exists (fun i => i * 2 + 1)%nat, (fun i => i / 2)%nat.
    intros i Hnz; split.
    + rewrite Nat.add_comm, Nat.div_add; auto.
    + rewrite Nat.add_comm, Nat.mod_add, Nat.div_add; auto; reflexivity.
Qed.

Lemma seq_union_zero_r {A : Type} (a : nat -> option A) :
  seq_union a seq_zero === a.
Proof. rewrite seq_union_comm; apply seq_union_zero_l. Qed.

Instance Proper_seq_product (A : Type) (M : Monoid A)
  : Proper (seq_bijection_upto_0 ==> seq_bijection_upto_0 ==> seq_bijection_upto_0) (@seq_product A M).
Proof.
  intros s1 s1' [[a [b H0]] [c [d H1]]] s2 s2' [[e [f H2]] [g [h H3]]].
  split.
  - exists (fun n => let (i, j) := nat_f n in nat_g (a i, e j)).
    exists (fun n => let (i, j) := nat_f n in nat_g (b i, f j)).
    intros i Hnz; unfold seq_product in Hnz; split.
    + destruct (nat_f i) eqn: Hi; rewrite nat_f_g.
      assert (Hs1: ~ s1 n === zero).
      { destruct (s1 n); auto.
        unfold equiv, zero; simpl; congruence. }
      destruct (H0 _ Hs1) as [Hba ?]; rewrite Hba.
      assert (Hs2: ~ s2 n0 === zero).
      { destruct (s2 n0); auto.
        unfold equiv, zero; simpl; congruence.
        rewrite option_mult_unit_r in Hnz; congruence. }
      destruct (H2 _ Hs2) as [Hfe ?]; rewrite Hfe.
      rewrite <- Hi, nat_g_f; reflexivity.
    + unfold seq_product; destruct (nat_f i) eqn: Hi.
      rewrite nat_f_g; unfold equiv in *.
      assert (Hs1: ~ s1 n === zero).
      { destruct (s1 n); auto.
        unfold equiv, zero; simpl; congruence. }
      destruct (H0 _ Hs1) as [? Heq]; rewrite Heq; clear Heq.
      assert (Hs2: ~ s2 n0 === zero).
      { destruct (s2 n0); auto.
        unfold equiv, zero; simpl; congruence.
        rewrite option_mult_unit_r in Hnz; congruence. }
      destruct (H2 _ Hs2) as [? Heq]; rewrite Heq; reflexivity.
  - exists (fun n => let (i, j) := nat_f n in nat_g (c i, g j)).
    exists (fun n => let (i, j) := nat_f n in nat_g (d i, h j)).
    intros i Hnz;  unfold seq_product in Hnz; split.
    + destruct (nat_f i) eqn: Hi; rewrite nat_f_g.
      assert (Hs1: ~ s1' n === zero).
      { destruct (s1' n); auto.
        unfold equiv, zero; simpl; congruence. }
      destruct (H1 _ Hs1) as [Hdc ?]; rewrite Hdc.
      assert (Hs2: ~ s2' n0 === zero).
      { destruct (s2' n0); auto.
        unfold equiv, zero; simpl; congruence.
        rewrite option_mult_unit_r in Hnz; congruence. }
      destruct (H3 _ Hs2) as [Hhg ?]; rewrite Hhg.
      rewrite <- Hi, nat_g_f; reflexivity.
    + unfold seq_product; destruct (nat_f i) eqn: Hi.
      rewrite nat_f_g; unfold equiv in *.
      assert (Hs1: ~ s1' n === zero).
      { destruct (s1' n); auto.
        unfold equiv, zero; simpl; congruence. }
      destruct (H1 _ Hs1) as [? Heq]; rewrite Heq; clear Heq.
      assert (Hs2: ~ s2' n0 === zero).
      { destruct (s2' n0); auto.
        unfold equiv, zero; simpl; congruence.
        rewrite option_mult_unit_r in Hnz; congruence. }
      destruct (H3 _ Hs2) as [? Heq]; rewrite Heq; reflexivity.
Qed.

Lemma seq_product_assoc {A : Type} {M : Monoid A} (L : MonoidLaws M) (a b c : nat -> option A) :
  seq_product M (seq_product M a b) c === seq_product M a (seq_product M b c).
Proof.
  set (f := fun n => let (n', k) := nat_f n in
                  let (i, j) := nat_f n' in
                  nat_g (i, nat_g (j, k))).
  set (g := fun n => let (i, n') := nat_f n in
                  let (j, k) := nat_f n' in
                  nat_g (nat_g (i, j), k)).
  unfold seq_product; split.
  - exists f, g; unfold f, g.
    intros i Hnz; split; destruct (nat_f i) eqn:Hi;
      destruct (nat_f n) eqn:Hn; rewrite 2!nat_f_g.
    + rewrite <- Hn, nat_g_f, <- Hi, nat_g_f; reflexivity.
    + apply option_mult_assoc; auto.
  - exists g, f; unfold f, g.
    intros i Hnz; split; destruct (nat_f i) eqn:Hi;
      destruct (nat_f n0) eqn:Hn0; rewrite 2!nat_f_g.
    + rewrite <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
    + rewrite option_mult_assoc; auto; reflexivity.
Qed.

Lemma seq_product_unit_l {A : Type} {M : Monoid A} (L : MonoidLaws M) (a : nat -> option A) :
  seq_product M (seq_one (monoid_unit M)) a === a.
Proof.
  unfold seq_product; split.
  - exists (fun n => snd (nat_f n)), (fun n => nat_g (O, n)).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hf.
      simpl; destruct n.
      * rewrite <- Hf. apply nat_g_f.
      * exfalso; apply Hnz; reflexivity.
    + destruct (nat_f i) eqn:Hf; simpl; destruct n.
      * simpl; unfold option_mult; destruct (a n0); try reflexivity.
        unfold equiv; f_equal; apply monoid_lunit.
      * exfalso; apply Hnz; reflexivity.
  - exists (fun n => nat_g (O, n)), (fun n => snd (nat_f n)).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hf; rewrite nat_f_g; reflexivity.
    + rewrite nat_f_g; unfold option_mult; simpl.
      destruct (a i); try reflexivity; unfold equiv; f_equal.
      rewrite monoid_lunit; auto.
Qed.

Lemma seq_product_unit_r {A : Type} {M : Monoid A} (L : MonoidLaws M) (a : nat -> option A) :
  seq_product M a (seq_one (monoid_unit M)) === a.
Proof.
  unfold seq_product; split.
  - exists (fun n => fst (nat_f n)), (fun n => nat_g (n, O)).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hf; simpl; destruct n0.
      * rewrite <- Hf; apply nat_g_f.
      * exfalso; apply Hnz, option_mult_unit_r.
    + destruct (nat_f i) eqn:Hf; simpl; destruct n0.
      * unfold option_mult; simpl.
        destruct (a n); try reflexivity.
        unfold equiv; f_equal; apply monoid_runit.
      * exfalso; apply Hnz, option_mult_unit_r.
  - exists (fun n => nat_g (n, O)), (fun n => fst (nat_f n)).
    intros i Hnz; split.
    + rewrite nat_f_g; reflexivity.
    + rewrite nat_f_g; simpl.
      destruct (a i); try reflexivity.
      unfold equiv, option_mult; f_equal.
      rewrite monoid_runit; auto.
Qed.

Lemma seq_product_union'_distr_l {A : Type} (M : Monoid A) (a b c : nat -> option A) :
  seq_product M a (seq_union' b c) === seq_union' (seq_product M a b) (seq_product M a c).
Proof.
  unfold seq_union', seq_flatten, seq_product.
  set (f := fun n => let (i, n') := nat_f n in
                  let (j, k) := nat_f n' in
                  match j with
                  | O => nat_g (O, nat_g (i, k))
                  | S O => nat_g (S O, nat_g (i, k))
                  | _ => O
                  end).
  set (g := fun n => let (i, n') := nat_f n in
                  let (j, k) := nat_f n' in
                  match i with
                  | O => nat_g (j, nat_g (O, k))
                  | S O => nat_g (j, nat_g (S O, k))
                  | _ => O
                  end).
  split.
  - exists f, g; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi, (nat_f n0) eqn:Hn0.
      destruct n1.
      * rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
      * destruct n1.
        -- rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
        -- rewrite option_mult_unit_r in Hnz;
             unfold equiv, zero in Hnz; simpl in Hnz; congruence.
    + destruct (nat_f i) eqn:Hi, (nat_f n0) eqn:Hn0.
      destruct n1.
      * rewrite 2!nat_f_g; reflexivity.
      * destruct n1.
        -- rewrite 2!nat_f_g; reflexivity.
        -- rewrite option_mult_unit_r in Hnz;
             unfold equiv, zero in Hnz; simpl in Hnz; congruence.
  - exists g, f; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi, (nat_f n0) eqn:Hn0.
      destruct n.
      * rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
    + destruct (nat_f i) eqn:Hi, (nat_f n0) eqn:Hn0.
      destruct n.
      * rewrite 2!nat_f_g; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
Qed.

Lemma seq_product_union_distr_l {A : Type} (M : Monoid A) (a b c : nat -> option A) :
  seq_product M a (seq_union b c) === seq_union (seq_product M a b) (seq_product M a c).
Proof.
  symmetry.
  rewrite seq_union_seq_union'.
  symmetry.
  cut (seq_product M a (seq_union b c) === seq_product M a (seq_union' b c)).
  { intro H; rewrite H; clear H; apply seq_product_union'_distr_l. }
  apply Proper_seq_product.
  - reflexivity.
  - apply seq_union_seq_union'.
Qed.

Lemma seq_product_union'_distr_r {A : Type} (M : Monoid A) (a b c : nat -> option A) :
  seq_product M (seq_union' a b) c === seq_union' (seq_product M a c) (seq_product M b c).
Proof.
  unfold seq_union', seq_flatten, seq_product.
  set (f := fun n => let (n', k) := nat_f n in
                  let (i, j) := nat_f n' in
                  match i with
                  | O => nat_g (O, nat_g (j, k))
                  | S O => nat_g (S O, nat_g (j, k))
                  | _ => O
                  end).
  set (g := fun n => let (i, n') := nat_f n in
                  let (j, k) := nat_f n' in
                  match i with
                  | O => nat_g (nat_g (O, j), k)
                  | S O => nat_g (nat_g (S O, j), k)
                  | _ => O
                  end).
  split.
  - exists f, g; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi, (nat_f n) eqn:Hn.
      destruct n1.
      * rewrite 2!nat_f_g, <- Hn, nat_g_f, <- Hi, nat_g_f; reflexivity.
      * destruct n1.
        -- rewrite 2!nat_f_g, <- Hn, nat_g_f, <- Hi, nat_g_f; reflexivity.
        -- unfold option_mult, equiv, zero in Hnz; simpl in Hnz; congruence.
    + destruct (nat_f i) eqn:Hi, (nat_f n) eqn:Hn.
      destruct n1.
      * rewrite 2!nat_f_g; reflexivity.
      * destruct n1.
        -- rewrite 2!nat_f_g; reflexivity.
        --  unfold option_mult, equiv, zero in Hnz; simpl in Hnz; congruence.
  - exists g, f; unfold f, g.
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi, (nat_f n0) eqn:Hn0.
      destruct n.
      * rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
    + destruct (nat_f i) eqn:Hi, (nat_f n0) eqn:Hn0.
      destruct n.
      * rewrite 2!nat_f_g; reflexivity.
      * destruct n.
        -- rewrite 2!nat_f_g; reflexivity.
        -- unfold equiv, zero in Hnz; simpl in Hnz; congruence.
Qed.

Lemma seq_product_union_distr_r {A : Type} (M : Monoid A) (a b c : nat -> option A) :
  seq_product M (seq_union a b) c === seq_union (seq_product M a c) (seq_product M b c).
Proof.
  symmetry.
  rewrite seq_union_seq_union'.
  symmetry.
  cut (seq_product M (seq_union a b) c === seq_product M (seq_union' a b) c).
  { intro H; rewrite H; clear H; apply seq_product_union'_distr_r. }
  apply Proper_seq_product.
  - apply seq_union_seq_union'.
  - reflexivity.
Qed.

Program Instance Semiring_seq (A : Type) (M : Monoid A) (L : MonoidLaws M)
  : Semiring (nat -> option A) :=
  {| sr_plus := seq_union
   ; sr_zero := seq_zero
   ; sr_mult := seq_product M
   ; sr_one := seq_one (monoid_unit M)
  |}.
Next Obligation. apply seq_union_assoc. Qed.
Next Obligation. apply seq_union_zero_l. Qed.
Next Obligation. apply seq_union_zero_r. Qed.
Next Obligation. apply seq_union_comm. Qed.
Next Obligation. apply seq_product_assoc; auto. Qed.
Next Obligation. apply seq_product_unit_l; auto. Qed.
Next Obligation. apply seq_product_unit_r; auto. Qed.
Next Obligation. apply seq_product_union_distr_l. Qed.
Next Obligation. apply seq_product_union_distr_r. Qed.
Next Obligation. rewrite seq_product_zero_l; reflexivity. Qed.
Next Obligation. rewrite seq_product_zero_r; reflexivity. Qed.

(* Yields indices in reverse order. *)
(*    (i, ixs) --> (((fi . gn) ...) . g1) . g0 *)
Fixpoint seq_product_n_ixs (n i : nat) : nat * list nat :=
  match n with
  | O => (i, [])
  | S n' =>
    let (i', j') := nat_f i in
    let (i'', ixs) := seq_product_n_ixs n' i' in
    (i'', j' :: ixs)
  end.

Fixpoint seq_product_n_ixs_inverse (i : nat) (ixs : list nat) : nat :=
  match ixs with
  | nil => i
  | j :: ixs' => nat_g (seq_product_n_ixs_inverse i ixs', j)
  end.

Lemma seq_product_n_ixs_left_inverse (n i : nat) :
  seq_product_n_ixs_inverse (fst (seq_product_n_ixs n i)) (snd (seq_product_n_ixs n i)) = i.
Proof.
  revert i; induction n; intro i; simpl; try reflexivity.
  destruct (nat_f i) eqn:Hi.
  destruct (seq_product_n_ixs n n0) eqn:H.
  simpl.
  specialize (IHn n0). rewrite H in IHn; simpl in IHn.
  rewrite IHn.
  rewrite <- Hi, nat_g_f; reflexivity.
Qed.

Lemma seq_product_n_ixs_right_inverse (i : nat) (ixs : list nat) :
  seq_product_n_ixs (length ixs) (seq_product_n_ixs_inverse i ixs) = (i, ixs).
Proof.
  revert i; induction ixs; intro i; simpl; try reflexivity.
  rewrite nat_f_g.
  rewrite IHixs; reflexivity.
Qed.

Fixpoint concat_ixs {A : Type} (M : Monoid A)
         (f g : nat -> option A) (i : nat) (ixs : list nat) : option A :=
  match ixs with
  | nil => f i
  | i' :: ixs' => option_mult M (concat_ixs M f g i ixs') (g i')
  end.

Definition concat_ixs' {A : Type} (M : Monoid A)
           (f g : nat -> option A) (i : nat) (ixs : list nat) : option A :=
  fold_right (fun j acc => option_mult M acc (g j)) (f i) ixs.

Lemma concat_ixs_spec {A : Type} (M : Monoid A)
      (f g : nat -> option A) (i : nat) (ixs : list nat) :
  concat_ixs M f g i ixs = concat_ixs' M f g i ixs.
Proof.
  unfold concat_ixs'.
  induction ixs; simpl; try reflexivity.
  rewrite IHixs. reflexivity.
Qed.

Lemma seq_product_n_ixs_inverse_spec {A : Type} (M : Monoid A) (f g : nat -> option A) (i : nat) (ixs : list nat) :
  seq_product_n M f g (length ixs) (seq_product_n_ixs_inverse i ixs) = concat_ixs M f g i ixs.
Proof.
  induction ixs; simpl; try congruence.
  unfold seq_product.
  rewrite nat_f_g.
  rewrite IHixs; reflexivity.
Qed.

Lemma seq_product_n_ixs_spec {A : Type} (M : Monoid A) (f g : nat -> option A) (n i : nat) :
  seq_product_n M f g n i =
  concat_ixs M f g (fst (seq_product_n_ixs n i)) (snd (seq_product_n_ixs n i)).
Proof.
  revert i; induction n; intro i; simpl; try reflexivity.
  unfold seq_product.
  destruct (nat_f i) eqn:Hi; simpl.
  destruct (seq_product_n_ixs n n0) eqn:H.
  simpl.
  specialize (IHn n0); rewrite H in IHn.
  simpl in *.
  rewrite IHn; reflexivity.
Qed.

Lemma seq_product_n_ixs_length (n i j : nat) (l : list nat) :
  seq_product_n_ixs n j = (i, l) ->
  n = length l.
Proof.
  revert i j l.
  induction n; simpl; intros i j l Heq.
  - inversion Heq; subst; reflexivity.
  - destruct (nat_f j) eqn:Hj.
    destruct (seq_product_n_ixs n n0) eqn:Hn.
    inversion Heq; subst.
    apply IHn in Hn; subst.
    reflexivity.
Qed.

(* Yields indices in correct order. *)
(*    (ixs, i) --> g0 . (g1 ... (gn . fi)) *)
Fixpoint seq_product_n'_ixs (n j : nat) : list nat * nat :=
  match n with
  | O => ([], j)
  | S n' =>
    let (i', j') := nat_f j in
    let (ixs, j'') := seq_product_n'_ixs n' j' in
    (i' :: ixs, j'')
  end.

Fixpoint seq_product_n'_ixs_inverse (ixs : list nat) (j : nat) : nat :=
  match ixs with
  | nil => j
  | i :: ixs' => nat_g (i, seq_product_n'_ixs_inverse ixs' j)
  end.

Lemma seq_product_n'_ixs_left_inverse (n i : nat) :
  seq_product_n'_ixs_inverse (fst (seq_product_n'_ixs n i)) (snd (seq_product_n'_ixs n i)) = i.
Proof.
  revert i; induction n; intro i; simpl; try reflexivity.

  destruct (nat_f i) eqn:Hi.
  destruct (seq_product_n'_ixs n n1) eqn:H.
  simpl.
  specialize (IHn n1). rewrite H in IHn; simpl in IHn.
  rewrite IHn, <- Hi, nat_g_f; reflexivity.
Qed.

Lemma seq_product_n'_ixs_right_inverse (ixs : list nat) (j : nat) :
  seq_product_n'_ixs (length ixs) (seq_product_n'_ixs_inverse ixs j) = (ixs, j).
Proof.
  revert j; induction ixs; intro j; simpl; try reflexivity.
  rewrite nat_f_g.
  rewrite IHixs; reflexivity.
Qed.

Definition concat_ixs'' {A : Type} (M : Monoid A)
           (f g : nat -> option A) (ixs : list nat) (j : nat) : option A :=
  fold_right (fun i acc => option_mult M (g i) acc) (f j) ixs.

Lemma seq_product_n'_ixs_inverse_spec {A : Type} (M : Monoid A)
      (f g : nat -> option A) (ixs : list nat) (j : nat) :
  seq_product_n'' M f g (length ixs) (seq_product_n'_ixs_inverse ixs j) =
  concat_ixs'' M f g ixs j.
Proof.
  induction ixs; simpl; try reflexivity.
  unfold seq_product.
  rewrite nat_f_g.
  rewrite IHixs; reflexivity.
Qed.

Lemma seq_product_n'_ixs_spec {A : Type} (M : Monoid A) (f g : nat -> option A) (n j : nat) :
  seq_product_n'' M f g n j =
  concat_ixs'' M f g (fst (seq_product_n'_ixs n j)) (snd (seq_product_n'_ixs n j)).
Proof.
  revert j; induction n; intro j; simpl; try reflexivity.
  unfold seq_product.
  destruct (nat_f j) eqn:Hj; simpl.
  destruct (seq_product_n'_ixs n n1) eqn:H.
  simpl.
  specialize (IHn n1); rewrite H in IHn.
  simpl in *.
  rewrite IHn; reflexivity.
Qed.

Lemma seq_product_n'_ixs_length (n i j : nat) (l : list nat) :
  seq_product_n'_ixs n j = (l, i) ->
  n = length l.
Proof.
  revert i j l.
  induction n; simpl; intros i j l Heq.
  - inversion Heq; subst; reflexivity.
  - destruct (nat_f j) eqn:Hj.
    destruct (seq_product_n'_ixs n n1) eqn:Hn.
    inversion Heq; subst.
    apply IHn in Hn; subst.
    reflexivity.
Qed.

Lemma ix_tree_product_collapse_ix_tree {A : Type} (M : Monoid A)
      (f g : nat -> option A) (t : ix_tree) :
  left_associated t ->
  ix_tree_product M f g t = seq_product_n' M f g (ix_tree_depth t) (collapse_ix_tree t).
Proof.
  induction 1; simpl; auto.
  unfold seq_product.
  rewrite nat_f_g, Nat.max_0_r, IHleft_associated; reflexivity.
Qed.

Lemma ix_tree_product'_collapse_ix_tree {A : Type} (M : Monoid A)
      (f g : nat -> option A) (t : ix_tree) :
  right_associated t ->
  ix_tree_product' M f g t = seq_product_n'' M f g (ix_tree_depth t) (collapse_ix_tree t).
Proof.
  induction 1; simpl; auto.
  unfold seq_product.
  rewrite nat_f_g, IHright_associated; reflexivity.
Qed.

Lemma ix_tree_product_mk_ix_tree {A : Type} (M : Monoid A)
      (f g : nat -> option A) (n i : nat) :
  ix_tree_product M f g (mk_ix_tree n i) = seq_product_n' M f g n i.
Proof.
  revert i; induction n; intro i; simpl; auto.
  unfold seq_product.
  destruct (nat_f i); simpl.
  rewrite IHn; reflexivity.
Qed.

Lemma ix_tree_product'_mk_ix_tree' {A : Type} (M : Monoid A)
      (f g : nat -> option A) (n i : nat) :
  ix_tree_product' M f g (mk_ix_tree' n i) = seq_product_n'' M f g n i.
Proof.
  revert i; induction n; intro i; simpl; auto.
  unfold seq_product.
  destruct (nat_f i); simpl.
  rewrite IHn; reflexivity.
Qed.

Lemma seq_reps_plus_seq_reps_plus' {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) :
  seq_reps_plus M f === seq_reps_plus' M f.
Proof.
  split.
  - exists (fun n => let (iters, k) := nat_f n in
             nat_g (iters, collapse_ix_tree
                             (right_associate (mk_ix_tree iters k)))).
    exists (fun n => let (iters, k) := nat_f n in
             nat_g (iters, collapse_ix_tree
                             (left_associate (mk_ix_tree' iters k)))).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      rewrite nat_f_g.
      rewrite <- nat_g_f, Hi.
      repeat f_equal.
      replace (mk_ix_tree'
                 n (collapse_ix_tree (right_associate (mk_ix_tree n n0)))) with
          (mk_ix_tree'
             (ix_tree_depth (right_associate (mk_ix_tree n n0)))
             (collapse_ix_tree (right_associate (mk_ix_tree n n0)))).
      * rewrite mk_ix_tree'_collapse.
        -- rewrite left_right_associate.
           ++ apply collapse_mk_ix_tree.
           ++ apply mk_ix_tree_left_associated.
        -- apply right_associate_spec, mk_ix_tree_left_associated.
      * f_equal.
        rewrite right_associate_depth.
        -- apply mk_ix_tree_depth.
        -- apply mk_ix_tree_left_associated.
    + unfold seq_reps_plus, seq_reps_plus', seq_flatten.
      destruct (nat_f i) eqn:Hi.
      rewrite nat_f_g.
      unfold seq_reps_n_plus, seq_reps_n_plus', equiv.
      rewrite seq_product_n_seq_product_n'.
      replace (seq_product_n' M f f n n0) with
          (seq_product_n' M f f n (collapse_ix_tree (mk_ix_tree n n0))).
      2: { rewrite collapse_mk_ix_tree; reflexivity. }
      set (t := mk_ix_tree n n0).
      rewrite <- (mk_ix_tree_depth n n0).
      rewrite <- ix_tree_product_collapse_ix_tree.
      2: { apply mk_ix_tree_left_associated. }
      fold t.
      rewrite <- right_associate_depth.
      2: { apply mk_ix_tree_left_associated. }
      rewrite <- ix_tree_product'_collapse_ix_tree.
      * apply ix_tree_product_right_associate; auto.
        apply mk_ix_tree_left_associated.
      * apply right_associate_spec, mk_ix_tree_left_associated.
  - exists (fun n => let (iters, k) := nat_f n in
             nat_g (iters, collapse_ix_tree
                             (left_associate (mk_ix_tree' iters k)))).
    exists (fun n => let (iters, k) := nat_f n in
             nat_g (iters, collapse_ix_tree
                             (right_associate (mk_ix_tree iters k)))).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      rewrite nat_f_g.
      rewrite <- nat_g_f, Hi.
      repeat f_equal.
      replace (mk_ix_tree
                 n (collapse_ix_tree (left_associate (mk_ix_tree' n n0)))) with
          (mk_ix_tree
             (ix_tree_depth (left_associate (mk_ix_tree' n n0)))
             (collapse_ix_tree (left_associate (mk_ix_tree' n n0)))).
      * rewrite mk_ix_tree_collapse.
        -- rewrite right_left_associate.
           ++ apply collapse_mk_ix_tree'.
           ++ apply mk_ix_tree'_right_associated.
        -- apply left_associate_spec, mk_ix_tree'_right_associated.
      * f_equal.
        rewrite left_associate_depth.
        -- apply mk_ix_tree'_depth.
        -- apply mk_ix_tree'_right_associated.
    + unfold seq_reps_plus, seq_reps_plus', seq_flatten.
      unfold seq_reps_n_plus, seq_reps_n_plus', equiv.
      destruct (nat_f i) eqn:Hi.
      rewrite nat_f_g.
      rewrite seq_product_n_seq_product_n'.
      replace (seq_product_n'' M f f n n0) with
          (seq_product_n'' M f f n (collapse_ix_tree (mk_ix_tree' n n0))).
      2: { rewrite collapse_mk_ix_tree'; reflexivity. }
      rewrite <- ix_tree_product'_mk_ix_tree'.
      rewrite collapse_mk_ix_tree'.
      set (t := mk_ix_tree' n n0).
      rewrite <- (mk_ix_tree'_depth n n0).
      fold t.
      rewrite <- left_associate_depth.
      2: { apply mk_ix_tree'_right_associated. }
      rewrite <- ix_tree_product_collapse_ix_tree.
      2: { apply left_associate_spec, mk_ix_tree'_right_associated. }
      apply ix_tree_product_left_associate; auto.
      apply mk_ix_tree'_right_associated.
Qed.

Lemma seq_product_n_nth_prod {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f g : nat -> option A) (n : nat) :
  seq_product_n M f g n = nth_prod f g n.
Proof. reflexivity. Qed.

Lemma seq_reps_n_nth_rep {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (n : nat) :
  seq_reps_n M f n === nth_rep f n.
Proof. reflexivity. Qed.

(* It would be nice to prove this for semirings in general but we need
   to show that seq_flatten computes the big sum.  *)
Lemma seq_reps_zero {A : Type} (M : Monoid A) (L : MonoidLaws M) :
  seq_reps M sr_zero === sr_one.
Proof.
  unfold seq_reps, seq_flatten; simpl; split.
  - exists (fun n => snd (nat_f n)), (fun n => nat_g (O, n)).
    intros i Hnz; destruct (nat_f i) eqn:Hi; destruct n.
    + split; simpl; try reflexivity; rewrite <- Hi, nat_g_f; reflexivity.
    + exfalso; apply Hnz; simpl.
      rewrite seq_product_zero_r; reflexivity.
  - exists (fun n => nat_g (O, n)), (fun n => snd (nat_f n)).
    intros i Hnz; rewrite nat_f_g; simpl; split; reflexivity.
Qed.

Lemma seq_product_option_mult_comm {A : Type} (M : Monoid A) (L: MonoidLaws M)
      (x : option A) (s1 s2 : nat -> option A) :
  seq_product M (option_mult M x ∘ s1) s2 = option_mult M x ∘ (seq_product M s1 s2).
Proof.
  apply functional_extensionality; intro n.
  unfold compose, seq_product.
  destruct (nat_f n); destruct x; apply option_mult_assoc; auto.
Qed.

Lemma seq_union_comm_4 {A : Type} (s1 s2 s3 s4 : nat -> option A) :
  seq_union (seq_union s1 s2) (seq_union s3 s4) ===
            seq_union (seq_union s1 s3) (seq_union s2 s4).
Proof.
  rewrite <- seq_union_assoc, (seq_union_comm (seq_union s1 s2) s3).
  rewrite <- 2!seq_union_assoc, (seq_union_comm s1 s3); reflexivity.
Qed.

Lemma seq_union_compose {A B : Type} (s1 s2 : nat -> A) (f : A -> B) :
  seq_union (f ∘ s1) (f ∘ s2) = f ∘ seq_union s1 s2.
Proof.
  apply functional_extensionality; intro n; unfold compose, seq_union.
  destruct (n mod 2); reflexivity.
Qed.

Lemma seq_bijection_upto_0_exists_some {A : Type} (s1 s2 : nat -> option A) (x : A) (i : nat) :
  s1 === s2 ->
  s1 i === Some x ->
  exists j, s2 j === Some x.
Proof.
  intros [[f [g Hinj]] _] Hi.
  unfold equiv in *; exists (f i).
  assert (H: s1 i <> None).
  { congruence. }
  destruct (Hinj i H) as [_ H0]. rewrite <- H0; auto.
Qed.

(** seq_reps_n f n i is:

   0    1    2
0  {ϵ},    {},    {}, ...
1  ϵf 0,  ϵf 1,  ϵf 2, ...
2  ϵff 0, ϵff 1, ϵff 2, ...
...
 *)

(** seq_product f g is flatten:

    0      1      2
0 f0.g0, f0.g1, f0.g2
1 f1.g0, f1.g1, f1.g2
2 f2.g0, f2.g1, f2.g2

    0         1        2
0 fg(0,0), fg(0,1), fg(0,2)
1 fg(1,0), fg(1,1), fg(1,2)
2 fg(2,0), fg(2,1), fg(2,2)

*)

(** seq_product f f* is flatten:

    0         1        2
0 ff*(0,0), ff*(0,1), ff*(0,2)
1 ff*(1,0), ff*(1,1), ff*(1,2)
2 ff*(2,0), ff*(2,1), ff*(2,2)

 *)

Lemma seq_product_n_ixs_zero {A : Type} (M : Monoid A) (s : nat -> option A) n i l :
  seq_product_n_ixs (length l) i = (n, l) ->
  (n = 0)%nat \/ seq_reps_n M s (length l) i === zero.
Proof.
  revert n i.
  induction l; simpl; intros n i H.
  - inversion H; subst; clear H.
    destruct n; auto; right; reflexivity.
  - destruct (nat_f i) eqn:Hi.
    destruct (seq_product_n_ixs (length l) n0) eqn:Hln0.
    inversion H; subst; clear H.
    apply IHl in Hln0.
    destruct Hln0; auto; right.
    unfold seq_product.
    rewrite Hi, H; reflexivity.
Qed.

Lemma seq_product_n'_ixs_zero {A : Type} (M : Monoid A) (s : nat -> option A) n i l :
  seq_product_n'_ixs (length l) i = (l, n) ->
  (n = 0)%nat \/ seq_reps_n' M s (length l) i === zero.
Proof.
  revert n i.
  induction l; simpl; intros n i H.
  - inversion H; subst; clear H.
    destruct n; auto; right; reflexivity.
  - destruct (nat_f i) eqn:Hi.
    destruct (seq_product_n'_ixs (length l) n1) eqn:Hln1.
    inversion H; subst; clear H.
    apply IHl in Hln1.
    destruct Hln1; auto; right.
    unfold seq_reps_n' in *. simpl.
    unfold seq_product.
    rewrite Hi, H.
    apply option_mult_unit_r.
Qed.

Lemma nat_iter_seq_product' {A : Type} (M : Monoid A) (L : MonoidLaws M)
            (s : nat -> option A) l n2 n :
  seq_product_n_ixs (length l) n2 = (O, l) ->
  Nat.iter (length l) (fun f' : nat -> option A => seq_product M f' s) s
           (seq_product_n_ixs_inverse n l) ===
           option_mult M (s n)
           (Nat.iter (length l) (fun f' : nat -> option A => seq_product M f' s)
                     (seq_one (monoid_unit M)) n2).
Proof.
  revert n2 n.
  induction l; simpl; intros n2 n H0.
  - inversion H0; subst; clear H0.
    unfold equiv; destruct (s n).
    + simpl.
      unfold option_mult.
      f_equal.
      destruct L; auto.
    + reflexivity.
  - unfold seq_product.
    rewrite nat_f_g.
    destruct (nat_f n2) eqn:Nn2.
    destruct (seq_product_n_ixs (length l) n0) eqn:Hln0.
    inversion H0; subst; clear H0.
    eapply IHl in Hln0.
    unfold equiv.
    rewrite <- option_mult_assoc; auto.
    rewrite Hln0; reflexivity.
Qed.

Lemma nat_iter_seq_product {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (s : nat -> option A) l n0 n1 :
  seq_product_n_ixs (length l) n0 = (n1, l) ->
  Nat.iter (length l) (fun f' : nat -> option A => seq_product M f' s) s n0 ===
           option_mult M (s n1)
           (Nat.iter (length l) (fun f' : nat -> option A => seq_product M f' s)
                     (seq_one (monoid_unit M)) (seq_product_n_ixs_inverse 0 l)).
Proof.
  revert n0 n1.
  induction l; simpl; intros n0 n1 H0.
  - inversion H0; subst; clear H0.
    destruct (s n1).
    + unfold option_mult.
      unfold equiv. f_equal.
      destruct L; auto.
    + reflexivity.
  - unfold seq_product.
    destruct (nat_f n0) eqn:Hn0.
    destruct (seq_product_n_ixs (length l) n) eqn:Hln.
    inversion H0; subst; clear H0.
    apply IHl in Hln.
    rewrite nat_f_g.
    rewrite Hln.
    unfold equiv.
    rewrite option_mult_assoc; auto.
Qed.

Lemma seq_product_seq_reps_r_seq_reps_plus {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (s : nat -> option A) :
  seq_product M s (seq_reps M s) === seq_reps_plus M s.
Proof.
  split.
  - exists (fun n => let (i, k) := nat_f n in
             let (iters, j) := nat_f k in
             let (_, ixs) := seq_product_n_ixs iters j in
             nat_g (iters, seq_product_n_ixs_inverse i ixs)).
    exists (fun n => let (iters, j) := nat_f n in
             let (i, ixs) := seq_product_n_ixs iters j in
             let k := seq_product_n_ixs_inverse O ixs in
             nat_g (i, nat_g (iters, k))).
    intros i Hnz; simpl; split.
    + destruct (nat_f i) eqn:Hi.
      destruct (nat_f n0) eqn:Hn0.
      destruct (seq_product_n_ixs n1 n2) eqn:Hn12.
      generalize (seq_product_n_ixs_length _ _ Hn12); intros; subst.
      unfold seq_product, seq_reps, seq_flatten in Hnz.
      rewrite Hi, Hn0 in Hnz.
      destruct (seq_product_n_ixs_zero M s n2 Hn12); subst.
      2: { exfalso; apply Hnz; rewrite H; apply option_mult_unit_r. }
      rewrite nat_f_g.
      rewrite seq_product_n_ixs_right_inverse.
      replace l with (snd (seq_product_n_ixs (length l) n2))
        by (rewrite Hn12; reflexivity).
      replace O with (fst (seq_product_n_ixs (length l) n2))
        by (rewrite Hn12; reflexivity).
      rewrite seq_product_n_ixs_left_inverse.
      rewrite Hn12; simpl.
      rewrite <- Hn0, nat_g_f.
      rewrite  <- Hi, nat_g_f; reflexivity.
    + unfold seq_product, seq_reps, seq_reps_plus, seq_flatten.
      destruct (nat_f i) eqn:Hi.
      destruct (nat_f n0) eqn:Hn0.
      destruct (seq_product_n_ixs n1 n2) eqn:Hn12.
      generalize (seq_product_n_ixs_length _ _ Hn12); intros; subst.
      rewrite nat_f_g.
      unfold seq_reps_n_plus, seq_reps_n, seq_product_n.
      symmetry.
      destruct (seq_product_n_ixs_zero M s n2 Hn12); subst.
      2: { unfold seq_product, seq_reps, seq_flatten in Hnz.
           rewrite Hi, Hn0 in Hnz.
           exfalso; apply Hnz; rewrite H. apply option_mult_unit_r. }
      apply nat_iter_seq_product'; auto.
  - exists (fun n => let (iters, j) := nat_f n in
             let (i, ixs) := seq_product_n_ixs iters j in
             let k := seq_product_n_ixs_inverse O ixs in
             nat_g (i, nat_g (iters, k))).
    exists (fun n => let (i, k) := nat_f n in
             let (iters, j) := nat_f k in
             let (_, ixs) := seq_product_n_ixs iters j in
             nat_g (iters, seq_product_n_ixs_inverse i ixs)).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      destruct (seq_product_n_ixs n n0) eqn:Hnn0.
      simpl.
      rewrite 2!nat_f_g.
      generalize (seq_product_n_ixs_length _ _ Hnn0); intros; subst.
      rewrite seq_product_n_ixs_right_inverse.
      replace l with (snd (seq_product_n_ixs (length l) n0))
        by (rewrite Hnn0; reflexivity).
      replace n1 with (fst (seq_product_n_ixs (length l) n0))
        by (rewrite Hnn0; reflexivity).
      rewrite seq_product_n_ixs_left_inverse.
      rewrite Hnn0.
      simpl; rewrite <- Hi, nat_g_f; reflexivity.
    + unfold seq_reps_plus, seq_reps, seq_flatten, seq_product.
      destruct (nat_f i) eqn:Hi.
      destruct (seq_product_n_ixs n n0) eqn:Hnn0.
      rewrite 2!nat_f_g.
      unfold seq_reps_n_plus.
      unfold seq_reps_n.
      unfold seq_product_n.
      generalize (seq_product_n_ixs_length _ _ Hnn0); intros; subst.
      apply nat_iter_seq_product; auto.
Qed.

Lemma seq_product_n'_ixs_option_mult {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (s : nat -> option A) l n2 n0 :
  seq_product_n'_ixs (length l) n2 = (l, 0%nat) ->
  option_mult M (seq_product_n'' M (seq_one (monoid_unit M)) s (length l) n2) (s n0) ===
  seq_product_n'' M s s (length l) (seq_product_n'_ixs_inverse l n0).
Proof.
  revert n2 n0.
  induction l; simpl; intros n2 n0 H0.
  - inversion H0; subst; clear H0; simpl.
    unfold equiv, option_mult.
    destruct (s n0); auto.
    f_equal; destruct L; auto.
  - unfold equiv, seq_product.
    destruct (nat_f n2) eqn:Hn2.
    destruct (seq_product_n'_ixs (length l) n1) eqn:Hln1.
    inversion H0; subst; clear H0.
    eapply IHl in Hln1.
    rewrite nat_f_g.
    rewrite <- Hln1.
    apply option_mult_assoc; auto.
Qed.

Lemma seq_product_n'_ixs_option_mult' {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (s : nat -> option A) l n0 n1 :
  seq_product_n'_ixs (length l) n0 = (l, n1) ->
  seq_product_n'' M s s (length l) n0 =
  option_mult M (seq_product_n'' M (seq_one (monoid_unit M)) s (length l) (seq_product_n'_ixs_inverse l 0)) (s n1).
Proof.
  revert n0 n1; induction l; simpl; intros n0 n1 H0.
  - inversion H0; subst; clear H0.
    destruct (s n1).
    + unfold option_mult; f_equal; destruct L; auto.
    + rewrite option_mult_unit_r; reflexivity.
  - unfold seq_product.
    destruct (nat_f n0) eqn:Hn0.
    destruct (seq_product_n'_ixs (length l) n2) eqn:Hln2.
    inversion H0; subst; clear H0.
    apply IHl in Hln2.
    rewrite Hln2.
    rewrite nat_f_g.
    rewrite option_mult_assoc; auto.
Qed.
  
Lemma seq_product_seq_reps_l_seq_reps_plus {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (s : nat -> option A) :
  seq_product M (seq_reps' M s) s === seq_reps_plus' M s.
Proof.
  split.
  - exists (fun n => let (k, i) := nat_f n in
             let (iters, j) := nat_f k in
             let (ixs, _) := seq_product_n'_ixs iters j in
             nat_g (iters, seq_product_n'_ixs_inverse ixs i)).
    exists (fun n => let (iters, j) := nat_f n in
             let (ixs, i) := seq_product_n'_ixs iters j in
             let k := seq_product_n'_ixs_inverse ixs O in
             nat_g (nat_g (iters, k), i)).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      destruct (nat_f n) eqn:Hn.
      destruct (seq_product_n'_ixs n1 n2) eqn:Hn12.
      generalize (seq_product_n'_ixs_length _ _ Hn12); intros; subst.
      rewrite nat_f_g; simpl.
      rewrite seq_product_n'_ixs_right_inverse.
      destruct (seq_product_n'_ixs_zero M s n2 Hn12); subst.
      2: { unfold seq_product, seq_reps, seq_flatten in Hnz.
           rewrite Hi in Hnz; exfalso; apply Hnz.
           unfold seq_reps', seq_flatten.
           rewrite Hn; simpl; rewrite H; reflexivity. }
      replace l with (fst (seq_product_n'_ixs (length l) n2)) by
          (rewrite Hn12; reflexivity).
      replace O with (snd (seq_product_n'_ixs (length l) n2)) by
          (rewrite Hn12; reflexivity).
      rewrite seq_product_n'_ixs_left_inverse.
      rewrite Hn12. simpl.
      rewrite <- Hn, nat_g_f.
      rewrite <- Hi, nat_g_f; reflexivity.
    + unfold seq_product, seq_reps', seq_reps_plus', seq_flatten.
      destruct (nat_f i) eqn:Hi.
      destruct (nat_f n) eqn:Hn.
      destruct (seq_product_n'_ixs n1 n2) eqn:Hn12.
      generalize (seq_product_n'_ixs_length _ _ Hn12); intros; subst.
      rewrite nat_f_g.
      unfold seq_reps_n', seq_reps_n_plus'.
      destruct (seq_product_n'_ixs_zero M s n2 Hn12); subst.
      2: { unfold seq_product, seq_reps, seq_flatten in Hnz.
           rewrite Hi in Hnz; exfalso; apply Hnz.
           unfold seq_reps', seq_flatten.
           rewrite Hn; simpl; rewrite H; reflexivity. }
      apply seq_product_n'_ixs_option_mult; auto.
  - exists (fun n => let (iters, j) := nat_f n in
             let (ixs, i) := seq_product_n'_ixs iters j in
             let k := seq_product_n'_ixs_inverse ixs O in
             nat_g (nat_g (iters, k), i)).
    exists (fun n => let (k, i) := nat_f n in
             let (iters, j) := nat_f k in
             let (ixs, _) := seq_product_n'_ixs iters j in
             nat_g (iters, seq_product_n'_ixs_inverse ixs i)).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      destruct (seq_product_n'_ixs n n0) eqn:Hnn0.
      generalize (seq_product_n'_ixs_length _ _ Hnn0); intros; subst.
      simpl; rewrite 2!nat_f_g.
      rewrite seq_product_n'_ixs_right_inverse.
      replace l with (fst (seq_product_n'_ixs (length l) n0)) by
          (rewrite Hnn0; reflexivity).
      replace n1 with (snd (seq_product_n'_ixs (length l) n0)) by
          (rewrite Hnn0; reflexivity).
      rewrite seq_product_n'_ixs_left_inverse.
      rewrite Hnn0; simpl.
      rewrite <- Hi, nat_g_f; reflexivity.
    + unfold equiv, seq_product.
      destruct (nat_f i) eqn:Hi.
      destruct (seq_product_n'_ixs n n0) eqn:Hnn0.
      generalize (seq_product_n'_ixs_length _ _ Hnn0); intros; subst.
      rewrite nat_f_g.
      unfold seq_reps', seq_reps_plus'.
      unfold seq_flatten.
      rewrite nat_f_g.
      rewrite Hi.
      unfold seq_reps_n', seq_reps_n_plus'.
      apply seq_product_n'_ixs_option_mult'; auto.
Qed.

Lemma leftmost_0_mk_ix_tree {A : Type} (M : Monoid A) (f : nat -> option A) k n i :
  seq_reps M f k <> None ->
  nat_f k = (n, i) ->
  leftmost 0 (mk_ix_tree n i).
Proof.
  unfold seq_reps, seq_flatten.
  intros Hnz Hk.
  rewrite Hk in Hnz.
  clear Hk. clear k.
  revert Hnz. revert i.
  induction n; simpl; intros i Hnz.
  - destruct i; try constructor.
    exfalso; apply Hnz; reflexivity.
  - unfold seq_product in Hnz.
    destruct (nat_f i) eqn:Hi.
    constructor; apply IHn.
    intro HC.
    apply Hnz.
    rewrite HC; reflexivity.
Qed.

Lemma rightmost_0_mk_ix_tree' {A : Type} (M : Monoid A) (f : nat -> option A) k n i :
  seq_reps' M f k <> None ->
  nat_f k = (n, i) ->
  rightmost 0 (mk_ix_tree' n i).
Proof.
  unfold seq_reps', seq_flatten.
  intros Hnz Hk.
  rewrite Hk in Hnz.
  clear Hk. clear k.
  revert Hnz. revert i.
  induction n; simpl; intros i Hnz.
  - destruct i; try constructor.
    exfalso; apply Hnz; reflexivity.
  - unfold seq_reps_n' in Hnz; simpl in Hnz; unfold seq_product in Hnz.
    destruct (nat_f i) eqn:Hi.
    constructor; apply IHn.
    intro HC.
    apply Hnz.
    unfold seq_reps_n' in *; simpl.
    rewrite HC; apply option_mult_unit_r.
Qed.

Lemma ix_tree_product_cut_left {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (n i : nat) :
  (O < n)%nat ->
  seq_product_n' M (seq_one (monoid_unit M)) f n i <> None ->
  ix_tree_product M (seq_one (monoid_unit M)) f (mk_ix_tree n i) =
  ix_tree_product M f f (cut_left (mk_ix_tree n i)).
Proof.
  revert i; induction n; simpl; intros i Hlt Hnz; try lia.
  unfold seq_product in Hnz.
  destruct (nat_f i) eqn:Hi.
  destruct n; simpl in *.
  - destruct n0; simpl.
    2: { exfalso; apply Hnz; reflexivity. }
    destruct (f n1).
    + unfold option_mult; f_equal; destruct L; auto.
    + apply option_mult_unit_r.
  - rewrite IHn; try lia.
    2: { unfold seq_product in *.
         destruct (nat_f n0) eqn:Hn0.
         intro HC; apply Hnz; rewrite HC; reflexivity. }
    destruct (nat_f n0) eqn:Hn0; reflexivity.
Qed.

Lemma ix_tree_product_cut_left' {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (t : ix_tree) :
  left_associated t ->
  (O < ix_tree_depth t)%nat ->
  leftmost O t ->
  ix_tree_product M (seq_one (monoid_unit M)) f t =
  ix_tree_product M f f (cut_left t).
Proof.
  induction 1; simpl; intros Hlt H0; try lia.
  inversion H0; subst.
  destruct l; simpl.
  - destruct n0; simpl.
    + destruct (f n).
      * unfold option_mult; f_equal; destruct L; auto.
      * reflexivity.
    + inversion H3.
  - simpl in *; rewrite IHleft_associated; auto; lia.
Qed.

Lemma ix_tree_product'_cut_right {A : Type} (M : Monoid A) (L : MonoidLaws M)
      (f : nat -> option A) (t : ix_tree) :
  right_associated t ->
  (O < ix_tree_depth t)%nat ->
  rightmost O t ->
  ix_tree_product' M (seq_one (monoid_unit M)) f t =
  ix_tree_product' M f f (cut_right t).
Proof.
  induction 1; simpl; intros Hlt H0; try lia.
  inversion H0; subst.
  destruct r; simpl.
  - destruct n0; simpl.
    + destruct (f n).
      * unfold option_mult; f_equal; destruct L; auto.
      * reflexivity.
    + inversion H3.
  - simpl in *; rewrite IHright_associated; auto; lia.
Qed.

Lemma seq_reps_seq_reps' {A : Type} (M : Monoid A) (L : MonoidLaws M) (f : nat -> option A) :
  seq_reps M f === seq_reps' M f.
Proof.
  split.
  - exists (fun n => let (iters, k) := nat_f n in
             if Nat.eqb iters O then
               nat_g (iters, k)
             else if Nat.eqb iters (S O) then
                    let (i, j) := nat_f k in nat_g (iters, nat_g (j, i))
                  else
                    nat_g (iters, collapse_ix_tree
                                    (cut_left (right_associate (ix_node (mk_ix_tree iters k)
                                                                        (ix_leaf O)))))).
    exists (fun n => let (iters, k) := nat_f n in
             if Nat.eqb iters O then
               nat_g (iters, k)
             else if Nat.eqb iters (S O) then
                    let (i, j) := nat_f k in nat_g (iters, nat_g (j, i))
                  else
                    nat_g (iters, collapse_ix_tree
                                    (cut_right (left_associate (ix_node (ix_leaf O)
                                                                        (mk_ix_tree' iters k)))))).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      destruct (Nat.eqb_spec n O); subst.
      { rewrite nat_f_g, <- Hi, nat_g_f; reflexivity. }
      destruct (Nat.eqb_spec n 1); subst.
      { destruct (nat_f n0) eqn:Hn0.
        rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity. }
      rewrite nat_f_g.
      apply Nat.eqb_neq in n1.
      apply Nat.eqb_neq in n2.
      rewrite n1, n2; clear n1 n2.
      rewrite <- nat_g_f, Hi; repeat f_equal.
      set (t := cut_left (right_associate (ix_node (mk_ix_tree n n0) (ix_leaf 0)))).
      replace n with (ix_tree_depth t).
      2: { unfold t.
           rewrite ix_tree_depth_cut_left.
           2: { apply right_associate_spec.
                constructor; apply mk_ix_tree_left_associated. }
           rewrite right_associate_depth.
           2: { constructor; apply mk_ix_tree_left_associated. }           
           simpl; rewrite Nat.max_0_r.
           apply mk_ix_tree_depth. }
      rewrite mk_ix_tree'_collapse.
      2: { apply right_associated_cut_left, right_associate_spec.
           constructor; apply mk_ix_tree_left_associated. }
      simpl; unfold t; simpl.
      rewrite left_associate_cut_left.
      2: { apply right_add_spec; try constructor.
           apply right_associate_spec, mk_ix_tree_left_associated. }
      assert (leftmost O (left_associate (right_add (right_associate (mk_ix_tree n n0))
                                                    (ix_leaf 0)))).
      { apply leftmost_left_associate, leftmost_right_add, leftmost_right_associate.
        unfold equiv, zero in Hnz; simpl in Hnz.
        eapply leftmost_0_mk_ix_tree; eauto. }
      rewrite left_add_cut_left; auto.
      2: { rewrite left_associate_depth.
           - rewrite right_add_depth; try lia; try constructor.
             apply right_associate_spec, mk_ix_tree_left_associated.
           - apply right_add_spec; try constructor.
             apply right_associate_spec, mk_ix_tree_left_associated. }
      2: { apply left_associate_spec.
           apply right_add_spec; try constructor.
           apply right_associate_spec, mk_ix_tree_left_associated. }
      rewrite left_associate_right_add; simpl.
      rewrite left_right_associate.
      * apply collapse_mk_ix_tree.
      * apply mk_ix_tree_left_associated.
    + unfold seq_reps, seq_reps', seq_flatten.
      unfold seq_reps_n, seq_reps_n', equiv.
      destruct (nat_f i) eqn:Hi.
      destruct (Nat.eqb_spec n O); subst.
      { rewrite nat_f_g; reflexivity. }
      destruct (Nat.eqb_spec n 1); subst.
      { destruct (nat_f n0) eqn:Hn0.
        rewrite nat_f_g; simpl.
        unfold seq_product.
        rewrite nat_f_g, Hn0.
        destruct n; simpl.
        - destruct (f n2); try reflexivity.
          + unfold option_mult; f_equal; destruct L; rewrite monoid_lunit; auto.
        - rewrite option_mult_unit_r; reflexivity. }
      rewrite nat_f_g; simpl.
      rewrite seq_product_n_seq_product_n'.
      rewrite <- ix_tree_product_mk_ix_tree.
      rewrite <- ix_tree_product'_mk_ix_tree'.
      rewrite mk_ix_tree'_collapse'.
      2: { rewrite ix_tree_depth_cut_left.
           2: { apply right_add_spec; try constructor.
                apply right_associate_spec, mk_ix_tree_left_associated. }
           rewrite right_add_depth; try constructor.
           2: { apply right_associate_spec, mk_ix_tree_left_associated. }
           simpl; rewrite Nat.add_0_r.
           rewrite right_associate_depth.
           - rewrite mk_ix_tree_depth; reflexivity.
           - apply mk_ix_tree_left_associated. }
      2: { apply right_associated_cut_left.
           apply right_add_spec; try constructor.
           apply right_associate_spec, mk_ix_tree_left_associated. }
      rewrite ix_tree_product_cut_left; auto; try lia.
      2: { intro HC; apply Hnz; unfold seq_reps, seq_flatten; rewrite Hi.
           unfold equiv, zero; simpl; unfold seq_reps_n.
           rewrite seq_product_n_seq_product_n'; auto. }
      rewrite ix_tree_product'_cut_right; auto.
      2: { apply right_associated_cut_left.
           apply right_add_spec; try constructor.
           apply right_associate_spec, mk_ix_tree_left_associated. }
      2: { rewrite ix_tree_depth_cut_left.
           2: { apply right_add_spec; try constructor.
                apply right_associate_spec, mk_ix_tree_left_associated. }
           rewrite right_add_depth; simpl; try constructor.
           2: { apply right_associate_spec, mk_ix_tree_left_associated. }
           rewrite right_associate_depth, mk_ix_tree_depth; try lia.
           apply mk_ix_tree_left_associated. }
      2: { apply rightmost_cut_left, rightmost_right_add; constructor. }
      rewrite cut_right_cut_left.
      2: { rewrite right_add_depth; try constructor.
           2: { apply right_associate_spec, mk_ix_tree_left_associated. }
           simpl; rewrite Nat.add_0_r.
           rewrite right_associate_depth.
           - rewrite mk_ix_tree_depth; lia.
           - apply mk_ix_tree_left_associated. }
      rewrite cut_right_right_add.
      2: { apply right_associate_spec, mk_ix_tree_left_associated. }
      rewrite cut_left_right_associate.
      2: { rewrite mk_ix_tree_depth; lia. }
      2: { apply mk_ix_tree_left_associated. }
      apply ix_tree_product_right_associate; auto.
      apply left_associated_cut_left, mk_ix_tree_left_associated.
  - exists (fun n => let (iters, k) := nat_f n in
             if Nat.eqb iters O then
               nat_g (iters, k)
             else if Nat.eqb iters (S O) then
                    let (i, j) := nat_f k in nat_g (iters, nat_g (j, i))
                  else
                    nat_g (iters, collapse_ix_tree
                                    (cut_right (left_associate (ix_node (ix_leaf O)
                                                                        (mk_ix_tree' iters k)))))).
    exists (fun n => let (iters, k) := nat_f n in
             if Nat.eqb iters O then
               nat_g (iters, k)
             else if Nat.eqb iters (S O) then
                    let (i, j) := nat_f k in nat_g (iters, nat_g (j, i))
                  else
                    nat_g (iters, collapse_ix_tree
                                    (cut_left (right_associate (ix_node (mk_ix_tree iters k)
                                                                        (ix_leaf O)))))).
    intros i Hnz; split.
    + destruct (nat_f i) eqn:Hi.
      destruct (Nat.eqb_spec n O); subst.
      { rewrite nat_f_g, <- Hi, nat_g_f; reflexivity. }
      destruct (Nat.eqb_spec n 1); subst.
      { destruct (nat_f n0) eqn:Hn0.
        rewrite 2!nat_f_g, <- Hn0, nat_g_f, <- Hi, nat_g_f; reflexivity. }
      rewrite nat_f_g.
      apply Nat.eqb_neq in n1.
      apply Nat.eqb_neq in n2.
      rewrite n1, n2; clear n1 n2.
      rewrite <- nat_g_f, Hi; repeat f_equal.
      set (t := cut_right (left_associate (ix_node (ix_leaf 0) (mk_ix_tree' n n0)))).
      replace n with (ix_tree_depth t).
      2: { unfold t.
           rewrite ix_tree_depth_cut_right.
           2: { apply left_associate_spec.
                constructor; apply mk_ix_tree'_right_associated. }
           rewrite left_associate_depth.
           2: { constructor; apply mk_ix_tree'_right_associated. }
           simpl; apply mk_ix_tree'_depth. }
      rewrite mk_ix_tree_collapse.
      2: { apply left_associated_cut_right, left_associate_spec.
           constructor; apply mk_ix_tree'_right_associated. }
      simpl; unfold t; simpl.
      rewrite right_associate_cut_right.
      2: { apply left_add_spec; try constructor.
           apply left_associate_spec, mk_ix_tree'_right_associated. }
      assert (rightmost O (right_associate (left_add (ix_leaf 0)
                                                     (left_associate (mk_ix_tree' n n0))))).
      { apply rightmost_right_associate, rightmost_left_add, rightmost_left_associate.
        unfold equiv, zero in Hnz; simpl in Hnz.
        eapply rightmost_0_mk_ix_tree'; eauto. }
      rewrite right_add_cut_right; auto.
      2: { rewrite right_associate_depth.
           - rewrite left_add_depth; try lia; try constructor.
             apply left_associate_spec, mk_ix_tree'_right_associated.
           - apply left_add_spec; try constructor.
             apply left_associate_spec, mk_ix_tree'_right_associated. }
      2: { apply right_associate_spec.
           apply left_add_spec; try constructor.
           apply left_associate_spec, mk_ix_tree'_right_associated. }
      rewrite right_associate_left_add; simpl.
      rewrite right_left_associate.
      * apply collapse_mk_ix_tree'.
      * apply mk_ix_tree'_right_associated.
    + unfold seq_reps, seq_reps', seq_flatten.
      unfold seq_reps_n, seq_reps_n', equiv.
      unfold seq_reps', seq_flatten in Hnz.
      destruct (nat_f i) eqn:Hi.
      destruct (Nat.eqb_spec n O); subst.
      { rewrite nat_f_g; reflexivity. }
      destruct (Nat.eqb_spec n 1); subst.
      { destruct (nat_f n0) eqn:Hn0.
        rewrite nat_f_g; simpl.
        unfold seq_product.
        rewrite nat_f_g, Hn0.
        destruct n2; simpl.
        - destruct (f n); try reflexivity.
          + unfold option_mult; f_equal; destruct L; rewrite monoid_lunit; auto.
        - rewrite option_mult_unit_r; reflexivity. }
      rewrite nat_f_g; simpl.
      rewrite seq_product_n_seq_product_n'.
      rewrite <- ix_tree_product_mk_ix_tree.
      rewrite <- ix_tree_product'_mk_ix_tree'.
      rewrite mk_ix_tree_collapse'.
      2: { rewrite ix_tree_depth_cut_right.
           2: { apply left_add_spec; try constructor.
                apply left_associate_spec, mk_ix_tree'_right_associated. }
           rewrite left_add_depth; try constructor.
           2: { apply left_associate_spec, mk_ix_tree'_right_associated. }
           simpl; rewrite left_associate_depth.
           - rewrite mk_ix_tree'_depth; reflexivity.
           - apply mk_ix_tree'_right_associated. }
      2: { apply left_associated_cut_right.
           apply left_add_spec; try constructor.
           apply left_associate_spec, mk_ix_tree'_right_associated. }
      rewrite ix_tree_product'_cut_right; auto.
      2: { apply mk_ix_tree'_right_associated. }
      2: { rewrite mk_ix_tree'_depth; lia. }
      2: { eapply rightmost_0_mk_ix_tree'; eauto.
           unfold seq_reps', seq_flatten.
           rewrite Hi; intro HC; apply Hnz; eapply HC. }
      rewrite ix_tree_product_cut_left'; auto.
      2: { apply left_associated_cut_right.
           apply left_add_spec; try constructor.
           apply left_associate_spec, mk_ix_tree'_right_associated. }
      2: { rewrite ix_tree_depth_cut_right.
           2: { apply left_add_spec; try constructor.
                apply left_associate_spec, mk_ix_tree'_right_associated. }
           rewrite left_add_depth; try constructor.
           2: { apply left_associate_spec, mk_ix_tree'_right_associated. }
           simpl.
           rewrite left_associate_depth.
           - rewrite mk_ix_tree'_depth; lia.
           - apply mk_ix_tree'_right_associated. }
      2: { apply leftmost_cut_right.
           apply leftmost_left_add; constructor. }
      rewrite <- cut_right_cut_left.
      2: { rewrite left_add_depth; try constructor.
           2: { apply left_associate_spec, mk_ix_tree'_right_associated. }
           simpl; rewrite left_associate_depth.
           - rewrite mk_ix_tree'_depth; lia.
           - apply mk_ix_tree'_right_associated. }
      rewrite cut_left_left_add.
      2: { apply left_associate_spec, mk_ix_tree'_right_associated. }
      rewrite cut_right_left_associate.
      2: { rewrite mk_ix_tree'_depth; lia. }
      2: { apply mk_ix_tree'_right_associated. }
      apply ix_tree_product_left_associate; auto.
      apply right_associated_cut_right, mk_ix_tree'_right_associated.
Qed.

(* r . r* === r* . r *)
Lemma seq_product_seq_reps_comm {A : Type} (M : Monoid A) (L : MonoidLaws M) (s : nat -> option A) :
  seq_product M s (seq_reps M s) === seq_product M (seq_reps M s) s.
Proof.
  rewrite seq_product_seq_reps_r_seq_reps_plus; auto.
  rewrite seq_reps_seq_reps'; auto.
  rewrite seq_product_seq_reps_l_seq_reps_plus; auto.
  apply seq_reps_plus_seq_reps_plus'; auto.
Qed.

Lemma seq_reps_unfold_r {A : Type} (M : Monoid A) (s : nat -> option A) :
  seq_reps M s === seq_union (seq_one (monoid_unit M)) (seq_product M (seq_reps M s) s).
Proof.
  split.
  - exists (fun n => let (i, j) := nat_f n in
             match i with
             | O => (2 * j)%nat
             | S i' =>
               let (j', i'') := nat_f j in
               (2 * nat_g (nat_g (i', j'), i'') + 1)%nat
             end).
    exists (fun n => match n mod 2 with
             | O => nat_g (O, O)
             | S _ =>
               let (k, i'') := nat_f (n / 2)%nat in
               let (i', j') := nat_f k in
               let j := nat_g (j', i'') in
               nat_g (S i', j)
             end).
    intros n Hnz; split.
    + destruct (nat_f n) eqn:Hn.
      destruct n0.
      * rewrite Nat.mul_comm, Nat.mod_mul; auto.
        destruct n1.
        -- rewrite <- Hn, nat_g_f; reflexivity.
        -- unfold seq_reps, seq_flatten in Hnz.
           rewrite Hn in Hnz; simpl in Hnz; congruence.
      * destruct (nat_f n1) eqn:Hn1.
        rewrite Nat.add_comm, Nat.mul_comm.
        rewrite Nat.mod_add; auto.
        replace (1 mod 2) with (S O) by reflexivity.
        rewrite Nat.div_add; auto.
        simpl.
        rewrite 2!nat_f_g.
        rewrite <- Hn1, nat_g_f.
        rewrite <- Hn, nat_g_f; reflexivity.
    + unfold equiv, zero in *; simpl in Hnz.
      unfold seq_reps, seq_flatten, seq_reps_n.
      unfold seq_union, seq_product.
      destruct (nat_f n) eqn:Hn.
      destruct n0.
      * rewrite Nat.mul_comm, Nat.mod_mul; auto.
        rewrite Nat.div_mul; auto.
      * destruct (nat_f n1) eqn:Hn1.
        rewrite Nat.add_comm, Nat.mul_comm.
        rewrite Nat.mod_add; auto.
        replace (1 mod 2) with (S O) by reflexivity.
        rewrite Nat.div_add; auto; simpl.
        unfold seq_product.
        rewrite Hn1.
        rewrite 2!nat_f_g.
        destruct (nat_f n2) eqn:Hn2; reflexivity.
  - exists (fun n => match n mod 2 with
             | O => nat_g (O, O)
             | S _ =>
               let (k, i'') := nat_f (n / 2)%nat in
               let (i', j') := nat_f k in
               let j := nat_g (j', i'') in
               nat_g (S i', j)
             end).
    exists (fun n => let (i, j) := nat_f n in
             match i with
             | O => (2 * j)%nat
             | S i' =>
               let (j', i'') := nat_f j in
               (2 * nat_g (nat_g (i', j'), i'') + 1)%nat
             end).
    intros n Hnz; split; unfold seq_union in Hnz.
    + destruct (mod_2_dec n) as [Hmod | Hmod]; rewrite Hmod in *.
      * rewrite nat_f_g.
        destruct n; auto.
        destruct n; inversion Hmod.
        exfalso; apply Hnz.
        apply singleton_seq_none.
        apply Nat.div_str_pos; lia.
      * destruct (nat_f (n/2)%nat) eqn:Hn.
        destruct (nat_f n0) eqn:Hn0.
        simpl.
        rewrite 2!nat_f_g.
        rewrite <- Hn0, nat_g_f.
        rewrite <- Hn, nat_g_f.
        rewrite Nat.add_0_r.
        apply odd_div_add; auto.
    + unfold seq_union, seq_product, seq_reps, seq_flatten.
      destruct (mod_2_dec n) as [Hmod | Hmod]; rewrite Hmod in *.
      * rewrite nat_f_g.
        destruct n.
        -- reflexivity.
        -- destruct n.
           ++ inversion Hmod.
           ++ exfalso; apply Hnz.
              apply singleton_seq_none.
              apply Nat.div_str_pos; lia.
      * destruct (nat_f (n/2)%nat) eqn:Hn.
        destruct (nat_f n0) eqn:Hn0.
        rewrite nat_f_g.
        unfold seq_reps_n, seq_product_n.
        simpl; unfold seq_product.
        rewrite nat_f_g; reflexivity.
Qed.

Lemma seq_reps_unfold {A : Type} (M : Monoid A) (L : MonoidLaws M) (s : nat -> option A) :
  seq_reps M s === seq_union (seq_one (monoid_unit M)) (seq_product M s (seq_reps M s)).
Proof.
  rewrite seq_product_seq_reps_comm; auto.
  apply seq_reps_unfold_r.
Qed.

(*** Regular expressions. *)

Inductive RE (A : Type) : Type :=
| RE_empty : RE A
| RE_epsilon : RE A
| RE_cons : A -> RE A -> RE A
| RE_seq : RE A -> RE A -> RE A
| RE_choice : RE A -> RE A -> RE A
| RE_star : RE A -> RE A.

Definition RE_plus {A : Type} (re : RE A) := RE_seq re (RE_star re).

Fixpoint RE_reduce {A : Type} (re : RE A) : RE A :=
  match re with
  | RE_empty _ => RE_empty _
  | RE_epsilon _ => RE_epsilon _
  | RE_cons x r => match RE_reduce r with
                  | RE_empty _ => RE_empty _
                  | r' => RE_cons x r'
                  end
  | RE_seq r1 r2 => match (RE_reduce r1, RE_reduce r2) with
                   | (RE_empty _, _) => RE_empty _
                   | (_, RE_empty _) => RE_empty _
                   | (RE_epsilon _, r2') => r2'
                   | (r1', RE_epsilon _) => r1'
                   | (r1', r2') => RE_seq r1' r2'
                   end
  | RE_choice r1 r2 => match (RE_reduce r1, RE_reduce r2) with
                      | (RE_empty _, r2') => r2'
                      | (r1', RE_empty _) => r1'
                      | (r1', r2') => RE_choice r1' r2'
                      end
  | RE_star r => match RE_reduce r with
                | RE_empty _ => RE_empty _
                | RE_epsilon _ => RE_epsilon _
                | r' => RE_star r'
                end
  end.

Inductive RE_is_empty {A : Type} : RE A -> Prop :=
| RE_is_empty_empty : RE_is_empty (RE_empty _)
| RE_is_empty_cons : forall x r,
    RE_is_empty r ->
    RE_is_empty (RE_cons x r)
| RE_is_empty_seq1 : forall r1 r2,
    RE_is_empty r1 ->
    RE_is_empty (RE_seq r1 r2)
| RE_is_empty_seq2 : forall r1 r2,
    RE_is_empty r2 ->
    RE_is_empty (RE_seq r1 r2)
| RE_is_empty_choice : forall r1 r2,
    RE_is_empty r1 ->
    RE_is_empty r2 ->
    RE_is_empty (RE_choice r1 r2).

Fixpoint RE_is_emptyb {A : Type} (re : RE A) : bool :=
  match re with
  | RE_empty _ => true
  | RE_epsilon _ => false
  | RE_cons x r => RE_is_emptyb r
  | RE_seq r1 r2 => RE_is_emptyb r1 || RE_is_emptyb r2
  | RE_choice r1 r2 => RE_is_emptyb r1 && RE_is_emptyb r2
  | RE_star _ => false (* RE_star (RE_empty _) is not empty *)
  end.

Lemma RE_is_emptyb_spec {A : Type} (re : RE A)
  : reflect (RE_is_empty re) (RE_is_emptyb re).
Proof.
  induction re; simpl.
  - repeat constructor.
  - constructor; intro HC; inversion HC.
  - destruct IHre; constructor; try constructor; auto.
    intro HC; inversion HC; auto.
  - destruct IHre1, IHre2; simpl; constructor; try solve[constructor; auto].
    intro HC; inversion HC; auto.
  - destruct IHre1, IHre2; simpl; repeat constructor; auto;
      intro HC; inversion HC; auto.
  - constructor; intro HC; inversion HC.
Qed.

Inductive RE_nonempty {A : Type} : RE A -> Prop :=
| RE_nonempty_epsilon : RE_nonempty (RE_epsilon _)
| RE_nonempty_cons : forall x r,
    RE_nonempty r ->
    RE_nonempty (RE_cons x r)
| RE_nonempty_seq : forall r1 r2,
    RE_nonempty r1 ->
    RE_nonempty r2 ->
    RE_nonempty (RE_seq r1 r2)
| RE_nonempty_choice1 : forall r1 r2,
    RE_nonempty r1 ->
    RE_nonempty (RE_choice r1 r2)
| RE_nonempty_choice2 : forall r1 r2,
    RE_nonempty r2 ->
    RE_nonempty (RE_choice r1 r2)
| RE_nonempty_star : forall r,
    RE_nonempty (RE_star r).

Fixpoint RE_nonemptyb {A : Type} (re : RE A) : bool :=
  match re with
  | RE_empty _ => false
  | RE_epsilon _ => true
  | RE_cons x r => RE_nonemptyb r
  | RE_seq r1 r2 => RE_nonemptyb r1 && RE_nonemptyb r2
  | RE_choice r1 r2 => RE_nonemptyb r1 || RE_nonemptyb r2
  | RE_star r => true
  end.

Lemma RE_nonemptyb_spec {A : Type} (re : RE A)
  : reflect (RE_nonempty re) (RE_nonemptyb re).
Proof.
  induction re; simpl.
  - constructor; intro HC; inversion HC.
  - repeat constructor.
  - destruct IHre; constructor; try constructor; auto.
    intro HC; inversion HC; auto.
  - destruct IHre1, IHre2; simpl; repeat constructor; auto;
      intro HC; inversion HC; auto.
  - destruct IHre1, IHre2; simpl; constructor; try solve[constructor; auto].
    intro HC; inversion HC; auto.
  - repeat constructor.
Qed.

Lemma RE_is_empty_not_nonempty {A : Type} (re : RE A) :
  RE_is_empty re <-> ~ RE_nonempty re.
Proof.
  split.
  - induction 1; intro HC; inversion HC; auto.
  - induction re; intro HC. 
    + constructor.
    + exfalso; apply HC; constructor.
    + constructor; apply IHre; intro H; apply HC; constructor; auto.
    + destruct (RE_nonemptyb_spec re1).
      * destruct (RE_nonemptyb_spec re2).
        -- exfalso; apply HC; constructor; auto.
        -- apply RE_is_empty_seq2; auto.
      * constructor; auto.
    + constructor.
      * apply IHre1; intro H; apply HC; constructor; auto.
      * apply IHre2; intro H; apply HC; solve [constructor; auto].
    + exfalso; apply HC; constructor.
Qed.

Lemma RE_not_is_empty_nonempty {A : Type} (re : RE A) :
  ~ RE_is_empty re <-> RE_nonempty re.
Proof.
  split.
  - induction re; intro HC.
    + exfalso; apply HC; constructor.
    + constructor.
    + constructor; apply IHre; intro H; apply HC; constructor; auto.
    + constructor.
      * apply IHre1; intro H; apply HC; constructor; auto.
      * apply IHre2; intro H; apply HC; solve [constructor; auto].
    + destruct (RE_is_emptyb_spec re1).
      * destruct (RE_is_emptyb_spec re2). 
        -- exfalso; apply HC; constructor; auto.
        -- solve [constructor; auto].
      * constructor; auto.
    + constructor.
  - induction 1; intro HC; inversion HC; auto.
Qed.

Fixpoint RE_of_tree_fail {A : Type} (t : tree A) (n : nat) : RE bool :=
  match t with
  | Leaf x => @RE_empty bool
  | Fail _ m => if m =? n then @RE_epsilon bool else @RE_empty bool
  | Choice _ t1 t2 => RE_choice (RE_cons true (RE_of_tree_fail t1 n))
                               (RE_cons false (RE_of_tree_fail t2 n))
  | Fix lbl t1 => RE_seq (RE_star (RE_of_tree_fail t1 lbl)) (RE_of_tree_fail t1 n)
  end.

Fixpoint RE_of_tree_f {A : Type} (t : tree A) (P : A -> bool) : RE bool :=
  match t with
  | Leaf x => if P x then @RE_epsilon bool else @RE_empty bool
  | Fail _ _ => @RE_empty bool
  | Choice _ t1 t2 => RE_choice (RE_cons true (RE_of_tree_f t1 P))
                               (RE_cons false (RE_of_tree_f t2 P))
  | Fix lbl t1 => RE_seq (RE_star (RE_of_tree_fail t1 lbl)) (RE_of_tree_f t1 P)
  end.

Fixpoint RE_of_tree_mixed {A : Type} (t : tree A) (P : nat + A -> bool) : RE bool :=
  match t with
  | Leaf x => if P (inr x) then @RE_epsilon bool else @RE_empty bool
  | Fail _ n => if P (inl n) then @RE_epsilon bool else @RE_empty bool
  | Choice _ t1 t2 => RE_choice (RE_cons true (RE_of_tree_mixed t1 P))
                               (RE_cons false (RE_of_tree_mixed t2 P))
  | Fix lbl t1 =>
    RE_seq (RE_star (RE_of_tree_mixed t1 (cotuple (eqb lbl) (const false))))
           (RE_of_tree_mixed t1 P)
  end.

Lemma RE_of_tree_fail_mixed {A : Type} (t : tree A) (n : nat) :
  RE_of_tree_mixed t (cotuple (eqb n) (const false)) = RE_of_tree_fail t n.
Proof.
  revert n; induction t; simpl; intro m; auto.
  - rewrite Nat.eqb_sym; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite 2!IHt; reflexivity.
Qed.

Lemma RE_of_tree_f_mixed {A : Type} (t : tree A) (P : A -> bool) :
  RE_of_tree_mixed t (cotuple (const false) P) = RE_of_tree_f t P.
Proof.
  induction t; simpl; auto.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt, RE_of_tree_fail_mixed; reflexivity.
Qed.

Definition RE_of_tree {A : Type} (t : tree A) (P : A -> bool) (n : nat) : RE bool :=
  RE_seq (RE_star (RE_of_tree_fail t n)) (RE_of_tree_f t P).

Lemma RE_of_tree_fail_fix {A : Type} (t : tree A) (m n : nat) :
  RE_of_tree_fail (Fix n t) m = RE_seq (RE_star (RE_of_tree_fail t n)) (RE_of_tree_fail t m).
Proof. reflexivity. Qed.

Lemma RE_of_tree_f_fix {A : Type} (t : tree A) (P : A -> bool) (n : nat) :
  RE_of_tree_f (Fix n t) P = RE_seq (RE_star (RE_of_tree_fail t n)) (RE_of_tree_f t P).
Proof. reflexivity. Qed.

Fixpoint RE_sequence {A : Type} (re : RE A) : nat -> option (list A) :=
  match re with
  | RE_empty _ => seq_zero
  | RE_epsilon _ => seq_one []
  | RE_cons x r => option_mult MonoidList (Some [x]) ∘ RE_sequence r
  | RE_seq r1 r2 => seq_product MonoidList (RE_sequence r1) (RE_sequence r2)
  | RE_choice r1 r2 => seq_union (RE_sequence r1) (RE_sequence r2)
  | RE_star r => seq_reps MonoidList (RE_sequence r)
  end.

Definition tree_sequence_fail {A : Type}
           (t : tree A) (lbl : nat) : nat -> option (list bool) :=
  RE_sequence (RE_of_tree_fail t lbl).

Definition tree_sequence_f {A : Type}
           (t : tree A) (P : A -> bool) : nat -> option (list bool) :=
  RE_sequence (RE_of_tree_f t P).

Definition tree_sequence_mixed {A : Type}
           (t : tree A) (P : nat + A -> bool)  : nat -> option (list bool) :=
  RE_sequence (RE_of_tree_mixed t P).

Definition tree_sequence {A : Type}
           (t : tree A) (P : A -> bool) (n : nat) : nat -> option (list bool) :=
  RE_sequence (RE_of_tree t P n).

Lemma RE_of_tree_mixed_fail {A : Type} (t : tree A) (lbl : nat) :
  RE_of_tree_fail t lbl = RE_of_tree_mixed t (cotuple (eqb lbl) (const false)).
Proof.
  revert lbl; induction t; simpl; intro lbl; auto.
  - rewrite Nat.eqb_sym; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite 2!IHt; reflexivity.
Qed.

Lemma RE_of_tree_mixed_f {A : Type} (t : tree A) (f : A -> bool) :
  RE_of_tree_f t f = RE_of_tree_mixed t (cotuple (const false) f).
Proof.
  induction t; simpl; auto.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt, RE_of_tree_mixed_fail; reflexivity.
Qed.

Lemma tree_sequence_mixed_fail {A : Type} (t : tree A) (lbl : nat) :
  tree_sequence_fail t lbl = tree_sequence_mixed t (cotuple (eqb lbl) (const false)).
Proof.
  unfold tree_sequence_fail, tree_sequence_mixed.
  rewrite RE_of_tree_mixed_fail; reflexivity.
Qed.

Lemma tree_sequence_mixed_f {A : Type} (t : tree A) (f : A -> bool) :
  tree_sequence_f t f = tree_sequence_mixed t (cotuple (const false) f).
Proof.
  unfold tree_sequence_f, tree_sequence_mixed.
  rewrite RE_of_tree_mixed_f; reflexivity.
Qed.

Lemma RE_is_empty_sequence {A : Type} (re : RE A) (i : nat) :
  RE_is_empty re ->
  RE_sequence re i = None.
Proof.
  intro Hempty. revert i. induction Hempty; intro i; simpl.
  - reflexivity.
  - unfold compose; rewrite IHHempty; reflexivity.
  - unfold seq_product; destruct (nat_f i); rewrite IHHempty; reflexivity.
  - unfold seq_product; destruct (nat_f i); rewrite IHHempty.
    unfold option_mult; destruct (RE_sequence r1 n); reflexivity.
  - unfold seq_union; simpl.
    rewrite IHHempty1, IHHempty2.
    destruct (snd (divmod i 1 0 1)); reflexivity.
Qed.

Lemma RE_nonempty_sequence {A : Type} (re : RE A) :
  RE_nonempty re ->
  exists i x, RE_sequence re i = Some x.
Proof.
  induction 1; simpl.
  - exists O, []; reflexivity.
  - unfold compose.
    destruct IHRE_nonempty as [i [y Heq]].
    exists i. eexists. rewrite Heq. reflexivity.
  - destruct IHRE_nonempty1 as [i [x H1]].
    destruct IHRE_nonempty2 as [j [y H2]].
    unfold seq_product. exists (nat_g (i, j)). eexists.
    rewrite nat_f_g, H1, H2; reflexivity.
  - destruct IHRE_nonempty as [i [x Heq]].
    unfold seq_union. exists (i*2)%nat.
    rewrite Nat.mod_mul; try lia.
    exists x; rewrite Nat.div_mul; try lia; auto.
  - destruct IHRE_nonempty as [i [x Heq]].
    unfold seq_union. exists (1+i*2)%nat.
    exists x; rewrite Nat.mod_add; try lia.
    assert (H0: ((1 + i * 2 ) / 2 = i)%nat).
    { rewrite Nat.div_add; auto. }
    rewrite H0. simpl; auto.
  - exists (nat_g (O, O)), []; unfold seq_reps, seq_flatten.
    rewrite nat_f_g; reflexivity.
Qed.

(** TODO: could be interesting to prove that a string is recognized
    iff it occurs in a sequence related to the RE by RE_sequence. *)

Inductive recognizes {A : Type} : RE A -> list A -> Prop :=
| recognizes_epsilon : recognizes (@RE_epsilon A) []
| recognizes_cons : forall x l r,
    recognizes r l ->
    recognizes (RE_cons x r) (x :: l)
| recognizes_seq : forall r1 r2 l1 l2,
    recognizes r1 l1 ->
    recognizes r2 l2 ->
    recognizes (RE_seq r1 r2) (l1 ++ l2)
| recognizes_choice_l : forall r1 r2 l,
    recognizes r1 l ->
    recognizes (RE_choice r1 r2) l
| recognizes_choice_r : forall r1 r2 l,
    recognizes r2 l ->
    recognizes (RE_choice r1 r2) l
| recognizes_plus : forall r l1 l2,
    recognizes r l1 ->
    recognizes (RE_star r) l2 ->
    recognizes (RE_plus r) (l1 ++ l2).

Lemma option_mult_none_r {A : Type} (M : Monoid A) (x : option A) :
  option_mult M x None = None.
Proof. destruct x; auto. Qed.    

Lemma RE_nonempty_RE_of_tree_fail_infer_fail {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  unbiased t ->
  not_bound_in n t ->
  RE_nonempty (RE_of_tree_fail t n) ->
  0 < infer_fail n t.
Proof.
  induction t; simpl; intros Hwf Hunbiased Hnotbound Hnonempty.
  - inversion Hnonempty.
  - destruct (Nat.eqb_spec n0 n); subst; try lra.
    inversion Hnonempty.
  - inversion Hwf; inversion Hunbiased; inversion Hnotbound; subst.
    rewrite H8; inversion Hnonempty; subst.
    + inversion H0; subst.
      apply IHt1 in H1; auto.
      assert (0 <= infer_fail n t2).
      { apply infer_fail_0_le; auto. }
      lra.
    + inversion H0; subst.
      apply IHt2 in H1; auto.
      assert (0 <= infer_fail n t1).
      { apply infer_fail_0_le; auto. }
      lra.
  - inversion Hwf; inversion Hunbiased; inversion Hnotbound; subst.
    inversion Hnonempty; subst.
    apply IHt in H5; auto.
    assert (infer_fail n0 t + infer_fail n t <= 1).
    { apply infer_fail_infer_fail_le_1; auto. }
    assert (infer_fail n0 t < 1).
    { lra. }
    apply Qlt_shift_div_l; lra.
Qed.

Lemma RE_nonempty_RE_of_tree_f_infer_f {A : Type} (t : tree A) (P : A -> bool) :
  wf_tree t ->
  unbiased t ->
  RE_nonempty (RE_of_tree_f t P) ->
  0 < infer_f (fun x => if P x then 1 else 0) t.
Proof.
  induction t; simpl; intros Hwf Hunbiased Hnonempty.
  - destruct (P a); try lra; inversion Hnonempty.
  - inversion Hnonempty.
  - inversion Hwf; inversion Hunbiased; subst.
    rewrite H8; inversion Hnonempty; subst.
    + inversion H0; subst.
      apply IHt1 in H1; auto.
      assert (0 <= infer_f (fun x => if P x then 1 else 0) t2).
      { apply infer_f_expectation_0_le; auto; intro x; destruct (P x); lra. }
      lra.
    + inversion H0; subst.
      apply IHt2 in H1; auto.
      assert (0 <= infer_f (fun x => if P x then 1 else 0) t1).
      { apply infer_f_expectation_0_le; auto; intro x; destruct (P x); lra. }
      lra.
  - inversion Hwf; inversion Hunbiased; subst.
    inversion Hnonempty; subst.
    apply IHt in H5; auto.
    assert (infer_f (fun x => if P x then 1 else 0) t + infer_fail n t <= 1).
    { apply infer_f_infer_fail_le_1; auto.
      intro x; destruct (P x); lra. }
    assert (infer_fail n t < 1).
    { lra. }
    apply Qlt_shift_div_l; lra.
Qed.

Lemma RE_nonempty_infer_fail {A : Type} (t : tree A) (P : A -> bool) (n : nat) :
  wf_tree t ->
  unbiased t ->
  not_bound_in n t ->
  RE_nonempty (RE_of_tree_f t P) ->
  infer_fail n t < 1.
Proof.
  intros Hwf Hunbiased Hnotbound Hnonempty.
  apply RE_nonempty_RE_of_tree_f_infer_f in Hnonempty; auto.
  assert (infer_f (fun x => if P x then 1 else 0) t + infer_fail n t <= 1).
  { apply infer_f_infer_fail_le_1; auto.
    intro x; destruct (P x); lra. }
  lra.
Qed.

Lemma RE_is_empty_infer_fail {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  unbiased t ->
  RE_is_empty (RE_of_tree_fail t n) ->
  infer_fail n t == 0.
Proof.
  induction t; simpl; intros Hwf Hunbiased Hempty; try reflexivity.
  - destruct (Nat.eqb_spec n0 n); subst; try lra; inversion Hempty.
  - inversion Hwf; inversion Hunbiased; subst.
    inversion Hempty; subst.
    inversion H1; inversion H5; subst.
    rewrite IHt1, IHt2; auto; lra.
  - inversion Hwf; inversion Hunbiased; subst.
    inversion Hempty; subst.
    + inversion H0.
    + rewrite IHt; auto.
      apply Qdiv_0_num.
Qed.

Lemma RE_is_empty_infer_f {A : Type} (t : tree A) (P : A -> bool) :
  wf_tree t ->
  unbiased t ->
  RE_is_empty (RE_of_tree_f t P) ->
  infer_f (fun x => if P x then 1 else 0) t == 0.
Proof.
  induction t; simpl; intros Hwf Hunbiased Hempty; try reflexivity.
  - destruct (P a); subst; try lra; inversion Hempty.
  - inversion Hwf; inversion Hunbiased; subst.
    inversion Hempty; subst.
    inversion H1; inversion H5; subst.
    rewrite IHt1, IHt2; auto; lra.
  - inversion Hwf; inversion Hunbiased; subst.
    inversion Hempty; subst.
    + inversion H0.
    + rewrite IHt; auto.
      apply Qdiv_0_num.
Qed.

Lemma seq_product_nil {A : Type} (s1 s2 : nat -> option (list A)) (i : nat) :
  seq_product MonoidList s1 s2 i = Some [] ->
  exists j, s2 j = Some [].
Proof.
  unfold seq_product.
  destruct (nat_f i) eqn:Hi; intro H.
  destruct (s1 n) eqn:Hn, (s2 n0) eqn:Hn0; inversion H.
  apply app_nil_inv in H1; destruct H1; subst; simpl; eexists; eauto.
Qed.

Lemma seq_incomparable_seq_one {A : Type} :
  seq_incomparable (@seq_one (list A) []).
Proof.
  intros [] [] x y Hneq H0 H1; try congruence; inversion H0; inversion H1.
Qed.

Lemma seq_incomparable_seq_zero {A : Type} :
  seq_incomparable (@seq_zero (list A)).
Proof. intros i j ? ? ? H; inversion H. Qed.

Lemma seq_one_inv {A : Type} (s : nat -> option (list A)) :
  s === seq_one [] ->
  forall i, s i = None \/ s i = Some [].
Proof.
  intros [[f [g H0]] H1] i.
  destruct (s i) eqn:Hi; auto; right; f_equal.
  assert (H: ~ s i === zero).
  { unfold equiv, zero; simpl; congruence. }
  apply H0 in H. destruct H as [_ H].
  destruct (f i).
  - rewrite Hi in H; inversion H; auto.
  - simpl in H; congruence.
Qed.

Lemma seq_union_inv {A : Type} (s s1 s2 : nat -> option (list A)) :
  s === seq_union s1 s2 ->
  forall i, s i = None \/ exists j, s i = s1 j \/ s i = s2 j.
Proof.
  intros [[f [g H0]] H1] i.
  destruct (s i) eqn:Hi; auto; right.
  assert (H: ~ s i === zero).
  { unfold equiv, zero; simpl; congruence. }
  apply H0 in H; destruct H as [_ H].
  rewrite Hi in H.
  unfold equiv, seq_union in H.
  destruct (f i mod 2); exists (f i / 2)%nat; auto.
Qed.

Lemma ext_eq_seq_bijection_upto_0 {A : Type} `{HasZero A} `{Equivalence A} (s1 s2 : nat -> A) :
  (forall i, s1 i === s2 i) ->
  seq_bijection_upto_0 s1 s2.
Proof.
  intros Heq; split; exists id, id; intros i Hnz;
    unfold id; split; auto; rewrite Heq; reflexivity.
Qed.

Lemma compose_seq_injection_upto_0 {A B : Type} `{HasZero A} `{Equivalence A}
      `{HasZero B} `{Equivalence B} (s1 s2 : nat -> A) (f : A -> B) :
  Proper (equiv ==> equiv) f ->
  f zero === zero ->
  seq_injection_upto_0 s1 s2 ->
  seq_injection_upto_0 (f ∘ s1) (f ∘ s2).
Proof.
  unfold compose; intros Hprop Hzero [g [h Hinj]].
  exists g, h; intros i Hnz.
  assert (H': ~ s1 i === zero).
  { intro HC; apply Hnz; rewrite HC; auto. }
  apply Hinj in H'.
  destruct H'; split; auto.
Qed.

Lemma compose_seq_bijection_upto_0 {A B : Type} `{HasZero A} `{Equivalence A}
      `{HasZero B} `{Equivalence B} (s1 s2 : nat -> A) (f : A -> B) :
  Proper (equiv ==> equiv) f ->
  f zero === zero ->
  seq_bijection_upto_0 s1 s2 ->
  seq_bijection_upto_0 (f ∘ s1) (f ∘ s2).
Proof.
  unfold compose; intros Jprop Hzero [Hinj Hsurj].
  split; apply compose_seq_injection_upto_0; auto.
Qed.
