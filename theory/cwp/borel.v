Set Implicit Arguments.

Require Import Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import List.
Import ListNotations.

Require Import axioms.
Require Import misc.
Require Import order.
Require Import Q.

Local Open Scope program_scope.

(** A real number in the unit interval represented by its infinite
    binary expansion. *)
Definition real : Type := nat -> bool.

Definition real_zero : real := const false.
Definition real_one : real := const true.

(* (** An open interval is represented by its real endpoints. *) *)
(* Definition open : Type := real*real. *)

(** Non-empty binary intervals. *)
Definition interval : Type := list bool.

(** Measurable sets generated by binary intervals and closed under
    countable union. *)
Inductive meas : Type :=
| meas_empty : meas
| meas_interval : interval -> meas
| meas_union : (nat -> meas) -> meas.

(** The Borel measure of a binary interval. *)
Definition interval_measure (bs : interval) : Q :=
  1 / (Qpow 2 (length bs)).

(** We can directly compute the intersection of two binary intervals,
    producing a new interval, or None if the intersection is empty. *)
Fixpoint interval_intersection (u v : list bool) : option (interval) :=
  match (u, v) with
  | ([], _) => Some v
  | (_, []) => Some u
  | (x :: xs, y :: ys) =>
    match interval_intersection xs ys with
    | None => None
    | Some zs =>
      if eqb x y then Some (x :: zs) else None
    end
  end.

(* Fixpoint interval_disjoint (a b : interval) : Prop := *)
(*   match (a, b) with *)
(*   | (None, _) => True *)
(*   | (_, None) => True *)
(*   | (Some [], _) => False *)
(*   | (_, Some []) => False *)
(*   | (Some (x :: xs), Some (y :: ys)) => interval_disjoint (Some xs) (Some ys) *)
(*   end. *)

Inductive comparable {A : Type} : list A -> list A -> Prop :=
| comparable_nil1 : forall l2,
    comparable nil l2
| comparable_nil2 : forall l1,
    comparable l1 nil
| comparable_cons : forall x l1 l2,
    comparable l1 l2 ->
    comparable (x :: l1) (x :: l2).

Inductive incomparable {A : Type} : list A -> list A -> Prop :=
| incomparable_head : forall x y xs ys,
    x <> y ->
    incomparable (x :: xs) (y :: ys)
| incomparable_tail : forall x xs ys,
    incomparable xs ys ->
    incomparable (x :: xs) (x :: ys).

Lemma not_incomparable_comparable {A : Type} `{EqType A} (l1 l2 : list A) :
  not (incomparable l1 l2) <-> comparable l1 l2.
Proof.
  split.
  - revert l2.
    induction l1; intros [] Hnotincomp; try constructor.
    destruct (eqb_spec a a0); subst.
    + constructor.
      apply IHl1.
      intro HC. apply Hnotincomp.
      apply incomparable_tail; auto.
    + exfalso; apply Hnotincomp; constructor; auto.
  - induction 1; intro HC; inversion HC; subst; congruence.
Qed.

Lemma incomparable_not_comparable {A : Type} `{EqType A} (l1 l2 : list A) :
  incomparable l1 l2 <-> not (comparable l1 l2).
Proof.
  split.
  - induction 1; intro HC; inversion HC; subst; congruence.
  - revert l2.
    induction l1; intros l2 Hnotcomp.
    + exfalso; apply Hnotcomp; constructor.
    + destruct l2.
      * exfalso; apply Hnotcomp; constructor.
      * destruct (eqb_spec a a0); subst.
        -- right. apply IHl1.
           intro HC. apply Hnotcomp. constructor; auto.
        -- constructor; auto.
Qed.

Lemma is_prefix_comparable {A : Type} (l1 l2 : list A) :
  comparable l1 l2 <-> is_prefix l1 l2 \/ is_prefix l2 l1.
Proof.
  split.
  - intro Hcomp.
    induction Hcomp; try solve [repeat constructor].
    destruct IHHcomp; solve [repeat constructor; auto].
  - intros [Hpre | Hpre]; induction Hpre; constructor; auto.
Qed.

Definition interval_disjoint (a b : interval) : Prop := incomparable a b.

(* Fixpoint interval_disjoint (a b : interval) : Prop := *)
(*   match (a, b) with *)
(*   | ([], _) => False *)
(*   | (_, []) => False *)
(*   | (x :: xs, y :: ys) => x <> y \/ interval_disjoint xs ys *)
(*   end. *)

Inductive disjoint : meas -> meas -> Prop :=
| disjoint_empty_1 : forall U,
    disjoint U meas_empty
| disjoint_empty_2 : forall U,
    disjoint meas_empty U
| disjoint_interval : forall a b,
    interval_disjoint a b ->
    disjoint (meas_interval a) (meas_interval b)
| disjoint_union : forall f g,
    (forall i j, disjoint (f i) (g j)) ->
    disjoint (meas_union f) (meas_union g).

(* Fixpoint first_n {A : Type} (f : nat -> A) (n : nat) : list A := *)
(*   match n with *)
(*   | O => [] *)
(*   | S n' => first_n f n' ++ [f n'] *)
(*   end. *)

(* Definition partial_sum (f : nat -> Q) (n : nat) : Q := *)
(*   sum_Q_list (first_n f (S n)). *)

Inductive partial_sumP (R : nat -> Q -> Prop) : nat -> Q -> Prop :=
| partial_sumP_O : forall q,
    R O q ->
    partial_sumP R O q
| partial_sumP_S : forall n p q s,
    partial_sumP R n q ->
    R (S n) p ->
    s == p + q ->
    partial_sumP R (S n) s.

Definition f_relation {A B : Type} (f : A -> B) (R : A -> B -> Prop) :=
  forall x, R x (f x).

Lemma fold_right_Qplus_app (l1 l2 : list Q) :
  fold_right Qplus 0 (l1 ++ l2) ==
  fold_right Qplus 0 l1 + fold_right Qplus 0 l2.
Proof. induction l1; simpl; lra. Qed.

(* Lemma partial_sum_spec (f : nat -> Q) (R : nat -> Q -> Prop) : *)
(*   f_relation f R -> *)
(*   Proper (eq ==> Qeq ==> iff) R -> *)
(*   f_relation (partial_sum f) (partial_sumP R). *)
(* Proof. *)
(*   intros Hrel Hproper n. *)
(*   induction n. *)
(*   - unfold partial_sum. simpl. unfold compose. *)
(*     constructor. *)
(*     rewrite Qplus_0_r. apply Hrel. *)
(*   - econstructor; eauto. *)
(*     unfold partial_sum. simpl. *)
(*     unfold sum_Q_list. *)
(*     rewrite fold_right_Qplus_app; simpl; lra. *)
(* Qed. *)

(** The Borel measure of a measurable set. *)
Inductive measure : meas -> Q -> Prop :=
| measure_empty : forall m,
    m == 0 ->
    measure meas_empty m
| measure_interval : forall i m,
    m == interval_measure i ->
    measure (meas_interval i) m
| measure_union : forall f g m,
    (forall i j, i <> j -> disjoint (f i) (f j)) ->
    (forall i, measure (f i) (g i)) ->
    supremum m (partial_sum g) ->
    measure (meas_union f) m.

Fixpoint real_in_intervalb_aux (r : real) (i : interval) (n : nat) : bool :=
  match i with
  | [] => true
  | b :: bs => eqb (r n) b && real_in_intervalb_aux r bs (S n)
  end.

Definition real_in_intervalb (r : real) (i : interval) : bool :=
  real_in_intervalb_aux r i O.

Inductive real_in_interval_aux : real -> interval -> nat -> Prop :=
| real_in_interval_nil : forall r n,
    real_in_interval_aux r [] n
| real_in_interval_cons : forall r bs n,
    real_in_interval_aux r bs (S n) ->
    real_in_interval_aux r (r n :: bs) n.

Definition real_in_interval (r : real) (i : interval) : Prop :=
  real_in_interval_aux r i O.

Lemma real_in_intervalb_aux_spec (r : real) (i : interval) (n : nat)
  : reflect (real_in_interval_aux r i n) (real_in_intervalb_aux r i n).
Proof.
  revert r n.
  induction i; intros r n; simpl.
  - repeat constructor.
  - destruct (Bool.eqb (r n) a) eqn:Heq; simpl.
    + apply eqb_prop in Heq; subst.
      destruct (IHi r (S n)).
      * repeat constructor; auto.
      * constructor; intro HC; inversion HC; subst; congruence.
    + apply eqb_false_iff in Heq.
      constructor; intro HC; inversion HC; subst; congruence.
Qed.

Lemma real_in_intervalb_spec (r : real) (i : interval)
  : reflect (real_in_interval r i) (real_in_intervalb r i).
Proof. apply real_in_intervalb_aux_spec. Qed.
  
(* Lemma real_in_interval_dec (r : real) (U : meas) : *)
(*   real_in_interval r U \/ ~ real_in_interval r U. *)

(* Lemma pred_dec {A : Type} (f : A -> bool) (x : A) : *)
(*   f x = true \/ ~ f x = true. *)
(* Proof. destruct (f x); auto. Qed. *)

Lemma bool_dec (x : bool) :
  x = true \/ ~ x = true.
Proof. destruct x; auto. Qed.

Lemma bool_sumbool (x : bool) :
  {x = true} + {~ x = true}.
Proof. destruct x; auto. Defined.

Fixpoint real_in_measb (U : meas) (r : real) : bool :=
  match U with
  | meas_empty => false
  | meas_interval i => real_in_intervalb r i
  | meas_union f =>
    if strong_LPO (fun n => real_in_measb (f n) r = true)
                  (fun n => bool_sumbool (real_in_measb (f n) r))
    then true else false
  end.

Inductive real_in_meas : meas -> real -> Prop :=
| real_in_meas_interval : forall r i,
    real_in_interval r i ->
    real_in_meas (meas_interval i) r
| real_in_meas_union : forall r f,
    (exists n, real_in_meas (f n) r) ->
    real_in_meas (meas_union f) r.

Lemma real_in_measb_spec (U : meas) (r : real)
  : reflect (real_in_meas U r) (real_in_measb U r).
Proof.
  induction U; simpl.
  - constructor; intro HC; inversion HC.
  - destruct (real_in_intervalb_spec r i); constructor.
    + constructor; auto.
    + intro HC. apply n.
      inversion HC; subst; auto.
  - destruct (strong_LPO (fun n : nat => real_in_measb (m n) r = true)
                         (fun n : nat => bool_sumbool (real_in_measb (m n) r))).
    + constructor; constructor.
      destruct e as [n Hn].
      exists n. destruct (H n); auto; congruence.
    + constructor.
      intro HC. inversion HC; subst.
      destruct H1 as [x H2].
      apply n; exists x; destruct (H x); auto.
Qed.

Lemma comparable_prefix {A : Type} (f : nat -> A) (n m : nat) :
  comparable (prefix f n) (prefix f m).
Proof.
  apply is_prefix_comparable.
  destruct (Nat.le_decidable n m);
    solve [constructor; apply prefix_is_prefix; lia].
Qed.

Inductive nth_element {A : Type} : nat -> list A -> A -> Prop :=
| nth_element_O : forall x xs,
    nth_element O (x :: xs) x
| nth_element_S : forall x xs y n,
    nth_element n xs y ->
    nth_element (S n) (x :: xs) y.

Lemma sdf {A : Type} (f : nat -> A) (l : list A) (x : A) :
  l <> nil ->
  (forall i, (i < length (x :: l))%nat -> nth_element i (x :: l) (f i)) ->
  forall i, (i < length l)%nat ->
       nth_element i l (f (S i)).
Proof.
  intros Hneq Hnth i Hlt.
  destruct l; try congruence.
  assert (Hlt': (S i < length (x :: a :: l))%nat).
  { simpl in *; lia. }
  specialize (Hnth (S i) Hlt').
  inversion Hnth; subst; auto.
Qed.

Lemma real_in_interval_aux_asdf(r : real) (bs : list bool) (n : nat) :
  (forall i, (i < length bs)%nat -> nth_element i bs (r (i + n)%nat)) ->
  real_in_interval_aux r bs n.
Proof.
  revert n.
  induction bs; intros n Hnth.
  - constructor.
  - simpl in Hnth.
    assert (a = r n).
    { specialize (Hnth O (Nat.lt_0_succ _)).
      inversion Hnth; subst.
      rewrite plus_0_l; reflexivity. }
    subst; constructor.
    destruct bs. constructor.
    apply IHbs.
    intros i Hlt.
    rewrite Nat.add_succ_r.
    set (g := drop r n).
    assert (forall i, g i = r (i + n)%nat).
    { intro m. unfold g. unfold drop; auto. }
    assert (nth_element i (b :: bs) (g (S i))).
    { apply sdf with (x := r n); auto.
      intro HC; congruence. }
    auto.
Qed.

Lemma kdfg {A : Type} (i : nat) (l1 l2 : list A) (x : A) :
  (i < length l1)%nat ->
  nth_element i l1 x ->
  nth_element i (l1 ++ l2) x.
Proof.
  revert i l2 x.
  induction l1; intros i l2 x Hlt Hnth.
  - inversion Hlt.
  - destruct i; inversion Hnth; subst; constructor.
    apply IHl1; auto; simpl in Hlt; lia.
Qed.

Lemma kdfgsdf {A : Type} (i : nat) (l1 l2 : list A) (x : A) :
  (length l1 <= i)%nat ->
  nth_element (i - length l1) l2 x ->
  nth_element i (l1 ++ l2) x.
Proof.
  revert l2 i x.
  induction l1; simpl; intros l2 i x Hlt Hnth.
  - rewrite Nat.sub_0_r in Hnth; auto.
  - destruct i. lia.
    constructor.
    apply IHl1. lia.
    apply Hnth.
Qed.

Lemma nth_element_slice (r : real) (n m i : nat) :
  (i < length (slice r n m))%nat ->
  nth_element i (slice r n m) (r (i + n)%nat).
Proof.
  revert n i. induction m; simpl; intros n i Hlt.
  - inversion Hlt.
  - unfold slice in *. simpl in *.
    destruct (Nat.ltb_spec0 i m).
    + apply kdfg. rewrite length_prefix; auto.
      apply IHm. rewrite length_prefix; auto.
    + assert (i = m).
      { rewrite app_length in Hlt.
        rewrite length_prefix in Hlt. simpl in Hlt.
        lia. }
      subst.
      apply kdfgsdf.
      rewrite length_prefix; lia.
      rewrite length_prefix.
      rewrite Nat.sub_diag.
      constructor.
Qed.

Lemma real_in_interval_aux_slice (r : real) (n m : nat) :
  real_in_interval_aux r (slice r n m) n.
Proof.
  apply real_in_interval_aux_asdf.
  apply nth_element_slice.
Qed.

Lemma real_in_interval_prefix (r : real) (n : nat) :
  real_in_interval r (prefix r n).
Proof.
  rewrite <- slice_O.
  apply real_in_interval_aux_slice.
Qed.

Lemma length_slice {A : Type} (f : nat -> A) (n m : nat) :
  length (slice f n m) = m.
Proof.
  induction m; auto.
  unfold slice in *. simpl.
  rewrite app_length.
  rewrite IHm; simpl; lia.
Qed.

Lemma slice_cons {A : Type} (f : nat -> A) (i n : nat) :
  slice f i (S n) = f i :: slice f (S i) n.
Proof.
  revert i.
  induction n; simpl; intro i.
  - reflexivity.
  - unfold slice in *; simpl in *.
    rewrite (IHn i); unfold drop; simpl.
    rewrite plus_n_Sm; reflexivity.
Qed.

Lemma real_in_interval_aux_slice_length (r : real) (bs : interval) (i : nat) :
  real_in_interval_aux r bs i ->
  slice r i (length bs) = bs.
Proof.
  revert i.
  induction bs; simpl; intros i Hin.
  - reflexivity.
  - inversion Hin; subst.
    apply IHbs in H3.
    rewrite <- H3.
    rewrite length_slice.
    apply slice_cons.
Qed.

Lemma real_in_interval_exists_prefix (r : real) (bs : interval) :
  real_in_interval r bs ->
  prefix r (length bs) = bs.
Proof.
  intro Hin.
  apply real_in_interval_aux_slice_length in Hin.
  rewrite slice_O in Hin; auto.
Qed.

Fixpoint count_Q (bs : list bool) : Q :=
  match bs with
  | [] => 0
  | b :: bs' => (if b then 1 else 0) + count_Q bs'
  end.

(** Relational version of count_Q'. *)
Inductive count_QR {A : Type} (P : A -> Prop) : list A -> Q -> Prop :=
| count_QR_nil : forall p,
    p == 0 ->
    count_QR P [] p
| count_QR_cons_false : forall x xs p,
    ~ P x ->
    count_QR P xs p ->
    count_QR P (x :: xs) p
| count_QR_cons_true : forall x xs p q,
    P x ->
    count_QR P xs p ->
    q == p + 1 ->
    count_QR P (x :: xs) q.

Instance Proper_count_QR {A : Type} (P : A -> Prop)
  : Proper (eq ==> Qeq ==> iff) (count_QR P).
Proof.
  intros ? l ? p q Heq; subst.
  split; intro H.
  - induction H; subst.
    + constructor. rewrite <- Heq; auto.
    + constructor; auto.
    + eapply count_QR_cons_true; eauto.
      rewrite <- Heq; auto.
  - induction H; subst.
    + constructor. rewrite Heq; auto.
    + constructor; auto.
    + eapply count_QR_cons_true; eauto.
      rewrite Heq; auto.
Qed.

Fixpoint count_Q' {A : Type} (f : A -> bool) (xs : list A) : Q :=
  match xs with
  | [] => 0
  | x :: xs' => (if f x then 1 else 0) + count_Q' f xs'
  end.

Lemma count_Q'_spec {A : Type} (f : A -> bool) (xs : list A) :
  count_Q' f xs = count_Q (map f xs).
Proof.
  induction xs; simpl; auto.
  rewrite IHxs; auto.
Qed.

Lemma count_Q'_app {A : Type} (f : A -> bool) (l1 l2 : list A) :
  count_Q' f (l1 ++ l2) == count_Q' f l1 + count_Q' f l2.
Proof. induction l1; simpl; lra. Qed.

Lemma count_Q'_rel_eq {A B : Type}
      (f : A -> bool) (g : B -> bool) (xs : list A) (ys : list B) :
  list_rel (fun x y => f x = g y) xs ys ->
  count_Q' f xs = count_Q' g ys.
Proof.
  induction 1; simpl.
  - reflexivity.
  - rewrite H, IHlist_rel; reflexivity.
Qed.

(* Lemma count_Q'_spec' {A : Type} (f : A -> bool) (xs : list A) : *)
(*   count_QR (fun x => is_true (f x)) xs (count_Q' f xs). *)
(* Proof. *)
(*   induction xs; simpl. *)
(*   - constructor; reflexivity. *)
(*   - destruct (f a) eqn:Hfa. *)
(*     + eapply count_QR_cons_true; eauto; field. *)
(*     + constructor. congruence. *)
(*       rewrite Qplus_0_l; auto. *)
(* Qed. *)

Lemma count_Q'_spec' {A : Type} (P : A -> Prop) (f : A -> bool) (xs : list A) :
  (forall x, reflect (P x) (f x)) ->
  count_QR P xs (count_Q' f xs).
Proof.
  intro Hreflect.
  induction xs; simpl.
  - constructor; reflexivity.
  - specialize (Hreflect a).
    destruct Hreflect.
    + eapply count_QR_cons_true; eauto; field.
    + constructor. congruence.
      rewrite Qplus_0_l; auto.
Qed.


Definition rel_freq {A : Type} (f : A -> bool) (l : list A) : Q :=
  match l with
  | [] => 0
  | _ => count_Q' f l / (Z.of_nat (length l) # 1)
  end.

Lemma rel_freq_eq {A B : Type} (P : A -> bool) (Q : B -> bool) (f : nat -> A) (g : nat -> B) (n : nat) :
  (forall i, P (f i) = Q (g i)) ->
  rel_freq P (prefix f n) == rel_freq Q (prefix g n).
Proof.
  intro Heq.
  destruct n; simpl; try lra.
  simpl; unfold rel_freq.
  destruct (prefix f n ++ [f n]) eqn:Hf.
  - apply app_eq_nil in Hf; destruct Hf; congruence.
  - destruct (prefix g n ++ [g n]) eqn:Hg.
    + apply app_eq_nil in Hg; destruct Hg; congruence.
    + rewrite <- Hf, <- Hg. simpl. f_equal.
      * rewrite 2!app_length.
        rewrite 2!length_prefix; simpl.
        rewrite 2!count_Q'_app.
        simpl. rewrite Heq.
        erewrite count_Q'_rel_eq. reflexivity.
        apply list_rel_prefix; auto.
Qed.

(* Definition rel_freq (U : meas) (rs : list real) : Q := *)
(*   match rs with *)
(*   | [] => 0 *)
(*   | _ => count_Q' (real_in_measb U) rs / (Z.of_nat (length rs) # 1) *)
(*   end. *)

Definition rel_freq' (U : meas) (rs : list real) : Q :=
  rel_freq (real_in_measb U) rs.

(** Relational version of rel_freq using count_QR. Then prove
    equivalence of the two versions. *)
Inductive rel_freqR : meas -> list real -> Q -> Prop :=
| rel_freqR_nil : forall U q,
    q == 0 ->
    rel_freqR U [] q
| rel_freqR_cons : forall U r rs a b,
    count_QR (real_in_meas U) (r :: rs) a ->
    b == a / (Z.of_nat (length (r :: rs)) # 1) ->
    rel_freqR U (r :: rs) b.

Lemma rel_freq_spec (U : meas) (rs : list real) :
  rel_freqR U rs (rel_freq' U rs).
Proof.
  destruct rs; simpl.
  - constructor; reflexivity.
  - econstructor; auto; try reflexivity.
    destruct (real_in_measb_spec U r).
    eapply count_QR_cons_true; auto.
    2: { rewrite Qplus_comm; reflexivity. }
    + apply count_Q'_spec'; intro x; apply real_in_measb_spec.
    + constructor; auto; rewrite Qplus_0_l.
      apply count_Q'_spec'; intro x; apply real_in_measb_spec.
Qed.

Lemma count_QR_deterministic {A : Type} (P : A -> Prop) (l : list A) (p q : Q) :
  count_QR P l p ->
  count_QR P l q ->
  p == q.
Proof.
  revert p q.
  induction l; intros p q H0 H1.
  - inversion H0; inversion H1; subst; lra.
  - inversion H0; inversion H1; subst; try congruence.
    + apply IHl; auto.
    + assert (Heq: p0 == p1).
      { apply IHl; auto. }
      lra.
Qed.

Lemma rel_freqR_deterministic (U : meas) (rs : list real) (p q : Q) :
  rel_freqR U rs p ->
  rel_freqR U rs q ->
  p == q.
Proof.
  induction rs; intros H0 H1.
  - inversion H0; inversion H1; subst; lra.
  - inversion H0; inversion H1; subst.
    rewrite H6, H12. field_simplify_eq.
    + eapply count_QR_deterministic; eauto.
    + simpl; apply Q_neq_0; lia.
Qed.

(** Characterization of uniformity of a sequence of real numbers in
    the unit interval. *)
Definition uniform (reals : nat -> real) : Prop :=
  forall U : meas,
  forall m : Q,
    measure U m ->
    forall eps : Q,
      0 < eps ->
      exists n, Qabs (m - rel_freq' U (prefix reals n)) < eps.

Definition uniform' (reals : nat -> real) : Prop :=
  forall U : meas,
  forall m : Q,
    measure U m ->
    forall eps : Q,
      0 < eps ->
      exists n, forall freq,
          rel_freqR U (prefix reals n) freq ->
          Qabs (m - freq) < eps.

Lemma uniform_equiv (reals : nat -> real) :
  uniform reals <-> uniform' reals.
Proof.
  unfold uniform, uniform'.
  split; intro H.
  - intros U m Hm eps Heps.
    specialize (H U m Hm eps Heps).
    destruct H as [n H].
    exists n. intros freq Hfreq.
    assert (Heq: freq == rel_freq' U (prefix reals n)).
    { eapply rel_freqR_deterministic; eauto.
      apply rel_freq_spec. }
    rewrite Heq; auto.
  - intros U m Hm eps Heps.
    specialize (H U m Hm eps Heps).
    destruct H as [n H].
    specialize (H (rel_freq' U (prefix reals n))
                  (rel_freq_spec U (prefix reals n))).
    exists n; auto.
Qed.

(** TODO: show how the above assumption leads to a similar property of
    the relative frequency of samples within some set P converging to
    the measure of P which is by another theorem equal to the inferred
    probability of P. *)

(* Inductive measure : borel -> Q -> Prop := *)
(* | measure_interval : forall i m, *)
(*     m == interval_measure i -> *)
(*     measure (borel_interval i) m *)
(* | measure_union : forall u v a b c m, *)
(*     measure u a -> *)
(*     measure v b -> *)
(*     measure (borel_intersection u v) c -> *)
(*     m == a + b - c -> *)
(*     measure (borel_union u v) m. *)

(* Fixpoint measure (b : borel) : Q := *)
(*   match b with *)
(*   | borel_interval i => interval_measure i *)
(*   | borel_union u v => measure u + measure v - measure (borel_intersection u v) *)
(*   | _ => 0 *)
(*   end. *)


Fixpoint positive_binary (p : positive) : list bool :=
  match p with
  | xI p' => true :: positive_binary p'
  | xO p' => false :: positive_binary p'
  | xH => [true]
  end.

Definition N_binary (n : N) : list bool :=
  match n with
  | N0 => []
  | Npos p => positive_binary p
  end.

Definition nat_binary (n : nat) : list bool :=
  N_binary (N.of_nat n).

Eval compute in (nat_binary 4).

(* Fixpoint strip_falses (bs : list bool) : list bool := *)
(*   match bs with *)
(*   | [] => [] *)
(*   | x :: [false] => [x] *)
(*   | x :: xs => x :: strip_falses xs *)
(*   end. *)

(* Fixpoint strip_falses (bs : list bool) : list bool := *)
(*   match bs with *)
(*   | [] => [] *)
(*   | false :: [] => [] *)
(*   | x :: xs => x :: strip_falses xs *)
(*   end. *)

Fixpoint strip_falses (bs : list bool) : list bool :=
  match bs with
  | [] => []
  | x :: xs =>
    match strip_falses xs with
    | [] =>
      if x then [x] else []
    | xs' => x :: xs'
    end
  end.

(** TODO: the natural numbers aren't actually in one-to-one
correspondence with bit sequences, unless you only consider bit
sequences with no leading zeros. So, we append a 1 to each bit
sequence before sending it to nat. *)

(** TODO: fix *)
Fixpoint binary_positive (bs : list bool) : positive :=
  match bs with
  | [] => xH (* invalid case *)
  | b :: [] => xH (* Assume b is true *)
  | b :: bs =>
    (if b then xI else xO) (binary_positive bs)
  end.

Definition binary_N_aux (bs : list bool) : N :=
  match bs with
  | [] => N0
  (* | false :: [] => N0 *)
  | _ => Npos (binary_positive bs)
  end.

Definition binary_N (bs : list bool) : N :=
  binary_N_aux (strip_falses bs).

Definition binary_nat (bs : list bool) : nat :=
  N.to_nat (binary_N bs).

(* Definition nat_binary_inv (bs : list bool) : nat := *)
(*   N.to_nat (Ascii.N_of_digits bs). *)

Lemma strip_falses_idempotent (bs : list bool) :
  strip_falses (strip_falses bs) = strip_falses bs.
Proof.
  induction bs; auto; simpl.
  destruct (strip_falses bs); destruct a;
    auto; simpl in *; rewrite IHbs; auto.
Qed.

Lemma binary_N_strip_falses (bs : list bool) :
  binary_N (strip_falses bs) = binary_N bs.
Proof.
  unfold binary_N; rewrite strip_falses_idempotent; reflexivity.
Qed.

Lemma binary_nat_strip_falses (bs : list bool) :
  binary_nat (strip_falses bs) = binary_nat bs.
Proof.
  unfold binary_nat; rewrite binary_N_strip_falses; reflexivity.
Qed.

Inductive no_leading_falses : list bool -> Prop :=
| no_leading_falses_nil :
    no_leading_falses []
| no_leading_falses_cons_false : forall b bs,
    no_leading_falses (b :: bs) ->
    no_leading_falses (false :: b :: bs)
| no_leading_falses_cons_true : forall bs,
    no_leading_falses bs ->
    no_leading_falses (true :: bs).

Lemma no_leading_falses_app (l1 l2 : list bool) :
  l2 <> nil ->
  no_leading_falses l2 ->
  no_leading_falses (l1 ++ l2).
Proof.
  revert l2.
  induction l1; simpl; intros l2 Hneq Hno; auto.
  destruct l1; simpl in *.
  + destruct l2; try congruence.
    destruct a; constructor; auto.
  + destruct a; constructor; auto.
Qed.

Lemma no_leading_falses_strip_falses (bs : list bool) :
  no_leading_falses (strip_falses bs).
Proof.
  induction bs; simpl.
  - constructor.
  - destruct (strip_falses bs); destruct a; constructor; auto.
Qed.

Lemma no_leading_falses_strip_falses_noop (bs : list bool) :
  no_leading_falses bs ->
  strip_falses bs = bs.
Proof.
  induction 1; auto.
  - simpl in *; rewrite IHno_leading_falses; auto.
  - simpl. rewrite IHno_leading_falses.
    destruct bs; auto.
Qed.

(* Lemma strip_falses_idempotent' (bs : list bool) : *)
(*   strip_falses (strip_falses bs) = strip_falses bs. *)
(* Proof. *)
(*   apply no_leading_falses_strip_falses_noop. *)
(*   apply no_leading_falses_strip_falses. *)
(* Qed. *)

Lemma positive_binary_non_nil (p : positive) :
  positive_binary p <> nil.
Proof. induction p; simpl; intro HC; congruence. Qed.
  
Lemma no_leading_falses_positive_binary (p : positive) :
  no_leading_falses (positive_binary p).
Proof.
  induction p; simpl.
  - constructor; auto.
  - destruct (positive_binary p) eqn:Hp.
    + exfalso; eapply positive_binary_non_nil; eauto.
    + constructor; auto.
  - repeat constructor.
Qed.

Lemma binary_N_aux_positive_binary (p : positive) :
  binary_N_aux (positive_binary p) = N.pos p.
Proof.
  induction p; simpl.
  - destruct (positive_binary p); simpl in *; lia.
  - destruct (positive_binary p); simpl in *; lia.
  - reflexivity.
Qed.

Lemma binary_N_N_binary (n : N) :
  binary_N (N_binary n) = n.
Proof.
  destruct n; auto.
  unfold N_binary, binary_N.
  rewrite no_leading_falses_strip_falses_noop.
  - apply binary_N_aux_positive_binary.
  - apply no_leading_falses_positive_binary.
Qed.

Lemma N_binary_binary_N (bs : list bool) :
  no_leading_falses bs ->
  N_binary (binary_N bs) = bs.
Proof.
  intro Hno; unfold binary_N.
  rewrite no_leading_falses_strip_falses_noop; auto.
  induction Hno; simpl; auto.
  - f_equal; auto.
  - destruct bs; auto;simpl in *; f_equal; auto.
Qed.

Lemma binary_nat_nat_binary (n : nat) :
  binary_nat (nat_binary n) = n.
Proof.
  unfold binary_nat, nat_binary.
  rewrite binary_N_N_binary.
  apply Nnat.Nat2N.id.
Qed.

Lemma nat_binary_binary_nat (bs : list bool) :
  no_leading_falses bs ->
  nat_binary (binary_nat bs) = bs.
Proof.
  unfold binary_nat, nat_binary.
  rewrite Nnat.N2Nat.id.
  apply N_binary_binary_N.
Qed.

(** Every bit sequence with no leading falses exists in the
    enumeration [nat_binary] (i.e., it's a surjective mapping onto the
    set of bit sequences with no leading falses). *)
Lemma nat_binary_surjective (bs : list bool) :
  no_leading_falses bs ->
  exists n, nat_binary n = bs.
Proof.
  exists (binary_nat bs); apply nat_binary_binary_nat; auto.
Qed.
  
(** Every bit sequence occurs at most once in [nat_binary] (i.e. it's
    an injective mapping). *)
Lemma nat_binary_injective (n m : nat) :
  nat_binary n = nat_binary m -> n = m.
Proof.
  intro Heq.
  assert (H: binary_nat (nat_binary n) = binary_nat (nat_binary m)).
  { rewrite Heq; reflexivity. }
  rewrite 2!binary_nat_nat_binary in H; auto.
Qed.


(** Real numbers r1 and r2 are equal up to the nth position, but
    differ at that position. *)
Definition real_neq_at_n (r1 r2 : real) (n : nat) : Prop :=
  prefix r1 n = prefix r2 n /\ r1 n <> r2 n.

Definition real_lt_at_n (r1 r2 : real) (n : nat) : Prop :=
  prefix r1 n = prefix r2 n /\ r1 n = false /\ r2 n = true.

Lemma list_eq_dec (A : Type) (l1 l2 : list A) :
  (forall x y : A, {x = y} + {x <> y}) ->
  {l1 = l2} + {l1 <> l2}.
Proof.
  revert l2.
  induction l1; intros l2 Hdec.
  - destruct l2.
    + left; auto.
    + right; congruence.
  - destruct l2.
    + right; congruence.
    + destruct (Hdec a a0); subst.
      * destruct (IHl1 l2 Hdec); subst.
        -- left; auto.
        -- right; congruence.
      * right; congruence.
Qed.

Lemma real_neq_at_n_dec (r1 r2 : real) :
  forall n, {real_neq_at_n r1 r2 n} + {~ real_neq_at_n r1 r2 n}.
Proof.
  intro n. unfold real_neq_at_n.
  destruct (list_eq_dec (prefix r1 n) (prefix r2 n) (Bool.bool_dec)).
  - rewrite e; clear e.
    destruct (Bool.bool_dec (r1 n) (r2 n)); firstorder.
  - firstorder.
Qed.

Lemma real_lt_at_n_dec (r1 r2 : real) :
  forall n, {real_lt_at_n r1 r2 n} + {~ real_lt_at_n r1 r2 n}.
Proof.
  intro n. unfold real_lt_at_n.
  destruct (list_eq_dec (prefix r1 n) (prefix r2 n) (Bool.bool_dec)).
  - rewrite e; clear e; destruct (r1 n); destruct (r2 n); intuition.
  - intuition.
Qed.

Definition real_eq_at_n (r1 r2 : real) (n : nat) : Prop :=
  r1 n = r2 n.

Lemma real_eq_at_n_dec (r1 r2 : real) (n : nat) :
  {real_eq_at_n r1 r2 n} + {~ real_eq_at_n r1 r2 n}.
Proof. destruct (Bool.bool_dec (r1 n) (r2 n)); firstorder. Qed.

Definition real_eqb (r1 r2 : real) : bool :=
  match strong_LPO (real_neq_at_n r1 r2) (real_neq_at_n_dec r1 r2) with
  | left _ => false
  | right _ => true
  end.

Definition real_ltb (r1 r2 : real) : bool :=
  match strong_LPO (real_lt_at_n r1 r2) (real_lt_at_n_dec r1 r2) with
  | left _ => true
  | right _ => false
  end.

Definition real_leb (r1 r2 : real) : bool :=
  real_eqb r1 r2 || real_ltb r1 r2.

Lemma not_exists_forall_not (A : Type) (P : A -> Prop) :
  not (exists x, P x) -> forall x, ~ P x.
Proof.
  intros Hnot x.
  intro HP. apply Hnot. exists x; auto.
Qed.

Lemma interval_measure_nonnegative (bs : interval) :
  0 <= interval_measure bs.
Proof.
  unfold interval_measure.
  assert (0 < Qpow 2 (length bs)).
  { apply Qpow_positive; lra. }
  apply Qle_shift_div_l; auto; lra.
Qed.

(* Require Import FunctionalExtensionality. *)

(* Program Instance EqType_real : EqType real := *)
(*   {| eqb := real_eqb |}. *)
(* Next Obligation. *)
(*   unfold real_eqb. *)
(*   destruct (strong_LPO (real_neq_at_n x y) (real_neq_at_n_dec x y)). *)
(*   - right. intro HC. *)
(*     assert (forall i, x i = y i). *)
(*     { rewrite HC; reflexivity. } *)
(*     destruct e as [n [_ Hneq]]; congruence. *)
(*   - left. *)
(*     assert (forall n, ~ real_neq_at_n x y n). *)
(*     { apply not_exists_forall_not; auto. } *)
(*     unfold real_neq_at_n in H. *)
(*     apply functional_extensionality; intro i. *)
(*     specialize (H i). *)
(*     admit. (* doable without classical axioms since things are decidable *) *)
(* Admitted. *)


(* Fixpoint prepend_bit (b : bool) (m : meas) : meas := *)
  
(* Inductive meas : Type := *)
(* | meas_empty : meas *)
(* | meas_interval : interval -> meas *)
(* | meas_union : (nat -> meas) -> meas. *)
