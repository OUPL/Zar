Set Implicit Arguments.
Require Import Coq.Program.Basics.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import ExtLib.Structures.Monoid.
Require Import Coq.Sorting.Permutation.
Require Import List.
Import ListNotations.
Local Open Scope program_scope.

Require Import axioms.
Require Import borel.
Require Import cpGCL.
Require Import geometric.
Require Import infer.
Require Import misc.
Require Import order.
Require Import Q.
Require Import regular.
Require Import tree.

Definition option_measure (x : option (list bool)) : Q :=
  match x with
  | None => 0
  | Some bs => interval_measure bs
  end.

Lemma option_measure_nonnegative (x : option (list bool)) :
  0 <= option_measure x.
Proof.
  destruct x; simpl; try lra; apply interval_measure_nonnegative.
Qed.

Lemma option_measure_None (x : option (list bool)) :
  option_measure x == 0 -> x = None.
Proof.
  unfold option_measure; intro H.
  destruct x; auto; exfalso; eapply interval_measure_nonzero; eauto.
Qed.

Lemma partial_sum_const (x : Q) (i : nat) :
  partial_sum (fun _ => x) i == sum_Q_list (repeat x i).
Proof.
  induction i; simpl.
  - reflexivity.
  - rewrite partial_sum_S; lra.
Qed.

Lemma partial_sum_singleton (f : nat -> Q) (n : nat) :
  (forall i, (0 < i)%nat -> f i == 0) ->
  partial_sum f (S n) == f O.
Proof.
  intros Hf; induction n.
  - unfold partial_sum; simpl; lra.
  - rewrite partial_sum_S, IHn.
    cut (f (S n) == 0). lra. apply Hf; lia.
Qed.

Lemma partial_sum_union (f g : nat -> Q) (i : nat) :
  partial_sum (seq_union f g) (i+i) == partial_sum f i + partial_sum g i.
Proof.
  induction i.
  - unfold partial_sum, seq_union; simpl. lra.
  - simpl.
    replace (S (i + S i)) with (S (S (i + i))) by lia.
    rewrite 4!partial_sum_S.
    rewrite IHi; clear IHi.
    cut (seq_union f g (i+i) + seq_union f g (S (i+i)) == f i + g i).
    + lra.
    + unfold seq_union.
      replace (i + i)%nat with (i * 2)%nat by lia.
      replace (S (i * 2)) with (1 + i * 2)%nat by lia.
      rewrite Nat.mod_mul; auto.
      rewrite Nat.mod_add; auto.
      replace ((i * 2) / 2)%nat with i.
      * replace ((1 + i * 2) / 2)%nat with i.
        -- reflexivity.
        -- rewrite Nat.div_add; auto.
      * rewrite Nat.div_mul; auto.
Qed.

Definition crunch (f : nat -> Q) (i : nat) : Q := f (i+i)%nat + f (S (i+i)).

Lemma partial_sum_crunch (f : nat -> Q) (i : nat) :
  partial_sum (crunch f) i == partial_sum f (i+i).
Proof.
  unfold crunch. simpl.
  induction i.
  - unfold partial_sum; simpl; lra.
  - replace (S i + S i)%nat with (S (S (i + i))) by lia.
    rewrite 3!partial_sum_S, IHi; lra.
Qed.

Lemma chain_partial_sum (s : nat -> Q) :
  (forall j, 0 <= s j) ->
  chain (partial_sum s).
Proof.
  intros Hnonneg i; simpl; rewrite partial_sum_S; specialize (Hnonneg i); lra.
Qed.

Lemma partial_sum_increasing (f : nat -> Q) (i j : nat) :
  (forall k, 0 <= f k) ->
  (i <= j)%nat ->
  partial_sum f i <= partial_sum f j.
Proof.
  revert i; induction j; intros i Hpos Hle.
  - inversion Hle; subst; lra.
  - destruct (Nat.eqb_spec i (S j)); subst.
    + lra.
    + eapply Qle_trans.
      apply IHj; auto; lia.
      apply chain_partial_sum; auto.
Qed.

Lemma partial_sum_le_crunch (f : nat -> Q) (i : nat) :
  (forall j, 0 <= f j) ->
  partial_sum f i <= partial_sum (crunch f) i.
Proof.
  intro Hle.
  rewrite partial_sum_crunch.
  apply partial_sum_increasing; auto; lia.
Qed.

Lemma crunch_partial_sum_supremum (f : nat -> Q) (sup : Q) :
  (forall i, 0 <= f i) ->
  supremum sup (partial_sum f) <-> supremum sup (partial_sum (crunch f)).
Proof.
  intro Hle; split; intros [Hub Hlub].
  - split.
    + intro y. specialize (Hub (y+y)%nat).
      rewrite partial_sum_crunch; auto.
    + intros y Hy.
      specialize (Hlub y).
      apply Hlub.
      eapply ge_upper_bound; eauto.
      intro i; apply partial_sum_le_crunch; auto.
  - split.
    + intro y. etransitivity; eauto.
      apply partial_sum_le_crunch; auto.
    + intros x Hx.
      apply Hlub.
      intro j. specialize (Hx (j+j)%nat).
      rewrite partial_sum_crunch; auto.
Qed.

(** Addition on rationals is continuous. *)
Lemma supremum_sum_Q (f g : nat -> Q) (supF supG : Q) :
  chain f ->
  chain g ->
  supremum supF f ->
  supremum supG g ->
  supremum (supF + supG) (fun i => f i + g i).
Proof.
  intros Hchainf Hchaing [Hubf Hlubf] [Hubg Hlubg].
  split.
  - intro x.
    specialize (Hubf x); specialize (Hubg x).
    simpl in *; lra.
  - intros x Hx; unfold upper_bound in Hx; simpl in *.
    cut (supF <= x - supG).
    { lra. }
    apply Hlubf; intro i; simpl in *.
    cut (supG <= x - f i).
    { lra. }
    apply Hlubg; intro j; simpl.
    destruct (Nat.leb_spec i j).
    + specialize (Hx j).
      assert (f i <= f j).
      { cut (leq (f i) (f j)). auto.
        apply chain_leq; auto. }
      lra.
    + specialize (Hx i).
      assert (g j <= g i).
      { cut (leq (g j) (g i)). auto.
        apply chain_leq; auto; lia. }
      lra.
Qed.

Lemma partial_sum_linear (f g : nat -> Q) (i : nat) :
  partial_sum (fun j => f j + g j) i == partial_sum f i + partial_sum g i.
Proof.
  induction i.
  - unfold partial_sum; simpl; lra.
  - rewrite 3!partial_sum_S, IHi; lra.
Qed.

Lemma partial_sum_scalar (f : nat -> Q) (c : Q) (i : nat) :
  partial_sum (fun j => c * f j) i == c * partial_sum f i.
Proof.
  induction i.
  - unfold partial_sum. simpl. lra.
  - rewrite 2!partial_sum_S.
    rewrite IHi. lra.
Qed.

Lemma supremum_scalar (f : nat -> Q) (c sup : Q):
  (0 <= c) ->
  supremum sup f -> supremum (c * sup) (fun i => c * f i).
Proof.
  intro Hpos.
  destruct (Qeq_dec 0 c); intros [Hub Hlub]; split.
  - intro i; simpl; rewrite <- q; lra.
  - intros x Hx; simpl; specialize (Hx O); simpl in Hx; nra.
  - intro x; specialize (Hub x); simpl in *; nra.
  - intros x Hx; simpl in *.
    cut (sup <= x / c).
    { intro H.
      assert (0 < c). lra.
      apply Qle_Qdiv' with (c := c); auto.
      assert (H': c * sup / c == sup).
      { field; lra. }
      rewrite H'; clear H'.
      apply Hlub; intro i; specialize (Hx i); simpl in *.
      apply Qle_shift_div_l; auto; lra. }
    apply Hlub; intro i; specialize (Hx i); simpl in *.
    apply Qle_shift_div_l; lra.
Qed.

Lemma supremum_scalar' (f : nat -> Q) (c sup : Q):
  (0 < c) ->
  supremum (c * sup) (fun i => c * f i) -> supremum sup f.
Proof.
  intros Hpos [Hub Hlub].
  split.
  -  intro i; specialize (Hub i); simpl in *; nra.
  - intros x Hx; simpl in *.
    cut (c * sup <= c * x).
    { nra. }
    apply Hlub; intro i; specialize (Hx i); simpl in *; nra.
Qed.

Lemma crunch_union_sum {A : Type} (f : A -> Q) (s1 s2 : nat -> A) (i : nat) :
  crunch (f ∘ seq_union s1 s2) i == f (s1 i) + f (s2 i).
Proof.
  unfold compose, crunch, seq_union.
  replace (i+i)%nat with (i*2)%nat by lia.
  rewrite Nat.mod_mul; auto.
  replace (S (i * 2)) with (1 + i * 2)%nat by lia.
  rewrite Nat.mod_add, Nat.div_add, Nat.div_mul; auto; simpl; lra.
Qed.

Lemma partial_sum_proper (f g : nat -> Q) :
  f_Qeq f g ->
  f_Qeq (partial_sum f) (partial_sum g).
Proof.
  intros Hfg i.
  unfold f_Qeq in Hfg. 
  induction i.
  - unfold partial_sum; simpl; reflexivity.
  - rewrite 2!partial_sum_S, IHi, Hfg; reflexivity.
Qed.

Instance Proper_partial_sum : Proper (equ ==> equ) partial_sum.
Proof.
  intros s1 s2 Hequ. apply f_Qeq_equ, partial_sum_proper.
  intro i; apply Qeq_equ; firstorder.
Qed.

Lemma partial_sum_measure_factor (b : bool) (i : nat) (s : nat -> option (list bool)):
  partial_sum (fun j : nat =>
                 option_measure (option_mult MonoidList (Some [b]) (s j))) i ==
  (1#2) * partial_sum (fun j => option_measure (s j)) i.
Proof.
  etransitivity; try apply partial_sum_scalar.
  apply partial_sum_proper. intro j.
  unfold option_measure, option_mult; simpl.
  destruct (s j). unfold interval_measure. simpl. field.
  apply Qpow_nonzero; lra.
  unfold interval_measure; simpl; lra.
Qed.

Lemma interval_measure_app (l1 l2 : list bool) :
  interval_measure (l1 ++ l2) == interval_measure l1 * interval_measure l2.
Proof.
  revert l2; induction l1; intro l2; simpl.
  - unfold interval_measure. simpl.
    rewrite Qdiv_1_den; lra.
  - unfold interval_measure in *; simpl.
    specialize (IHl1 l2).
    rewrite 2!Qdiv_Qmult_den; try lra.
    + rewrite IHl1; lra.
    + apply Qlt_not_eq, Qpow_positive; lra.
    + apply Qlt_not_eq, Qpow_positive; lra.
Qed.

(** The measure of the product is the product of the measures. *)
Lemma option_measure_product (x y : option (list bool)) :
  option_measure (option_mult MonoidList x y) ==
  option_measure x * option_measure y.
Proof.
  destruct x, y; simpl; try lra.
  apply interval_measure_app.
Qed.

Lemma option_measure_homo s1 s2 i :
  option_measure (seq_product MonoidList s1 s2 i) ==
  option_measure (s1 (fst (nat_f i))) * option_measure (s2 (snd (nat_f i))).
Proof.
  unfold seq_product.
  destruct (nat_f i).
  unfold option_mult. simpl.
  destruct (s1 n); destruct (s2 n0); simpl; try lra.
  apply interval_measure_app.
Qed.

Lemma seq_product_flatten {A : Type} (M : Monoid A) (s1 s2 : nat -> option A) (i : nat) :
  seq_product M s1 s2 i = seq_flatten (fun i j => option_mult M (s1 i) (s2 j)) i.
Proof. reflexivity. Qed.

Lemma sum_Q_list_permutation (l1 l2 : list Q) :
  Permutation l1 l2 ->
  sum_Q_list l1 == sum_Q_list l2.
Proof. induction 1; simpl; lra. Qed.

Definition row_ixs (l : list nat) : list nat :=
  range (S (list_max (map (fst ∘ nat_f) l))).

Definition col_ixs (l : list nat) (r : nat) : list nat :=
  map (snd ∘ nat_f) (filter (fun n => let (i, j) := nat_f n in i =? r) l).

Lemma map_nat_f_g_rows {A : Type} (a : nat) (rows : nat -> nat -> A) (l : list nat) :
  map (fun j => rows a j) l =
  map (fun n => let (i, j) := nat_f n in rows i j)
      (map (fun j => nat_g (a, j)) l).
Proof.
  induction l; simpl; auto.
  rewrite nat_f_g, IHl; reflexivity.
Qed.

Lemma concat_map_rows {A : Type} (l : list nat) (f : nat -> list nat) (rows : nat -> nat -> A) :
  concat (map (fun i => map (fun j => rows i j) (f i)) l) =
  map (seq_flatten rows)
      (concat
         (map (fun i => map (fun j => nat_g (i, j))
                         (f i))
              l)).
Proof.
  induction l; simpl; auto.
  rewrite map_app.
  f_equal; auto; apply map_nat_f_g_rows.
Qed.

Definition list_disjoint {A : Type} (l1 l2 : list A) : Prop :=
  forall x, ~ (In x l1 /\ In x l2).

Lemma list_disjoint_injection {A B : Type} (l1 l2 : list A) (f : A -> B) :
  injection f ->
  list_disjoint l1 l2 ->
  list_disjoint (map f l1) (map f l2).
Proof.
  intros [g Hgf] Hdisj y [Hin1 Hin2].
  - apply in_map_iff in Hin1.
    apply in_map_iff in Hin2.
    destruct Hin1 as [x [? Hin1]]; subst.
    destruct Hin2 as [x' [? Hin2]]; subst.
    apply injection_injective in H; firstorder; subst; firstorder.
Qed.

Lemma list_disjoint_nodup_app {A : Type} (l1 l2 : list A) :
  list_disjoint l1 l2 ->
  NoDup l1 ->
  NoDup l2 ->
  NoDup (l1 ++ l2).
Proof.
  revert l2; induction l1; intros l2 Hdisj Hnodup1 Hnodup2; simpl; auto.
  constructor.
  - intros Hx.
    apply NoDup_cons_iff in Hnodup1.
    destruct Hnodup1.
    apply in_app_or in Hx. destruct Hx; auto.
    apply (Hdisj a); intuition.
  - apply IHl1; auto.
    + intros x [H0 H1]; apply (Hdisj x); intuition.
    + apply NoDup_cons_iff in Hnodup1; intuition.
Qed.

Inductive all_disjoint {A : Type} : list (list A) -> Prop :=
| all_disjoint_nil : all_disjoint []
| all_disjoint_cons : forall l ls,
    all_disjoint ls ->
    (forall l', In l' ls -> list_disjoint l l') ->
    all_disjoint (l :: ls).

Lemma all_disjoint_single {A : Type} (l : list A) :
  all_disjoint [l].
Proof. constructor; try constructor; intros ? HC; inversion HC. Qed.

Instance Symmetric_list_disjoint {A : Type} : Symmetric (@list_disjoint A).
Proof. firstorder. Qed.

Lemma NoDup_concat {A : Type} (ls : list (list A)) :
  (forall l, In l ls -> NoDup l) ->
  all_disjoint ls ->
  NoDup (concat ls).
Proof.
  induction ls; intros Hnodup Hdisj; simpl; try constructor.
  apply list_disjoint_nodup_app.
  - intros x [Hin1 Hin2].
    apply in_concat in Hin2.
    destruct Hin2 as [l [Hin2 Hin3]].
    inversion Hdisj; subst.
    specialize (H2 l Hin2 x).
    intuition.
  - apply Hnodup; left; reflexivity.
  - apply IHls.
    + intros l Hin; apply Hnodup; right; auto.
    + inversion Hdisj; auto.
Qed.

Lemma map_injection {A B : Type} (l : list A) (f : A -> B) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  induction l; intros Hinj Hnodup; simpl; constructor.
  - intro HC. apply in_map_iff in HC.
    destruct HC as [x [Heq Hin]].
    apply Hinj in Heq; subst; intuition.
    apply NoDup_cons_iff in Hnodup; intuition.
  - apply IHl; intuition.
    apply NoDup_cons_iff in Hnodup; intuition.
Qed.

Lemma all_disjoint_app {A : Type} (ls1 ls2 : list (list A)) :
  all_disjoint ls1 ->
  all_disjoint ls2 ->
  (forall l1 l2, In l1 ls1 -> In l2 ls2 -> list_disjoint l1 l2) ->
  all_disjoint (ls1 ++ ls2).
Proof.
  revert ls2; induction ls1; intros ls2 Hdisj1 Hdisj2 Hdisj; simpl; auto.
  constructor.
  - apply IHls1; auto; intuition; inversion Hdisj1; subst; auto.
  - intros l Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hdisj1; subst; auto.
    + apply Hdisj; intuition.
Qed.

Lemma all_disjoint_injective {A B : Type} (ls : list A) (f : A -> list B) :
  (forall x y, x <> y -> list_disjoint (f x) (f y)) ->
  NoDup ls ->
  all_disjoint (map f ls).
Proof.
  induction ls; intros Hdisj Hnodup; simpl; constructor.
  - apply IHls; auto.
    apply NoDup_cons_iff in Hnodup; intuition.
  - intros l Hin y.
    apply in_map_iff in Hin.
    destruct Hin as [x [? Hin]]; subst.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup.
    apply Hdisj; intro HC; subst; congruence.
Qed.

Lemma Permutation_flatten_concat_ixs {A : Type} (rows : nat -> nat -> A) n :
  Permutation (first_n (seq_flatten rows) n)
              (concat
                 (map (fun i => map (fun j => rows i j)
                                 (col_ixs (range n) i))
                      (row_ixs (range n)))).
Proof.
  rewrite first_n_first_n'.
  unfold first_n'.
  rewrite concat_map_rows.
  apply Permutation_map.
  apply NoDup_Permutation.
  - apply NoDup_range.
  - apply NoDup_concat.
    + intros l Hin.
      apply in_map_iff in Hin.
      destruct Hin as [i [? Hin]]; subst.
      apply FinFun.Injective_map_NoDup.
      * intros j k Heq.
        apply injection_injective in Heq.
        -- inversion Heq; reflexivity.
        -- exists nat_f; apply nat_f_g.
      * unfold col_ixs. unfold compose.
        apply map_injection.
        -- intros j k Hin1 Hin2 Heq.
           apply filter_In in Hin1; apply filter_In in Hin2.
           destruct Hin1 as [Hin1 Hj]; destruct Hin2 as [Hin2 Hk].
           destruct (nat_f j) eqn:H0; destruct (nat_f k) eqn:H1.
           simpl in *.
           apply Nat.eqb_eq in Hj; apply Nat.eqb_eq in Hk; subst.
           rewrite <- H0 in H1; apply injection_injective in H1; auto.
           exists nat_g; apply nat_g_f.
        -- apply NoDup_filter, NoDup_range.
    + unfold row_ixs, col_ixs, compose; simpl.
      rewrite map_app; simpl.
      apply all_disjoint_app.
      * apply all_disjoint_injective.
        -- intros i j Hneq k [H0 H1].
           apply in_map_iff in H0; destruct H0 as [x [? H0]].
           apply in_map_iff in H0; destruct H0 as [y [? H0]].
           apply in_map_iff in H1; destruct H1 as [z [? H1]].
           apply in_map_iff in H1; destruct H1 as [w [? H1]].
           subst.
           apply injection_injective in H3.
           2: { exists nat_f; apply nat_f_g. }
           inversion H3; subst; congruence.
        -- apply NoDup_range.
      * apply all_disjoint_single.
      * intros l1 l2 Hin1 Hin2 i [H0 H1]. 
        simpl in *.
        destruct Hin2; auto.
        subst.
        apply in_map_iff in Hin1.
        apply in_map_iff in H1.
        destruct Hin1 as [j [HHeq Hin1]]; subst.
        destruct H1 as [k [HHeq Hin2]]; subst.
        apply in_map_iff in H0.
        destruct H0 as [m [Heq Hin0]]; subst.
        apply in_map_iff in Hin2.
        destruct Hin2 as [o [Heq' Hin2]]; subst.
        apply in_map_iff in Hin0.
        destruct Hin0 as [p [Heq' Hin0]]; subst.
        apply filter_In in Hin0.
        destruct Hin0.
        apply filter_In in Hin2.
        destruct Hin2.
        apply injection_injective in Heq.
        2: { exists nat_f; apply nat_f_g. }
        inversion Heq; subst; clear Heq.
        rewrite 2!range_seq in Hin1.
        apply in_seq in Hin1. lia.
  - intro k; split; intro Hin.
    + apply in_concat.
      destruct (nat_f k) as [i j] eqn:Hk.
      exists (map (fun j0 : nat => nat_g (i, j0)) (col_ixs (range n) i)).
      split.
      * apply in_map_iff.
        exists i; intuition.
        unfold row_ixs.
        rewrite range_seq.
        apply in_seq. split; try lia.
        simpl.
        assert (In ((fst ∘ nat_f) k) (map (fst ∘ nat_f) (range n))).
        { apply in_map; auto. }
        unfold compose in H. 
        rewrite Hk in H. simpl in H.
        apply list_max_spec in H. unfold compose. lia.
      * apply in_map_iff.
        exists j. split.
        -- rewrite <- Hk; apply nat_g_f.
        -- unfold col_ixs.
           apply in_map_iff. unfold compose. exists k. split.
           ++ rewrite Hk; reflexivity.
           ++ apply filter_In. split; auto.
              rewrite Hk. apply Nat.eqb_refl.
    + apply in_concat in Hin; destruct Hin as [l [Hin1 Hin2]].
      apply in_map_iff in Hin1; destruct Hin1 as [i [? Hin1]]; subst.
      apply in_map_iff in Hin2; destruct Hin2 as [j [? Hin2]]; subst.
      unfold row_ixs in Hin1; rewrite range_seq in Hin1.
      apply in_seq in Hin1; simpl in Hin1.
      unfold col_ixs in Hin2; apply in_map_iff in Hin2.
      destruct Hin2 as [k [? Hin2]]; subst.
      apply filter_In in Hin2; destruct Hin2 as [H0 H1].
      unfold compose; destruct (nat_f k) eqn:Hk. simpl.
      apply Nat.eqb_eq in H1; subst; rewrite <- Hk, nat_g_f; auto.
Qed.

Lemma sum_Q_list_concat (ls : list (list Q)) :  
  sum_Q_list (concat ls) == sum_Q_list (map sum_Q_list ls).
Proof.
  induction ls; simpl; try lra.
  rewrite sum_Q_list_app; rewrite IHls; reflexivity.
Qed.

(* Fixpoint get {A : Type} (default : A) (l : list A) (n : nat) : A := *)
(*   match l with *)
(*   | [] => default *)
(*   | (x :: xs) => match n with *)
(*                | O => x *)
(*                | S n' => get default xs n' *)
(*                end *)
(*   end. *)

Lemma list_rel_length {A B : Type} (l1 : list A) (l2 : list B) (R : A -> B -> Prop) :
  list_rel R l1 l2 ->
  length l1 = length l2.
Proof. induction 1; simpl; auto. Qed.

(* Lemma list_rel_get {A B : Type} (l1 : list A) (l2 : list B) (R : A -> B -> Prop) (defA : A) (defB : B) : *)
(*   R defA defB -> *)
(*   list_rel R l1 l2 <-> length l1 = length l2 /\ forall i, R (get defA l1 i) (get defB l2 i). *)
(* Proof. *)
(*   intro Hdef; split. *)
(*   - induction 1; split; simpl; intuition; destruct i; auto. *)
(*   - revert l2; induction l1; intros l2 [Hlen Hget]. *)
(*     + destruct l2. *)
(*       * constructor. *)
(*       * simpl in Hlen; lia. *)
(*     + destruct l2. *)
(*       * simpl in Hlen; lia. *)
(*       * constructor. *)
(*         -- apply (Hget O). *)
(*         -- apply IHl1; intuition; apply (Hget (S i)). *)
(* Qed. *)

Lemma list_rel_map {A B C D: Type} (l1 : list A) (l2 : list B)
      (R : C -> D -> Prop) (f : A -> C) (g : B -> D) :
  list_rel (fun x y => R (f x) (g y)) l1 l2 ->
  list_rel R (map f l1) (map g l2).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma sub_perm_map {A B : Type} (l1 l2 : list A) (f : A -> B) :
  sub_perm l1 l2 -> sub_perm (map f l1) (map f l2).
Proof.
  unfold sub_perm; intros [l Hperm].
  exists (map f l). rewrite <- map_app.
  apply Permutation_map; auto.
Qed.

Lemma filter_app_exists {A : Type} (f : A -> bool) (l l1 l2 : list A) :
  filter f l = l1 ++ l2 ->
  exists l1' l2', l = l1' ++ l2' /\ filter f l1' = l1 /\ filter f l2' = l2.
Proof.
  revert l1 l2; induction l; simpl; intros l1 l2 Hfilter.
  - symmetry in Hfilter; apply app_eq_nil in Hfilter.
    destruct Hfilter; subst; exists [], []; intuition.
  - destruct (f a) eqn:Ha.
    + destruct l1, l2; simpl in *.
      * inversion Hfilter.
      * inversion Hfilter; subst.
        exists [], (a0 :: l); intuition; simpl; rewrite Ha; reflexivity.
      * rewrite app_nil_r in Hfilter.
        inversion Hfilter; subst.
        exists (a0 :: l), []; intuition; simpl; rewrite Ha; reflexivity.
      * inversion Hfilter; subst.
        apply IHl in H1.
        destruct H1 as [l1' [l2' [? [H0 H1]]]]; subst.
        exists (a0 :: l1'), l2'; simpl; rewrite Ha; intuition.
    + apply IHl in Hfilter. destruct Hfilter as [l1' [l2' [? [H0 H1]]]]; subst.
      exists (a :: l1'), l2'; simpl; rewrite Ha; intuition.
Qed.

Lemma not_in_filter_orb (f : nat -> bool) (l : list nat) (n : nat) :
  ~ In n l ->
  filter f l = filter (fun m => (m =? n) || f m) l.
Proof.
  induction l; intros Hnotin; simpl; auto.
  destruct (f a) eqn:Ha.
  - rewrite orb_true_r; rewrite IHl; intuition.
  - rewrite orb_false_r.
    destruct (Nat.eqb_spec a n); subst.
    + exfalso; apply Hnotin; left; reflexivity.
    + apply IHl; intuition.
Qed.

Lemma in_filter_orb {A : Type} (l : list A) (f g : A -> bool) :
  (forall x, In x (filter (fun y => f y || g y) l) -> g x = false) ->
  forall x, In x l -> g x = false.
Proof.
  intros Heq x Hin.
  destruct (g x) eqn:Hgx; auto.
  specialize (Heq x).
  assert (In x (filter (fun y => f y || g y) l)).
  { apply filter_In; intuition. }
  apply Heq in H. congruence.
Qed.

Lemma NoDup_app_disjoint {A : Type} (l1 l2 : list A) :
  NoDup (l1 ++ l2) ->
  list_disjoint l1 l2.
Proof.
  revert l2; induction l1; simpl; intros l2 Hnodup x [H0 H1].
  - inversion H0.
  - apply NoDup_cons_iff in Hnodup.
    destruct Hnodup.
    simpl in H0. destruct H0; subst.
    + apply H; apply in_or_app; right; auto.
    + eapply IHl1; eauto.
Qed.

Lemma nodup_filter_orb_app (f : nat -> bool) (l l1 l2 : list nat) (n : nat) :
  NoDup l ->
  f n = false ->
  filter (fun i => (i =? n) || f i) l = l1 ++ n :: l2 ->
  filter f l = l1 ++ l2.
Proof.
  intros Hnodup Hfalse Hfilter.
  apply filter_app_exists in Hfilter.
  destruct Hfilter as [l1' [l2' [? [H0 H1]]]]; subst.
  replace (n :: l2) with ([n] ++ l2) in H1 by reflexivity.
  apply filter_app_exists  in H1.
  destruct H1 as [l1'' [l2'' [? [H1 H2]]]]; subst.
  assert (filter f l1'' = []).
  { apply filter_nil.
    intros x Hin.
    apply in_filter_orb with (l:=l1'') (f0:=fun i => i =? n); auto.
    rewrite H1; intros i []; subst; auto. inversion H. }
  assert (In n l1'').
  { cut (In n (filter (fun i => (i =? n) || f i) l1'')).
    { intro Hin; apply filter_In in Hin; firstorder. }
    rewrite H1; left; reflexivity. }
  pose proof Hnodup as Hnodup1.
  rewrite app_assoc in Hnodup1.
  apply NoDup_app in Hnodup1.
  apply NoDup_app_comm in Hnodup.
  apply NoDup_app in Hnodup.
  apply NoDup_app_disjoint in Hnodup.
  apply NoDup_app_disjoint in Hnodup1.
  unfold list_disjoint in *.
  simpl. rewrite 2!filter_app. rewrite H. simpl.
  f_equal; apply not_in_filter_orb; intuition.
  - eapply Hnodup1; eauto.
  - eapply Hnodup; eauto.
Qed.

Lemma inc_nodup_permutation_filter_orb (l1 l2 : list nat) :
  incl l1 l2 ->
  NoDup l1 ->
  NoDup l2 ->
  Permutation l1 (filter (fun i => existsb (eqb i) l1) l2).
Proof.
  revert l2. induction l1; intros l2 Hincl Hnodup1 Hnodup2; simpl.
  - rewrite filter_nil; auto.
  - assert (H: In a (filter (fun i : nat => (i =? a) || existsb (Nat.eqb i) l1) l2)).
    { apply filter_In. split; intuition; rewrite Nat.eqb_refl; reflexivity. }
    apply in_split in H.
    destruct H as [l [l' Heq]].
    rewrite Heq.
    apply Permutation_cons_app.
    apply nodup_filter_orb_app in Heq; auto.
    rewrite <- Heq.
    apply IHl1; auto.
    + intros x Hin; apply Hincl; right; auto.
    + inversion Hnodup1; auto.
    + apply existsb_not_in.
      apply NoDup_cons_iff in Hnodup1; intuition.
Qed.

Lemma Permutation_filter_existsb (l : list nat) :
  NoDup l ->
  Permutation l (filter (fun i => existsb (eqb i) l) (range (S (list_max l)))).
Proof.
  intro Hnodup.
  apply inc_nodup_permutation_filter_orb; auto.
  - intros x Hin; apply in_range_list_max; auto.
  - apply NoDup_range.
Qed.

Lemma sub_perm_range_list_max (l : list nat) :
  NoDup l ->
  sub_perm l (range (S (list_max l))).
Proof.
  intros Hnodup.
  exists (filter (negb ∘ fun i => existsb (eqb i) l) (range (S (list_max l)))).
  etransitivity.
  apply Permutation_app_tail, Permutation_filter_existsb; auto.
  apply Permutation_filter_partition.
Qed.

Lemma list_rel_Qle_sup_ixs (l : list nat) (i : nat) (rows : nat -> nat -> Q) (sups : nat -> Q) :
  (forall i j, 0 <= rows i j) ->
  (forall i, supremum (sups i) (partial_sum (rows i))) ->
  list_rel (fun l k => sum_Q_list l <= sups k)
           (map (fun i0 => map (fun j => rows i0 j) (col_ixs (range i) i0)) l) l.
Proof.
  intros Hnonneg Hsups; induction l; simpl; constructor; auto.
  eapply Qle_trans.
  2: { specialize (Hsups a). destruct Hsups.
       unfold upper_bound in H. simpl in H.
       apply (H (S (list_max (col_ixs (range i) a)))). }
  unfold partial_sum.
  rewrite first_n_first_n'. unfold first_n'.
  replace (fun j => rows a j) with (rows a) by reflexivity.
  apply sub_perm_sum_Q_list; auto.
  - intros x Hin. apply in_map_iff in Hin.
    destruct Hin as [? [? Hin]]; subst; auto.
  - apply sub_perm_map.
    apply sub_perm_range_list_max.
    unfold col_ixs. simpl.
    apply map_injection.
    + unfold compose.
      intros x y Hinx Hiny Heq.
      apply filter_In in Hinx; destruct Hinx as [Hinx H0].
      apply filter_In in Hiny; destruct Hiny as [Hiny H1].
      destruct (nat_f x) eqn:Hx.
      destruct (nat_f y) eqn:Hy.
      apply Nat.eqb_eq in H0; apply Nat.eqb_eq in H1; simpl in *; subst.
      rewrite <- Hx in Hy. apply injection_injective in Hy; auto.
      exists nat_g; apply nat_g_f.
    + apply NoDup_filter, NoDup_range.
Qed.

Lemma forall_Qlt_Qle (x ub : Q) :
  (forall y, y < x -> y <= ub) ->
  x <= ub.
Proof.
  intros Hle.
  destruct (Qlt_le_dec ub x); auto.
  assert (H0: (x + ub) / 2 < x).
  { apply Qlt_shift_div_r; lra. }
  assert (H1: ub < (x + ub) / 2).
  { apply Qlt_shift_div_l; lra. }
  specialize (Hle ((x + ub) / 2) H0); lra.
Qed.

(* Lemma forall_list_rel_Qlt_Qle (l : list Q) (ub : Q) : *)
(*   (forall l', list_rel Qlt l' l -> sum_Q_list l' <= ub) -> *)
(*   sum_Q_list l <= ub. *)
(* Proof. *)
(*   revert ub. *)
(*   induction l; simpl; intros ub Hle. *)
(*   - specialize (Hle [] (list_rel_nil _)); simpl in Hle; auto. *)
(*   - cut (sum_Q_list l <= ub - a). *)
(*     { lra. } *)
(*     apply IHl. *)
(*     intros l' Hrel. *)
(*     cut (a + sum_Q_list l' <= ub). *)
(*     { lra. } *)
(*     apply forall_Qlt_Qle; intros y Hlt. *)
(*     assert (y - sum_Q_list l' < a). *)
(*     { lra. } *)
(*     specialize (Hle (((y - sum_Q_list l' + a) / 2) :: l')). *)
(*     simpl in Hle. *)
(*     eapply Qle_trans. *)
(*     2: { apply Hle; constructor; auto; apply Qlt_shift_div_r; lra. } *)
(*     cut (y - sum_Q_list l' <= (y - sum_Q_list l' + a) / 2). *)
(*     { lra. } *)
(*     apply Qle_shift_div_l; lra. *)
(* Qed. *)

Lemma concat_map_nil {A B : Type} (l : list A) :
  concat (map (const (@nil B)) l) = [].
Proof. induction l; simpl; auto. Qed.

Lemma rows_sups_upper_bound (rows : list (nat -> Q)) (sups : list Q) (ub : Q) :
  (forall row, In row rows -> forall i, 0 <= row i) ->
  list_rel (fun sup row => supremum sup (partial_sum row)) sups rows ->
  (forall j, sum_Q_list (map (fun row => sum_Q_list (first_n' row j)) rows) <= ub) ->
  sum_Q_list sups <= ub.
Proof.
  revert ub rows. induction sups; intros ub rows Hnonneg Hrel Hle.
  - inversion Hrel; subst. simpl in *; apply (Hle O).
  - simpl.
    inversion Hrel; subst.
    assert (H: forall row : nat -> Q, In row ys -> forall i : nat, 0 <= row i).
    { intros row Hin i; apply Hnonneg; right; auto. }
    specialize (IHsups (ub - a) ys H H3); clear H.
    cut (sum_Q_list sups <= ub - a).
    { lra. }
    apply IHsups; intro j.
    simpl in Hle.
    clear Hrel H3 IHsups.
    cut (a + sum_Q_list (map (fun row => sum_Q_list (first_n' row j)) ys) <= ub).
    { lra. }
    apply forall_Qlt_Qle.
    set (b := sum_Q_list (map (fun row : nat -> Q => sum_Q_list (first_n' row j)) ys)).
    intros x Hlt.
    set (eps := a + b - x).
    assert (Heps: 0 < eps).
    { unfold eps; lra. }
    apply supremum_converges with (eps:=eps) in H1; auto.
    + destruct H1 as [k Hepsle].
      set (c := sum_Q_list (map (fun row : nat -> Q => sum_Q_list (first_n' row k)) ys)).
      destruct (Nat.leb_spec0 j k).
      * specialize (Hle k). unfold partial_sum in *.
        rewrite first_n_first_n' in Hepsle.
        unfold eps in Heps.
        assert (H0: x < sum_Q_list (first_n' y k) + b).
        { unfold eps in Hepsle; lra. }
        assert (H1: b <= c).
        { unfold b, c.
          apply sum_Q_list_pointwise_Qle.
          apply list_rel_map.
          apply list_rel_reflexive.
          intros row Hin.
          rewrite <- 2!first_n_first_n'.
          apply sum_Q_list_first_n_Qle; auto; apply Hnonneg; right; auto. }
        unfold b, c, eps in *; lra.
      * specialize (Hle j). unfold partial_sum in *.
        rewrite first_n_first_n' in Hepsle.
        unfold eps in Heps.
        assert (H0: (k < j)%nat).
        { lia. }
        assert (H1: x < sum_Q_list (first_n' y j) + b).
        { unfold eps in Hepsle.
          apply Qlt_le_trans with (y:=sum_Q_list (first_n' y k) + b).
          - lra.
          - cut (sum_Q_list (first_n' y k) <= sum_Q_list (first_n' y j)).
            { lra. }
            rewrite <- 2!first_n_first_n'.
            apply sum_Q_list_first_n_Qle; try lia.
            intros i; apply Hnonneg; left; reflexivity. }
        assert (H2: c <= b).
        { unfold b, c.
          apply sum_Q_list_pointwise_Qle.
          apply list_rel_map.
          apply list_rel_reflexive.
          intros row Hin.
          rewrite <- 2!first_n_first_n'.
          apply sum_Q_list_first_n_Qle; try lia; apply Hnonneg; right; auto. }
        unfold b, c, eps in *; lra.
    + apply chain_partial_sum.
      apply Hnonneg; left; reflexivity.
Qed.

(* Lemma map_rows {A B C : Type} (rows : A -> B -> C) (l1 : list B) (l2 : list A) (f : list C -> C) : *)
(*   map (fun g : B -> C => f (map g l1)) (map rows l2) = *)
(*   map f (map (fun x : A => map (rows x) l1) l2). *)
(* Proof. induction l2; simpl; auto; rewrite IHl2; auto. Qed. *)

(* Lemma jsdfg (rows : nat -> nat -> Q) (sups : nat -> Q) (ub : Q) (n : nat) : *)
(*   (forall i j, 0 <= rows i j) -> *)
(*   (forall i, supremum (sups i) (partial_sum (rows i))) -> *)
(*   (forall j, sum_Q_list (concat (map (fun i => map (rows i) (range j)) (range n))) <= ub) -> *)
(*   partial_sum sups n <= ub. *)
(* Proof. *)
(*   intros Hnonneg Hsups Hle. *)
(*   apply jsdfgsdf with (rows := first_n rows n). *)
(*   - intros row Hin i. apply in_first_n in Hin. *)
(*     destruct Hin as [j [Hle' Heq]]; subst; auto. *)
(*   - clear Hle. clear ub. *)
(*     induction n; simpl; try constructor. *)
(*     simpl. apply list_rel_app; split; auto; constructor; auto; constructor. *)
(*   - intro j. *)
(*     specialize (Hle j). *)
(*     rewrite sum_Q_list_concat in Hle.  *)
(*     rewrite first_n_first_n'. *)
(*     unfold first_n'. *)
(*     eapply Qle_trans; eauto. *)
(*     apply lkmdfgkdfgdfg. *)
(*     apply list_eq_sum_Q_list. *)
(*     apply odfg. *)
(* Qed. *)

Lemma map_nat_f_g_rows' (rows : nat -> nat -> Q) (l1 l2 : list nat) :
  map (map (fun n0 : nat => let (i, j) := nat_f n0 in rows i j))
      (map (fun i : nat => map (fun j : nat => nat_g (i, j)) l2) l1) =
  map (fun row : nat -> Q => map row l2) (map rows l1).
Proof.
  revert l2.
  induction l1; intros l2; simpl; auto.
  rewrite IHl1. f_equal.
  clear IHl1. clear l1.
  induction l2; simpl; auto.
  rewrite nat_f_g. rewrite IHl2; auto.
Qed.

Lemma supremum_flatten (rows : nat -> nat -> Q) (sups : nat -> Q) (sup : Q) :
  (forall i j, 0 <= rows i j) ->
  (forall i, supremum (sups i) (partial_sum (rows i))) ->
  supremum sup (partial_sum sups) ->
  supremum sup (partial_sum (seq_flatten rows)).
Proof.
  intros Hnonneg Hsups [Hub Hlub].
  split.
  - intro i. simpl in *.
    unfold partial_sum.
    rewrite sum_Q_list_permutation.
    2: { apply Permutation_flatten_concat_ixs. }
    rewrite sum_Q_list_concat.
    unfold row_ixs.
    apply Qle_trans with (y:= partial_sum sups (S (list_max (map (fst ∘ nat_f) (range i))))).
    2: { apply Hub. }
    unfold partial_sum. rewrite first_n_first_n'. unfold first_n'.
    apply sum_Q_list_pointwise_Qle.
    apply list_rel_map.
    apply list_rel_Qle_sup_ixs; auto.
  - intros ub H.
    apply Hlub.
    intro i. simpl.
    unfold upper_bound in H; simpl in *.
    apply rows_sups_upper_bound with (rows := first_n rows i).
    + intros row Hin j. apply in_first_n in Hin.
      destruct Hin as [k [Hle Heq]]; subst; auto.
    + rewrite 2!first_n_first_n'.
      apply list_rel_map.
      induction i; try constructor.
      simpl. apply list_rel_app; split; auto; constructor; auto; constructor.
    + intro j.
      apply Qle_trans with (y := sum_Q_list (concat (map (fun row => first_n row j) (first_n rows i)))).
      { rewrite sum_Q_list_concat. rewrite first_n_first_n'.
        apply Qeq_Qle.
        apply sum_Q_list_pointwise_Qeq.
        apply list_rel_map.
        apply list_rel_map.
        unfold first_n'.
        induction i. simpl. constructor.
        - simpl. rewrite map_app; simpl.
          apply list_rel_app; split; auto.
          constructor.
          + rewrite first_n_first_n'; reflexivity.
          + constructor. }
      rename i into n.
      rename j into m.
      set (l := concat (map (fun i => map (fun j => nat_g (i, j)) (range m)) (range n))).
      (** There is some index k for which the goal inequality follows
          by transitivity using H. *)
      set (k := S (list_max l)).
      specialize (H k).
      eapply Qle_trans; eauto.
      unfold partial_sum.
      apply sub_perm_sum_Q_list.
      * intros x Hin. apply in_first_n in Hin. destruct Hin as [i [Hle Heq]]; subst.
        unfold seq_flatten; destruct (nat_f i); auto.
      * exists (map (seq_flatten rows) (filter (fun n => negb (existsb (Nat.eqb n) l)) (range k))).
        replace (concat (map (fun row : nat -> Q => first_n row m) (first_n rows n))) with
            (map (seq_flatten rows) l).
        2: { unfold seq_flatten. unfold l. rewrite concat_map.
             f_equal.
             replace (map (fun row => first_n row m) (first_n rows n)) with
                 (map (fun row => first_n' row m) (first_n' rows n)).
             { apply map_nat_f_g_rows'. }
             rewrite first_n_first_n'.
             apply map_ext; intros f; rewrite first_n_first_n'; reflexivity. }
        etransitivity.
        -- apply Permutation_app_tail.
           eapply Permutation_map.
           apply nodup_incl_permutation with (l2:=range k).
           ++ 
             unfold l. apply NoDup_concat.
             ** intros l' Hin.
                apply in_map_iff in Hin.
                destruct Hin as [x [Heq Hin]]; subst.
                apply FinFun.Injective_map_NoDup.
                { intros y z Heq. apply injection_injective in Heq; inversion Heq; auto.
                  exists nat_f; apply nat_f_g. }
                apply NoDup_range.
             ** apply all_disjoint_injective.
                { intros x y Hneq z [H0 H1]. 
                  apply in_map_iff in H0; destruct H0 as [i [? H0]]; subst.
                  apply in_map_iff in H1; destruct H1 as [j [? H1]]; subst.
                  apply injection_injective in H2; inversion H2; subst; try congruence.
                  exists nat_f; apply nat_f_g. }
                apply NoDup_range.
           ++ apply NoDup_range.
           ++ unfold l; intros x Hin.
              assert (Hle: (x < k)%nat).
              { apply le_lt_n_Sm; apply list_max_spec; auto. }
              apply in_concat in Hin.
              destruct Hin as [l' [Hin Hin']].
              apply in_map_iff in Hin; destruct Hin as [y [? Hin]]; subst.
              apply in_map_iff in Hin'. destruct Hin' as [z [? Hin']]; subst.
              rewrite range_seq in *.
              apply in_seq in Hin.
              apply in_seq in Hin'.
              apply in_seq. simpl in *.
              split; try lia.
        -- rewrite first_n_first_n'.
           unfold first_n'.
           rewrite <- map_app.
           apply Permutation_map.
           apply Permutation_filter_partition.
Qed.

Lemma supremum_le (s : nat -> Q) (c sup : Q) :
  (forall i, c <= s i) ->
  supremum sup s ->
  c <= sup.
Proof.
  intros Hle [Hub Hlub]; simpl in *.
  apply Qle_trans with (y := s O); eauto; apply Hub.
Qed.

Lemma partial_sum_nonnegative (s : nat -> Q) (i : nat) :
  (forall j, 0 <= s j) ->
  0 <= partial_sum s i.
Proof.
  intros Hle; unfold partial_sum; induction i; simpl; try lra.
  rewrite sum_Q_list_app; simpl; specialize (Hle i); lra.
Qed.

Lemma supremum_product (s1 s2 : nat -> option (list bool)) (a b : Q) :
  supremum a (partial_sum (option_measure ∘ s1)) ->
  supremum b (partial_sum (option_measure ∘ s2)) ->
  supremum (a * b)
           (partial_sum (option_measure ∘ seq_product MonoidList s1 s2)).
Proof.
  intros Hsupa Hsupb.
  eapply supremum_f_Qeq.
  - apply partial_sum_proper.
    intro i.
    unfold compose. rewrite seq_product_flatten. reflexivity.
  - eapply Proper_supremum.
    { reflexivity. }
    { apply Proper_partial_sum, seq_flatten_compose. }
    apply supremum_flatten with (sups := fun i => option_measure (s1 i) * b).
    + intros i j; apply option_measure_nonnegative.
    + intros i.
      eapply supremum_f_Qeq.
      apply partial_sum_proper.
      intro j. symmetry. apply option_measure_product.
      eapply supremum_f_Qeq.
      intro j. symmetry. apply partial_sum_scalar.
      apply supremum_scalar; auto.
      apply option_measure_nonnegative.
    + eapply supremum_f_Qeq.
      apply partial_sum_proper.
      intro j.
      rewrite 2Qmult_comm. reflexivity.
      eapply equ_supremum.
      apply Qeq_equ. apply Qmult_comm.
      eapply supremum_f_Qeq.
      intro j. symmetry. apply partial_sum_scalar.
      apply supremum_scalar; auto.
      eapply supremum_le; eauto.
      intro i; unfold compose.
      apply partial_sum_nonnegative; intros; apply option_measure_nonnegative.
Qed.

Lemma seq_bijection_seq_star (r1 r2 : RE bool) :
  seq_bijection (RE_sequence (RE_seq (RE_star r1) r2))
                (seq_flatten
                   (fun i j => seq_product MonoidList
                                        (seq_reps_n MonoidList (RE_sequence r1) i)
                                        (RE_sequence r2) j)).
Proof.
  exists (fun n => let (i, j) := nat_f n in
           let (i0, j0) := nat_f i in
           nat_g (i0, nat_g (j0, j))).
  split.
  - exists (fun n => let (i, j) := nat_f n in
             let (i0, j0) := nat_f j in
             nat_g (nat_g (i, i0), j0)).
    split; intro n.
    + destruct (nat_f n) eqn:Hn.
      destruct (nat_f n0) eqn:Hn0.
      rewrite 2!nat_f_g.
      rewrite <- Hn0, nat_g_f, <- Hn, nat_g_f; reflexivity.
    + destruct (nat_f n) eqn:Hn.
      destruct (nat_f n1) eqn:Hn0.
      rewrite 2!nat_f_g.
      rewrite <- Hn0, nat_g_f, <- Hn, nat_g_f; reflexivity.
  - intro i; simpl; unfold seq_product, seq_reps, seq_flatten.
    destruct (nat_f i) eqn:Hi.
    destruct (nat_f n) eqn:Hn.
    rewrite 2!nat_f_g; reflexivity.
Qed.

Lemma supremum_seq_reps_n (s : nat -> option (list bool)) (a : Q) (n : nat) :
  supremum a (partial_sum (option_measure ∘ s)) ->
  supremum (Qpow a n) (partial_sum (option_measure ∘ seq_reps_n MonoidList s n)).
Proof.
  induction n.
  - unfold compose; simpl; intros _.
    apply const_supremum'.
    + intro i; unfold partial_sum; simpl; rewrite sum_Q_list_app; simpl.
      assert (0 <= option_measure (seq_one [] i)).
      { apply option_measure_nonnegative. }
      lra.
    + exists (S O).
      intros n Hle; apply Qeq_equ; induction n; unfold partial_sum.
      * inversion Hle.
      * destruct n.
        -- reflexivity.
        -- assert (H: (1 <= S n)%nat).
           { lia. }
           apply IHn in H.
           unfold partial_sum in H. simpl in H.
           rewrite sum_Q_list_app in H. simpl in H.
           simpl. rewrite 2!sum_Q_list_app. simpl.
           lra.
  - intro Hsup. simpl. unfold compose. simpl.
    eapply Proper_supremum.
    { apply Qeq_equ. apply Qmult_comm. }
    { reflexivity. }
    apply supremum_product; auto.
Qed.

Lemma RE_star_seq_geometric (r1 r2 : RE bool) (a b : Q) :
  0 <= a -> 0 <= b -> b < 1 ->
  supremum a (partial_sum (option_measure ∘ RE_sequence r2)) ->
  supremum b (partial_sum (option_measure ∘ RE_sequence r1)) ->
  supremum (a / (1 - b)) (partial_sum (option_measure ∘ RE_sequence (RE_seq (RE_star r1) r2))).
Proof.
  intros Ha0 Hb0 Hb1 Hsup1 Hsup2.
  eapply seq_bijection_supremum.
  3: {
    eapply seq_bijection_compose.
    symmetry. apply seq_bijection_seq_star. }
  - intros; apply option_measure_nonnegative.
  - intros; apply option_measure_nonnegative.
  - eapply supremum_f_Qeq.
    + apply partial_sum_proper.
      symmetry; intro j.
      apply f_Qeq_equ, seq_flatten_compose; auto.
    +  apply supremum_flatten with (sups := geometric_sequence a b).
       * intros i j; apply option_measure_nonnegative.
       * intros j.
         unfold geometric_sequence.
         eapply Proper_supremum.
         { apply Qeq_equ, Qmult_comm. }
         { reflexivity. }
         apply supremum_product; auto.
         apply supremum_seq_reps_n; auto.
       * apply geometric_series'_supremum; lra.
Qed.

Lemma partial_sum_singleton_seq {A : Type} (f : option A -> Q) (x : A) (i : nat) :
  (1 <= i)%nat ->
  (f None == 0) ->
  partial_sum (fun j => f (seq_one x j)) i == f (Some x).
Proof.
  intros Hle Hnone.
  induction i.
  - inversion Hle.
  - rewrite partial_sum_S.
    destruct i.
    + unfold partial_sum; simpl; lra.
    + assert (H: (1 <= S i)%nat).
      { lia. }
      apply IHi in H; rewrite H.
      simpl; rewrite Hnone; lra.
Qed.

Lemma infer_fail_supremum {A : Type} (t : tree A) (n : nat) :
  wf_tree t ->
  unbiased t ->
  not_bound_in n t ->
  supremum (infer_fail n t)
           (partial_sum (option_measure ∘ RE_sequence (RE_of_tree_fail t n))).
Proof.
  generalize n.
  induction t; intros m Hwf Hunbiased Hnotbound.
  - unfold compose; simpl.
    apply const_supremum.
    intro i; apply Qeq_equ.
    rewrite partial_sum_const, sum_Q_list_repeat_0; lra.
  - unfold compose; simpl.
    destruct (Nat.eqb_spec n0 m); subst.
    + apply const_supremum'.
      * apply chain_partial_sum.
        intros; apply option_measure_nonnegative.
      * exists (S O).
        intros i Hle; apply Qeq_equ.
        apply partial_sum_singleton_seq; auto; reflexivity.
    + apply const_supremum.
      intro i; apply Qeq_equ.
      unfold option_measure; simpl.
      rewrite partial_sum_const, sum_Q_list_repeat_0; lra.
  - apply crunch_partial_sum_supremum.
    { intro i; apply option_measure_nonnegative. }
    eapply Proper_supremum_Q.
    + reflexivity.
    + etransitivity.
      apply partial_sum_proper; simpl.
      intro j; apply crunch_union_sum.
      intro j; apply partial_sum_linear.
    + simpl; inversion Hwf; inversion Hunbiased; inversion Hnotbound;
        subst; apply supremum_sum_Q; specialize (IHt1 m); specialize (IHt2 m).
      * intro i; apply partial_sum_increasing; auto.
        intro j; apply option_measure_nonnegative.
      * intro i; apply partial_sum_increasing; auto.
        intro j; apply option_measure_nonnegative.
      * eapply Proper_supremum.
        { apply Qeq_equ; rewrite H8; reflexivity. }
        apply f_Qeq_equ; intro i.
        apply partial_sum_measure_factor.
        apply supremum_scalar; auto; lra.
      * eapply Proper_supremum.
        { apply Qeq_equ; rewrite H8; reflexivity. }
        apply f_Qeq_equ; intro i.
        apply partial_sum_measure_factor.
        apply supremum_scalar; auto; lra.
  - rewrite infer_fail_fix, RE_of_tree_fail_fix.
    inversion Hwf; inversion Hunbiased; inversion Hnotbound; subst.
    destruct (RE_nonemptyb_spec (RE_of_tree_fail t m)).
    + apply RE_nonempty_RE_of_tree_fail_infer_fail in r; auto.
      apply RE_star_seq_geometric; auto.
      * apply infer_fail_0_le; auto.
      * apply infer_fail_0_le; auto.
      * apply infer_fail_lt_1; auto.
        assert (infer_fail m t + infer_fail n0 t <= 1).
        { apply infer_fail_infer_fail_le_1; auto. }
        lra.
    + apply RE_is_empty_not_nonempty in n1.
      assert (forall i, RE_sequence (RE_of_tree_fail t m) i = None).
      { intro i; apply RE_is_empty_sequence; auto. }
      apply supremum_f_Qeq with (f := const 0).
      { intro i. simpl. unfold compose, const.
        transitivity (partial_sum (const 0) i).
        { symmetry; apply partial_sum_0. }
        apply partial_sum_proper; intro j.
        unfold const, seq_product. simpl. destruct (nat_f j).
        rewrite H, option_mult_none_r; reflexivity. }
      apply RE_is_empty_infer_fail in n1; auto.
      eapply equ_supremum. apply Qeq_equ. rewrite n1, Qdiv_0_num; reflexivity.
      apply const_supremum; intro i; reflexivity.
Qed.

Lemma infer_f_supremum {A : Type} (t : tree A) (P : A -> bool) :
  wf_tree t ->
  unbiased t ->
  supremum (infer_f (fun x => if P x then 1 else 0) t)
           (partial_sum (option_measure ∘ tree_sequence_f t P)).
Proof.
  induction t; intros Hwf Hunbiased.
  - unfold compose, tree_sequence_f; simpl.
    destruct (P a) eqn:Ha.
    + apply const_supremum'.
      * apply chain_partial_sum.
        intros; apply option_measure_nonnegative.
      * exists (S O).
        intros i Hle; apply Qeq_equ.
        apply partial_sum_singleton_seq; auto; reflexivity.
    + apply const_supremum.
      intro i; apply Qeq_equ.
      unfold option_measure; simpl.
      rewrite partial_sum_const, sum_Q_list_repeat_0; lra.
  - apply const_supremum; intro i; apply Qeq_equ.
    unfold compose, option_measure; simpl.
    rewrite partial_sum_const, sum_Q_list_repeat_0; lra.
  - apply crunch_partial_sum_supremum.
    { intro i; apply option_measure_nonnegative. }
    eapply Proper_supremum_Q.
    + reflexivity.
    + etransitivity.
      apply partial_sum_proper.
      unfold tree_sequence. simpl.
      intro j; apply crunch_union_sum.
      intro j; apply partial_sum_linear.
    + simpl; inversion Hwf; inversion Hunbiased; subst; apply supremum_sum_Q.
      * intro i; apply partial_sum_increasing; auto.
        intro j; apply option_measure_nonnegative.
      * intro i; apply partial_sum_increasing; auto.
        intro j; apply option_measure_nonnegative.
      * eapply Proper_supremum.
        { apply Qeq_equ; rewrite H8; reflexivity. }
        apply f_Qeq_equ; intro i.
        apply partial_sum_measure_factor.
        apply supremum_scalar; auto; lra.
      * eapply Proper_supremum.
        { apply Qeq_equ; rewrite H8; reflexivity. }
        apply f_Qeq_equ; intro i.
        apply partial_sum_measure_factor.
        apply supremum_scalar; auto; lra.
  - unfold tree_sequence_f.
    rewrite infer_f_fix, RE_of_tree_f_fix.
    inversion Hwf; inversion Hunbiased; subst.
    destruct (RE_nonemptyb_spec (RE_of_tree_f t P)).
    + apply RE_nonempty_RE_of_tree_f_infer_f in r; auto.
      apply RE_star_seq_geometric; auto; try lra.
      * apply infer_fail_0_le; auto.
      * apply infer_fail_lt_1; auto.
        assert (infer_f (fun x => if P x then 1 else 0) t + infer_fail n t <= 1).
        { apply infer_f_infer_fail_le_1; auto.
          intro x; destruct (P x); lra. }
        lra.
      * apply infer_fail_supremum; auto.
    + apply RE_is_empty_not_nonempty in n0.
      assert (forall i, RE_sequence (RE_of_tree_f t P) i = None).
      { intro i; apply RE_is_empty_sequence; auto. }
      apply supremum_f_Qeq with (f := const 0).
      { intro i. simpl. unfold compose, const.
        transitivity (partial_sum (const 0) i).
        { symmetry; apply partial_sum_0. }
        apply partial_sum_proper; intro j.
        unfold const, seq_product. simpl. destruct (nat_f j).
        rewrite H, option_mult_none_r; reflexivity. }
      apply RE_is_empty_infer_f in n0; auto.
      eapply equ_supremum. apply Qeq_equ. rewrite n0, Qdiv_0_num; reflexivity.
      apply const_supremum; intro i; reflexivity.
Qed.

(** PLAN:
        Show a bijection (maybe trivial?) between the sequence and a
        flattened table where the nth row has measure equal to a^n*b
        where a is [infer_fail n t] and b is [infer_f P t]. The nth
        row is be the cartesian product of the nth repetitions of r1
        (seq_product_n r1 n) with r2 where the sequence is [RE_seq
        (RE_star r1) r2].
 *)

(** foster, kozen, netkat*)

Lemma infer_supremum {A : Type} (t : tree A) (P : A -> bool) (n : nat) :
  wf_tree t ->
  unbiased t ->
  (forall m, free_in m t -> m = n) ->
  not_bound_in n t ->
  supremum (infer (fun x => if P x then 1 else 0) t)
           (partial_sum (option_measure ∘ tree_sequence t P n)).
Proof.
  intros Hwf Hunbiased Hfree Hnotbound.
  unfold infer. eapply supremum_Qeq.
  { rewrite infer_f_lib_infer_fail_complement; eauto; reflexivity. }
  destruct (RE_nonemptyb_spec (RE_of_tree_f t P)).
  - apply RE_nonempty_infer_fail with (n0:=n) in r; auto.
    apply RE_star_seq_geometric; auto.
    + apply infer_f_expectation_0_le; auto.
      intros x; destruct (P x); lra.
    + apply infer_fail_0_le; auto.
    + apply infer_f_supremum; auto.
    + apply infer_fail_supremum; auto.
  - apply RE_is_empty_not_nonempty in n0.
    pose proof n0 as H.
    apply RE_is_empty_infer_f in H; auto.
    eapply supremum_Qeq.
    { rewrite H, Qdiv_0_num; reflexivity. }
    clear H.
    unfold tree_sequence.
    eapply supremum_f_Qeq.
    apply partial_sum_proper.
    intro x. unfold compose.
    rewrite RE_is_empty_sequence.
    + reflexivity.
    + apply RE_is_empty_seq2; auto.
    + apply const_supremum; intro i; apply Qeq_equ; apply partial_sum_0.
Qed.
