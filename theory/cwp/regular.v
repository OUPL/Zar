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
Import ListNotations.
Local Open Scope program_scope.

Require Import axioms.
Require Import infer.
Require Import misc.
Require Import order.
Require Import Q.
Require Import tree.

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

Definition seq_injection {A : Type} (s1 s2 : nat -> A) : Prop :=
  exists f : nat -> nat, injection f /\ forall i, s1 i = s2 (f i).

Definition seq_bijection {A : Type} (s1 s2 : nat -> A) : Prop :=
  exists f : nat -> nat, bijection f /\ forall i, s1 i = s2 (f i).

Instance Reflexive_seq_bijection {A : Type} : Reflexive (@seq_bijection A).
Proof. repeat (exists id; intuition). Qed.

Instance Symmetric_seq_bijection {A : Type} : Symmetric (@seq_bijection A).
Proof.
  intros s1 s2 [f [[g [Hgf Hfg]] Heq]].
  exists g. split; firstorder.
  rewrite Heq, Hfg; reflexivity.
Qed.

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

Lemma sub_perm_nil {A : Type} (l : list A) :
  sub_perm [] l.
(* Proof. exists [], l; firstorder. Qed. *)
Proof. exists l; apply Permutation_refl. Qed.

Lemma Permutation_filter {A : Type} (f : A -> bool) (l : list A) :
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

Lemma jkdfgf {A : Type} (f g : A -> bool) (l : list A) :
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
  apply Permutation_filter.
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

Definition singleton_seq {A : Type} (x : A) (i : nat) : option A :=
  match i with
  | O => Some x
  | _ => None
  end.

Lemma singleton_seq_none {A : Type} (x : A) (i : nat) :
  (0 < i)%nat ->
  singleton_seq x i = None.
Proof. intro Hlt; destruct i; try lia; reflexivity. Qed.

(** Interleave two infinite sequences together. *)
Definition seq_union {A : Type} (f g : nat -> A) (i : nat) : A :=
  match modulo i 2 with
  | O => f (div i 2)
  | _ => g (div i 2)%nat
  end.

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

(** Flatten a sequence of sequences via the bijection from nat to nat*nat. *)
Definition seq_flatten {A : Type} (f : nat -> nat -> A) (n : nat) : A :=
  let (i, j) := nat_f n in f i j.

(** Split a sequence into a sequence of sequences.*)
Definition seq_split {A : Type} (f : nat -> A) (i j : nat) : A :=
  let n := nat_g (i, j) in f n.

Definition MonoidList {A : Type} : Monoid (list A) :=
  {| monoid_plus := fun x y => app x y
   ; monoid_unit := [] |}.

Program Instance MonoidLawsList {A : Type} : MonoidLaws (@MonoidList A).
Next Obligation. intros ? ? ?; rewrite app_assoc; reflexivity. Qed.
Next Obligation. intro; reflexivity. Qed.
Next Obligation. intro; apply app_nil_r. Qed.

Definition option_mult {A : Type} (M : Monoid A) (x y : option A) : option A :=
  match (x, y) with
  | (Some l, Some r) => Some (monoid_plus M l r)
  | _ => None
  end.

(** Cartesian product of two monoid sequences. *)
Definition seq_product {A : Type} (M : Monoid A) (f g : nat -> option A) (n : nat)
  : option A :=
  let (i, j) := nat_f n in option_mult M (f i) (g j).

Definition seq_product_n {A : Type} (M : Monoid A) (f g : nat -> option A) (n i : nat)
  : option A :=
  Nat.iter n (fun f' => seq_product M f' g) f i.

Definition seq_reps_n {A : Type} (M : Monoid A) (f : nat -> option A) (n : nat)
  : nat -> option A :=
  seq_product_n M (singleton_seq (monoid_unit M)) f n.

(** Sequence containing all finite repetitions of elements of the
    argument sequence. *)
Definition seq_reps {A : Type} (M : Monoid A) (f : nat -> option A) : nat -> option A :=
  seq_flatten (fun n i => seq_reps_n M f n i).

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

(* Inductive RE_is_epsilon {A : Type} : RE A -> Prop := *)
(* | RE_is_epsilon_epsilon : RE_is_epsilon (@RE_epsilon _) *)
(* | RE_is_empty_seq1 : forall r1 r2, *)
(*     RE_is_empty r1 -> *)
(*     RE_is_empty (RE_seq r1 r2) *)
(* | RE_is_empty_seq2 : forall r1 r2, *)
(*     RE_is_empty r2 -> *)
(*     RE_is_empty (RE_seq r1 r2) *)
(* | RE_is_empty_choice : forall r1 r2, *)
(*     RE_is_empty r1 -> *)
(*     RE_is_empty r2 -> *)
(*     RE_is_empty (RE_choice r1 r2). *)

(* Inductive RE_is_single {A : Type} : A -> RE A -> Prop := *)
(* | RE_is_single_cons : forall x r, *)
(*     RE_is_epsilon r -> *)
(*     RE_is_single x (RE_cons x r) *)
(* | RE_is_single_seq : forall x r1 r2, *)
(*     RE_is_single x r1 -> *)
(*     RE_is_epsilon r2 -> *)
(*     RE_is_single x (RE_seq r1 r2) *)
(* | RE_is_single_choice : forall x r1 r2, *)
(*     RE_is_single x r1 -> *)
(*     RE_is_single x r2 -> *)
(*     RE_is_single x (RE_choice r1 r2). *)

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

(* Fixpoint RE_of_tree_lib {A : Type} (t : tree A) (P : A -> bool) : RE bool := *)
(*   match t with *)
(*   | Leaf x => if P x then @RE_epsilon bool else @RE_empty bool *)
(*   | Fail _ _ => @RE_empty bool *)
(*   | Choice _ t1 t2 => RE_choice (RE_cons true (RE_of_tree_lib t1 P)) *)
(*                                (RE_cons false (RE_of_tree_lib t2 P)) *)
(*   | Fix lbl t1 => if RE_is_fullb (RE_of_tree_fail t1 lbl) *)
(*                  then @RE_epsilon bool *)
(*                  else RE_seq (RE_star (RE_of_tree_fail t1 lbl)) (RE_of_tree_lib t1 P) *)
(*   end. *)

Fixpoint RE_of_tree_lib {A : Type} (t : tree A) (P : A -> bool) : RE bool :=
  match t with
  | Leaf x => if P x then @RE_epsilon bool else @RE_empty bool
  | Fail _ _ => @RE_empty bool
  | Choice _ t1 t2 => RE_choice (RE_cons true (RE_of_tree_lib t1 P))
                               (RE_cons false (RE_of_tree_lib t2 P))
  | Fix lbl t1 => if Qeq_bool (infer_fail lbl t1) 1
                 then @RE_epsilon bool
                 else RE_seq (RE_star (RE_of_tree_fail t1 lbl)) (RE_of_tree_lib t1 P)
  end.

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
  | RE_empty _ => const None
  | RE_epsilon _ => singleton_seq []
  | RE_cons x r => option_mult MonoidList (Some [x]) ∘ RE_sequence r
  | RE_seq r1 r2 => seq_product MonoidList (RE_sequence r1) (RE_sequence r2)
  | RE_choice r1 r2 => seq_union (RE_sequence r1) (RE_sequence r2)
  | RE_star r => seq_reps MonoidList (RE_sequence r)
  end.

Definition tree_sequence_f {A : Type}
           (t : tree A) (P : A -> bool) : nat -> option (list bool) :=
  RE_sequence (RE_of_tree_f t P).

Definition tree_sequence {A : Type}
           (t : tree A) (P : A -> bool) (n : nat) : nat -> option (list bool) :=
  RE_sequence (RE_of_tree t P n).

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

Lemma seq_bijection_compose {A B : Type} (f : A -> B) (s1 s2 : nat -> A) :
  seq_bijection s1 s2 ->
  seq_bijection (f ∘ s1) (f ∘ s2).
Proof.
  intros [g [[g' [Hg'g Hgg']] Heq]].
  unfold compose.
  exists g; firstorder.
  rewrite Heq; auto.
Qed.

Lemma seq_flatten_compose {A B : Type} `{OType B}
      (f : A -> B) (rows : nat -> nat -> A) :
  equ (f ∘ seq_flatten rows) (seq_flatten (fun i j => f (rows i j))).
Proof.
  unfold compose, seq_flatten.
  split; intro j; simpl; destruct (nat_f j); reflexivity.
Qed.

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
