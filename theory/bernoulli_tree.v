(** Construction of KY trees for probabilistic choice with proof of
correctness wrt a simple inference function. *)

(** Given a rational number p ∈ [0, 1], construct a boolean tree t
such that infer(t) = p (the probability of sampling true from t is
equal to p). *)

(*To install ITree, do: *)
(*     opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Init.Nat.
Require Import PeanoNat.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qfield.
Require Import Coq.micromega.Lqa.
Require Import Omega.
Local Open Scope program_scope.
Import ListNotations.


(** KY trees *)
Inductive tree A : Type :=
| Leaf : A -> tree A
| Fail : tree A
| Split : tree A -> tree A -> tree A.

Fixpoint tree_fmap {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf _ x => Leaf _ (f x)
  | Split _ t1 t2 => Split _ (tree_fmap f t1) (tree_fmap f t2)
  | Fail _ => Fail _
  end.

Fixpoint tree_join {A : Type} (t : tree (tree A)) : tree A :=
  match t with
  | Leaf _ t' => t'
  | Split _ t1 t2 => Split _ (tree_join t1) (tree_join t2)
  | Fail _ => Fail _
  end.

Definition tree_bind {A B : Type} (t : tree A) (k : A -> tree B) : tree B :=
  tree_join (tree_fmap k t).

Instance Monad_tree : Monad tree := { ret := Leaf; bind := @tree_bind }.

Definition tree_kcomp {A B C : Type} (f : A -> tree B) (g : B -> tree C) : A -> tree C :=
  fun x => bind (f x) g.


(** Bernoulli KY tree construction (for implementing probabilistic choice) *)
Definition unit_bool_eqb (x y : unit + bool) : bool :=
  match (x, y) with
  | (inl _, inl _) => true
  | (inr b1, inr b2) => Bool.eqb b1 b2 (* XNOR *)
  | _ => false
  end.

Lemma unit_bool_eqb_spec (x y : unit + bool)
  : Bool.reflect (x = y) (unit_bool_eqb x y).
Proof.
  destruct x, y.
  - destruct u, u0; left; reflexivity.
  - right; congruence.
  - right; congruence.
  - destruct b, b0; constructor; auto; congruence.
Qed.

Lemma unit_bool_eqb_refl (x : unit + bool) :
  unit_bool_eqb x x.
Proof. destruct x; auto; apply eqb_reflx. Qed.

Fixpoint unit_bool_tree_eqb (t1 : tree (unit + bool)) (t2 : tree (unit + bool)) : bool :=
  match (t1, t2) with
  | (Leaf _ b1, Leaf _ b2) => unit_bool_eqb b1 b2
  | ((Split _ t1 t2), (Split _ t1' t2')) =>
    andb (unit_bool_tree_eqb t1 t1') (unit_bool_tree_eqb t2 t2')
  | (Fail _, Fail _) => true
  | _ => false
  end.

Lemma unit_bool_tree_eqb_refl (t : tree (unit + bool)) :
  unit_bool_tree_eqb t t = true.
Proof.
  induction t; auto.
  - apply unit_bool_eqb_refl.
  - simpl; intuition.
Qed.

(** Using equality testing to check for success (SPECIALIZED TO BOOL) *)
Fixpoint add_to_tree (b : bool) (t : tree (unit + bool)) : tree (unit + bool) :=
  match t with
  | Leaf _ (inl _) => Leaf _ (inr b)
  | Leaf _ (inr _) => t
  | Split _ t1 t2 =>
    let t1' := add_to_tree b t1 in
    if unit_bool_tree_eqb t1 t1'
    then Split _ t1 (add_to_tree b t2)
    else Split _ t1' t2
  | Fail _ => Fail _
  end.

Fixpoint heightb {A : Type} (t : tree A) : nat :=
  match t with
  | Split _ t1 t2 => 1 + max (heightb t1) (heightb t2)
  | _ => 0
  end.

Inductive height {A : Type} : tree A -> nat -> Prop :=
| height_leaf : forall x, height (Leaf _ x) 0
| height_fail : height (Fail _ ) 0
| height_split : forall t1 t2 n m,
    height t1 n ->
    height t2 m ->
    height (Split _ t1 t2) (1 + max n m).

Lemma heightb_spec {A : Type} (t : tree A) :
  height t (heightb t).
Proof.
  induction t; simpl; constructor; auto.
Qed.

Fixpoint new_bool_tree (n : nat) : tree (unit + bool) :=
  match n with
  | O => Leaf _ (inl tt)
  | S n' => Split _ (new_bool_tree n') (new_bool_tree n')
  end.

Fixpoint list_tree_aux (l : list bool) (t : tree (unit + bool))
  : tree (unit + bool) :=
  match l with
  | [] => t
  | b :: bs =>
    let t' := add_to_tree b t in
    let t'' := if unit_bool_tree_eqb t t'
               then Split _ t (add_to_tree b (new_bool_tree (heightb t)))
               else t' in
    list_tree_aux bs t''
  end.

Fixpoint tie_tree (t : tree (unit + bool)) : tree bool :=
  match t with
  | Leaf _ (inl _) => Fail _
  | Leaf _ (inr b) => Leaf _ b
  | Split _ t1 t2 => Split _ (tie_tree t1) (tie_tree t2)
  | Fail _ => Fail _
  end.

Definition list_tree (l : list bool) : tree bool :=
  tie_tree (list_tree_aux l (Leaf _ (inl tt))).

Definition bernoulli_tree (n d : nat) : tree bool :=
  list_tree (repeat true n ++ repeat false (d-n)).


(** Inference on KY trees *)
Fixpoint mass {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf _ x => f x
  | Split _ t1 t2 => (1#2) * mass f t1 + (1#2) * mass f t2
  | Fail _ => 0
  end.

(** Liberal mass *)
Fixpoint lmass {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf _ x => f x
  | Split _ t1 t2 => (1#2) * mass f t1 + (1#2) * mass f t2
  | Fail _ => 1
  end.

Definition infer_ {A : Type} (f g : A -> Q) (t : tree A) : Q * Q :=
  (mass f t, mass g t).

Definition infer {A : Type} (f : A -> bool) (t : tree A) : Q :=
  let (n, d) := infer_ (fun x => if f x then 1 else 0) (fun _ => 1) t in
  n / d.

Inductive congruent {A B : Type} : tree A -> tree B -> Prop :=
| congruent_leaf_leaf : forall x y, congruent (Leaf _ x) (Leaf _ y)
| congruent_leaf_fail : forall x, congruent (Leaf _ x) (Fail _)
| congruent_fail_leaf : forall y, congruent (Fail _) (Leaf _ y)
| congruent_fail_fail : congruent (Fail _) (Fail _)
| congruent_split : forall t1 t1' t2 t2',
    congruent t1 t1' -> congruent t2 t2' ->
    congruent (Split _ t1 t2) (Split _ t1' t2').

Lemma congruent_refl {A : Type} (t : tree A) :
  congruent t t.
Proof. induction t; constructor; auto. Qed.

Lemma congruent_symm {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent t1 t2 -> congruent t2 t1.
Proof. intro H; induction H; constructor; auto. Qed.

Lemma congruent_trans {A B C : Type}
      (t1 : tree A) (t2 : tree B) (t3 : tree C) :
  congruent t1 t2 -> congruent t2 t3 -> congruent t1 t3.
Proof.
  revert t3 t1; induction t2; intros t1 t3 H0 H1;
    inversion H0; inversion H1; subst; constructor.
  - eapply IHt2_1 in H4; eauto.
  - eapply IHt2_2 in H5; eauto.
Qed.

Inductive perfect {A : Type} : tree A -> Prop :=
| perfect_leaf : forall x, perfect (Leaf _ x)
| perfect_fail : perfect (Fail _)
| perfect_split : forall t1 t2,
    congruent t1 t2 ->
    perfect t1 -> perfect t2 ->
    perfect (Split _ t1 t2).  

Lemma congruent_perfect {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent t1 t2 -> perfect t1 -> perfect t2.
Proof.
  intro H. induction H; intros; try solve [constructor].
  inversion H1; subst. constructor; auto.
  apply congruent_symm in H.
  eapply congruent_trans; eauto.
  eapply congruent_trans; eauto.
Qed.

Fixpoint countb {A : Type} (f : A -> bool) (t : tree A) : nat :=
  match t with
  | Leaf _ x => if f x then 1 else 0
  | Fail _ => 0
  | Split _ t1 t2 => countb f t1 + countb f t2
  end.

Inductive count {A : Type} (f : A -> bool) : tree A -> nat -> Prop :=
| count_leaf0 : forall x, ~ f x -> count f (Leaf _ x) 0
| count_leaf1 : forall x, f x -> count f (Leaf _ x) 1
| count_fail : count f (Fail _) 0
| count_split : forall t1 t2 n m,
    count f t1 n -> count f t2 m ->
    count f (Split _ t1 t2) (n + m).

Lemma countb_spec {A : Type} (f : A -> bool) (t : tree A) :
  count f t (countb f t).
Proof.
  induction t; simpl; try solve [constructor; auto].
  destruct (f a) eqn:H; constructor; congruence.
Qed.

Fixpoint countb_list {A : Type} (f : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + countb_list f xs
  end.

Fixpoint terminals {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf _ _ => 1
  | Fail _ => 1
  | Split _ t1 t2 => terminals t1 + terminals t2
  end.

Lemma terminals_nonzero {A : Type} (t : tree A) :
  (0 < terminals t)%nat.
Proof. induction t; simpl; omega. Qed.

Lemma perfect_congruent_terminals {A B : Type} (t1 : tree A) (t2 : tree B) :
  perfect t1 -> perfect t2 ->
  congruent t1 t2 ->
  terminals t1 = terminals t2.
Proof.
  revert t2.
  induction t1; intros t2 H0 H1 H2; inversion H2; subst; auto.
  - inversion H0; subst; inversion H1; subst; simpl; auto.
Qed.

Lemma Q_lem1 a b c d :
  (a#c) * (b#d) = (a*b#c*d).
Proof. reflexivity. Qed.

Lemma Q_lem2 a b c :
  (a#c) + (b#c) == (a+b#c).
Proof.
  rewrite 3!Qmake_Qdiv.
  rewrite inject_Z_plus. field.
  admit.
Admitted.

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
  assert (H1: (c + c = 2 * c)%nat). omega.
  rewrite H1. clear H1.
  rewrite Nat2Pos.inj_mul; auto.
  apply Q_lem2.
Qed.

Lemma count_mass {A : Type} (t : tree A) (f : A -> bool) (n : nat) :
  perfect t ->
  countb f t = n ->
  mass (fun x => if f x then 1 else 0) t == (Z.of_nat n # Pos.of_nat (terminals t)).
Proof.
  revert n.
  induction t; intros n Hp Hc.
  - simpl in *; destruct (f a); subst; field.
  - simpl in *; subst; field.
  - simpl in *.
    inversion Hp; subst.
    specialize (IHt1 (countb f t1) H2 eq_refl).
    specialize (IHt2 (countb f t2) H3 eq_refl).
    rewrite IHt1, IHt2. clear IHt1 IHt2.
    apply (@perfect_congruent_terminals _ _ t1 t2) in H2; auto.
    rewrite H2.
    clear Hp H1 H2 H3.
    apply Q_lem3.
    generalize (terminals_nonzero t2); omega.
Qed.

Lemma new_bool_tree_height (n : nat) :
  heightb (new_bool_tree n) = n.
Proof.
  induction n; simpl; auto.
  - rewrite IHn, Nat.max_id; reflexivity.
Qed.

Lemma new_bool_tree_perfect (n : nat) :
  perfect (new_bool_tree n).
Proof. induction n; simpl; constructor; auto; apply congruent_refl. Qed.

Lemma congruent_heightb {A B : Type} (t1 : tree A) (t2 : tree B) :
  congruent t1 t2 ->
  heightb t1 = heightb t2.
Proof.
  intro H; induction H; auto; simpl;
    rewrite IHcongruent1, IHcongruent2; reflexivity.
Qed.

Lemma perfect_height_congruent {A B : Type} (t1 : tree A) (t2 : tree B) :
  perfect t1 -> perfect t2 ->
  heightb t1 = heightb t2 ->
  congruent t1 t2.
Proof.
  revert t2. induction t1; intros t2 Hp1 Hp2 Hh.
  - destruct t2; try constructor; inversion Hh.
  - destruct t2; try constructor; inversion Hh.
  - destruct t2.
    + inversion Hh.
    + inversion Hh.
    + simpl in *.
      inversion Hp1. inversion Hp2. subst.
      apply congruent_heightb in H1.
      apply congruent_heightb in H6.
      rewrite H1, H6 in *.
      rewrite 2!Nat.max_id in *.
      inversion Hh.
      constructor.
      * apply IHt1_1; firstorder.
      * apply IHt1_2; firstorder.
Qed.

Lemma perfect_new_tree_congruent {A : Type} (t : tree A) :
  perfect t ->
  congruent t (new_bool_tree (heightb t)).
Proof.
  intro Hp.
  apply perfect_height_congruent; auto.
  apply new_bool_tree_perfect.
  rewrite new_bool_tree_height; reflexivity.
Qed.

Lemma add_to_tree_congruent (b : bool) (t : tree (unit + bool)) :
  congruent t (add_to_tree b t).
Proof.
  induction t; simpl; try destruct a; try constructor.
  destruct (unit_bool_tree_eqb t1 (add_to_tree b t1));
    constructor; auto; apply congruent_refl.
Qed.

Lemma list_tree_aux_perfect (l : list bool) (t : tree (unit + bool)) :
  perfect t ->
  perfect (list_tree_aux l t).
Proof.
  revert t. induction l; auto.
  - intros t Hp. simpl.
    apply IHl.
    destruct (unit_bool_tree_eqb t (add_to_tree a t)).
    + assert (H0: congruent t (add_to_tree a (new_bool_tree (heightb t)))).
      { apply congruent_trans with (t2:=new_bool_tree (heightb t)).
        apply perfect_new_tree_congruent; auto.
        apply add_to_tree_congruent. }
      constructor; auto.
      * eapply congruent_perfect; eauto.
    + eapply congruent_perfect; eauto.
      apply add_to_tree_congruent.
Qed.

Lemma tie_tree_shape (t : tree (unit + bool)) :
  congruent t (tie_tree t).
Proof. induction t; try destruct a; constructor; auto. Qed.

Lemma bernoulli_perfect (n d : nat) :
  perfect (bernoulli_tree n d).
Proof.
  unfold bernoulli_tree.
  unfold list_tree.
  eapply congruent_perfect.
  apply tie_tree_shape.
  apply list_tree_aux_perfect.
  constructor.
Qed.

Lemma countb_tie_tree (f : bool -> bool) (t : tree (unit + bool)) :
  countb f (tie_tree t) = countb (fun x => match x with
                                        | inl _ => false
                                        | inr x' => f x'
                                        end) t.
Proof. induction t; simpl; auto; destruct a; auto. Qed.

Lemma add_to_tree_new_tree a n :
  unit_bool_tree_eqb (new_bool_tree n) (add_to_tree a (new_bool_tree n)) = false.
Proof.
  induction n; auto.
  simpl; rewrite 2!IHn; auto.
Qed.

Lemma countb_add_to_new_tree (f : bool -> bool) a n :
  countb (fun x : unit + bool => match x with
                           | inl _ => false
                           | inr x' => f x'
                           end) (add_to_tree a (new_bool_tree n)) =
  ((if f a then 1 else 0) +
   countb (fun x : unit + bool => match x with
                            | inl _ => false
                            | inr x' => f x'
                            end) (new_bool_tree n))%nat.
Proof.
  induction n; auto.
  simpl; rewrite add_to_tree_new_tree; simpl; rewrite IHn; omega.
Qed.

Lemma countb_new_tree (f : bool -> bool) n :
  countb (fun x : unit + bool => match x with
                           | inl _ => false
                           | inr x' => f x'
                           end) (new_bool_tree n) = O.
Proof. induction n; auto; simpl; rewrite IHn; auto. Qed.

Lemma countb_list_tree_aux f l t :
  countb (fun x => match x with
                | inl _ => false
                | inr x' => f x'
                end) (list_tree_aux l t) =
  (countb_list f l + countb (fun x => match x with
                                   | inl _ => false
                                   | inr x' => f x'
                                   end) t)%nat.
Proof.
  revert f t. induction l; intros f t; auto.
  simpl. destruct (unit_bool_tree_eqb t (add_to_tree a t)) eqn:H0.
  - rewrite IHl. simpl. clear IHl.
    rewrite countb_add_to_new_tree.
    rewrite countb_new_tree.
    omega.
  - rewrite IHl. clear IHl.
    cut ((countb (fun x : unit + bool => match x with
                                   | inl _ => false
                                   | inr x' => f x'
                                   end) (add_to_tree a t))%nat =
         ((if f a then 1 else 0) +
          countb (fun x : unit + bool => match x with
                                   | inl _ => false
                                   | inr x' => f x'
                                   end) t)%nat); try omega.
    (* NOTE: countb, add_to_tree *)
    induction t; simpl in *; try congruence.
    + destruct a0; simpl; try omega.
      unfold unit_bool_eqb in H0. rewrite eqb_reflx in H0. congruence.
    + destruct (unit_bool_tree_eqb t1 (add_to_tree a t1)) eqn:H1.
      * rewrite unit_bool_tree_eqb_refl in H0.
        simpl in H0.
        apply IHt2 in H0. clear IHt1 IHt2.
        simpl; omega.
      * specialize (IHt1 eq_refl). simpl; omega.
Qed.

Lemma list_tree_count (l : list bool) (f : bool -> bool) :
  countb f (list_tree l) = countb_list f l.
Proof.
  unfold list_tree. simpl.

  revert f. induction l; intro f; auto.
  simpl. rewrite <- IHl.
  rewrite 2!countb_tie_tree.
  rewrite 2!countb_list_tree_aux. simpl.
  destruct (f a); auto.
Qed.

Lemma countb_list_app {A : Type} (f : A -> bool) (l1 l2 : list A) :
  countb_list f (l1 ++ l2) = (countb_list f l1 + countb_list f l2)%nat.
Proof. induction l1; auto; simpl; rewrite IHl1; omega. Qed.

Lemma count_true_n (n : nat) :
  countb_list id (repeat true n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma count_false_0 (n : nat) :
  countb_list id (repeat false n) = O.
Proof. induction n; simpl; auto. Qed.

Lemma bernoulli_count_n (n d : nat) :
  countb id (bernoulli_tree n d) = n.
Proof.
  unfold bernoulli_tree.
  rewrite list_tree_count.
  rewrite countb_list_app.
  rewrite count_true_n.
  rewrite count_false_0.
  apply Nat.add_0_r.
Qed.

Lemma list_tree_count_mass (l : list bool) :
  countb (fun _ => true) (list_tree l) = length l.
Proof.
  unfold list_tree. rewrite countb_tie_tree.
  rewrite countb_list_tree_aux. simpl. rewrite Nat.add_0_r.
  induction l; auto; simpl; rewrite IHl; auto.
Qed.

Lemma bernoulli_count_d (n d : nat) :
  (n <= d)%nat ->
  countb (fun _ => true) (bernoulli_tree n d) = d.
Proof.
  intros ?; unfold bernoulli_tree.
  rewrite list_tree_count_mass, app_length, 2!repeat_length; omega.
Qed.

Lemma bernoulli_tree_indicator_mass (n d : nat) :
  mass (fun b => if b:bool then 1 else 0) (bernoulli_tree n d) ==
  (Z.of_nat n # Pos.of_nat (terminals (bernoulli_tree n d))).
Proof.
  apply count_mass. apply bernoulli_perfect. apply bernoulli_count_n.
Qed.

Lemma bernoulli_tree_const_mass (n d : nat) :
  (n <= d)%nat ->
  mass (fun _ => 1) (bernoulli_tree n d) ==
  (Z.of_nat d # Pos.of_nat (terminals (bernoulli_tree n d))).
Proof.
  intro H.
  exact (@count_mass bool (bernoulli_tree n d) (fun _ => true) d
                     (bernoulli_perfect n d) (bernoulli_count_d n d H)).
Qed.

Lemma Q_lem4 (a b c : Q) :
  0 < b -> 0 < c ->
  (a / c) / (b / c) == a / b.
Proof. intros H0 H1; field; split; nra. Qed.

(* Maybe useful for below *)
(* Require Import Coq.PArith.BinPos. *)

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

    Eval compute in (Z.pos (Pos.of_nat 2)).
    Eval compute in (Z.of_nat 2).

    (* ugh *)
    admit.
Admitted.

Lemma bernoulli_tree_spec (n d : nat) :
  (0 < d)%nat -> (n <= d)%nat ->
  infer id (bernoulli_tree n d) == Z.of_nat n # Pos.of_nat d.
Proof.
  intros H0 H1. unfold infer.
  simpl. unfold id.
  rewrite bernoulli_tree_indicator_mass.
  rewrite bernoulli_tree_const_mass; auto.
  apply Q_lem5; auto.
Qed.
