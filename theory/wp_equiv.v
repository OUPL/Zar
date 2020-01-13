(*** Equivalence of abstract tree compilation/inference with wp semantics for unconditioned loop-free programs. *)

(*To install ITree, do:
    opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.
Import ITreeNotations.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Init.Nat.
Require Import PeanoNat.
Require Import Coq.QArith.QArith_base.
Require Import Omega.
Local Open Scope program_scope.

Import ListNotations.

Definition val := bool.
Definition St : Type := nat -> val.
Definition empty : St := fun _ => false.
Definition upd (x : nat) (v : val) (st : St) : St :=
  fun y => if Nat.eqb y x then v else st y.
Definition exp := St -> val.

Inductive com : Type :=
| CSkip : com
| CAssign : nat -> exp -> com
| CSeq : com -> com -> com
| CIte : exp -> com -> com -> com
| CChoice : Q -> com -> com -> com.

Record prog :=
  { prog_com : com
  ; prog_query : exp
  }.

Inductive tree A : Type :=
| Leaf : A -> tree A
| Choice : Q -> tree A -> tree A -> tree A.

Fixpoint tree_fmap {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf _ x => Leaf _ (f x)
  | Choice _ p t1 t2 => Choice _ p (tree_fmap f t1) (tree_fmap f t2)
  end.

Fixpoint tree_join {A : Type} (t : tree (tree A)) : tree A :=
  match t with
  | Leaf _ t' => t'
  | Choice _ p t1 t2 => Choice _ p (tree_join t1) (tree_join t2)
  end.

Definition tree_bind {A B : Type} (t : tree A) (k : A -> tree B) : tree B :=
  tree_join (tree_fmap k t).

Instance Monad_tree : Monad tree := { ret := Leaf; bind := @tree_bind }.

Definition tree_kcomp {A B C : Type} (f : A -> tree B) (g : B -> tree C) : A -> tree C :=
  fun x => bind (f x) g.

Fixpoint interp (c : com) : St -> tree St :=
  match c with
  | CSkip => ret
  | CSeq c1 c2 => tree_kcomp (interp c1) (interp c2)
  | CAssign x e => fun st => ret (upd x (e st) st)
  | CIte e c1 c2 => fun st => interp (if (e st) then c1 else c2) st
  | CChoice p c1 c2 => fun st => Choice _ p (interp c1 st) (interp c2 st)
  end.

Definition interp_prog (p : prog) : St -> tree bool :=
  fun st => tree_fmap (prog_query p) (interp (prog_com p) st).

Fixpoint infer {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf _ x => f x
  | Choice _ p t1 t2 => p * infer f t1 + (1-p) * infer f t2
  end.

Fixpoint wp (c : com) (f : St -> Q) (st : St) : Q :=
  match c with
  | CSkip => f st
  | CSeq c1 c2 => wp c1 (wp c2 f) st
  | CAssign x e => f (upd x (e st) st)
  | CIte e c1 c2 => if e st then wp c1 f st else wp c2 f st
  | CChoice p c1 c2 => p * wp c1 f st + (1-p) * wp c2 f st
  end.

Inductive wp_ : com -> (St -> Q) -> (St -> Q) -> Prop :=
| wp_skip : forall f, wp_ CSkip f f
| wp_seq : forall c1 c2 f f' f'',
    wp_ c2 f f' ->
    wp_ c1 f' f'' ->
    wp_ (CSeq c1 c2) f f''
| wp_assign : forall x e f,
    wp_ (CAssign x e) f (fun st => f (upd x (e st) st))
| wp_ite : forall e c1 c2 f g h,
    wp_ c1 f g ->
    wp_ c2 f h ->
    wp_ (CIte e c1 c2) f (fun st => if e st then g st else h st)
| wp_choice : forall p c1 c2 f g h,
    wp_ c1 f g ->
    wp_ c2 f h ->
    wp_ (CChoice p c1 c2) f (fun st => p * g st + (1-p) * h st).

(** The functional and relational versions of wp agree. *)
Lemma wp_spec (c : com) (f : St -> Q) :
  wp_ c f (wp c f).
Proof.
  revert f.
  induction c; try solve [intros; simpl; constructor; auto]; intro f.
  - econstructor.
    + apply IHc2.
    + apply IHc1.
Qed.    

Theorem equiv (c : com) (f : St -> Q) (s : St) :
  wp c f s = infer f (interp c s).
Proof.
  revert f s.
  induction c; intros f s; auto; simpl.
  - rewrite IHc1; unfold tree_kcomp.
    clear IHc1; revert f; induction (interp c1 s); intro f; simpl.
    + unfold tree_bind; simpl; apply IHc2.
    + rewrite IHt1, IHt2; reflexivity.
  - destruct (e s); auto.
  - rewrite IHc1, IHc2; auto.
Qed.
