(*** Equivalence of abstract tree compilation/inference with cwp semantics for conditioned loop-free programs. *)

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
| CChoice : Q -> com -> com -> com
| CObserve : exp -> com.

Record prog :=
  { prog_com : com
  ; prog_query : exp
  }.

Inductive tree A : Type :=
| Leaf : A -> tree A
| Choice : Q -> tree A -> tree A -> tree A
| Fail : tree A.

Fixpoint tree_fmap {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf _ x => Leaf _ (f x)
  | Choice _ p t1 t2 => Choice _ p (tree_fmap f t1) (tree_fmap f t2)
  | Fail _ => Fail _
  end.

Fixpoint tree_join {A : Type} (t : tree (tree A)) : tree A :=
  match t with
  | Leaf _ t' => t'
  | Choice _ p t1 t2 => Choice _ p (tree_join t1) (tree_join t2)
  | Fail _ => Fail _
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
  | CObserve e => fun st => if e st then ret st else Fail _
  end.

Definition interp_prog (p : prog) : St -> tree bool :=
  fun st => tree_fmap (prog_query p) (interp (prog_com p) st).

Fixpoint density {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf _ x => f x
  | Choice _ p t1 t2 => p * density f t1 + (1-p) * density f t2
  | Fail _ => 0
  end.

Definition infer_ {A : Type} (f g : A -> Q) (t : tree A) : Q * Q :=
  (density f t, density g t).

Definition infer {A : Type} (f : A -> bool) (t : tree A) : Q :=
  let (n, d) := infer_ (fun x => if f x then 1 else 0) (fun _ => 1) t in
  n / d.

Fixpoint cwp_ (c : com) (f : St -> Q) (g : St -> Q) (st : St) : Q * Q :=
  match c with
  | CSkip => (f st, g st)
  | CSeq c1 c2 =>
    let f' := fun s => fst (cwp_ c2 f g s) in
    let g' := fun s => snd (cwp_ c2 f g s) in
    cwp_ c1 f' g' st
  | CAssign x e => (f (upd x (e st) st), g (upd x (e st) st))
  | CIte e c1 c2 => cwp_ (if (e st) then c1 else c2) f g st
  | CChoice p c1 c2 =>
    (p * fst (cwp_ c1 f g st) + (1-p) * fst (cwp_ c2 f g st),
     p * snd (cwp_ c1 f g st) + (1-p) * snd (cwp_ c2 f g st))
  | CObserve e => if e st then (f st, g st) else (0, 0)
  end.

Definition cwp (c : com) (f : St -> Q) (st : St) : Q :=
  let (n, d) := cwp_ c f (fun _ => 1) st in
  n / d.

Theorem equiv_ (c : com) (f g : St -> Q) (s : St) :
  cwp_ c f g s = infer_ f g (interp c s).
Proof.
  revert f g s.
  induction c; intros f g s; auto.
  - simpl; rewrite IHc1; clear IHc1; unfold tree_kcomp; simpl.
    induction (interp c1 s); auto.
    + unfold infer_; simpl; unfold tree_bind; simpl.
      rewrite IHc2; reflexivity.
    + unfold tree_bind; simpl; unfold infer_ in *; simpl in *.
      inversion IHt1; inversion IHt2.
      rewrite H0, H1, H2, H3; reflexivity.
  - simpl; destruct (e s).
    + rewrite IHc1; reflexivity.
    + rewrite IHc2; reflexivity.
  - unfold infer; simpl; rewrite IHc1, IHc2; reflexivity.
  - simpl; destruct (e s); reflexivity.
Qed.

Theorem equiv (c : com) (f : St -> bool) (s : St) :
  cwp c (fun x => if f x then 1 else 0) s = infer f (interp c s).
Proof.
  unfold cwp, infer; rewrite equiv_; reflexivity.
Qed.
