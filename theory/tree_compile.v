(*** Compiling abstract trees to KY trees. *)

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

(** Abstract trees (with probabilistic choice nodes) *)
Inductive atree A : Type :=
| ALeaf : A -> atree A
| AChoice : Q -> atree A -> atree A -> atree A
| AFail : atree A.

Fixpoint atree_fmap {A B : Type} (f : A -> B) (t : atree A) : atree B :=
  match t with
  | ALeaf _ x => ALeaf _ (f x)
  | AChoice _ p t1 t2 => AChoice _ p (atree_fmap f t1) (atree_fmap f t2)
  | AFail _ => AFail _
  end.

Fixpoint atree_join {A : Type} (t : atree (atree A)) : atree A :=
  match t with
  | ALeaf _ t' => t'
  | AChoice _ p t1 t2 => AChoice _ p (atree_join t1) (atree_join t2)
  | AFail _ => AFail _
  end.

Definition atree_bind {A B : Type} (t : atree A) (k : A -> atree B) : atree B :=
  atree_join (atree_fmap k t).

Instance Monad_atree : Monad atree := { ret := ALeaf; bind := @atree_bind }.

Definition atree_kcomp {A B C : Type} (f : A -> atree B) (g : B -> atree C) : A -> atree C :=
  fun x => bind (f x) g.


(** Interpreting commands using abstract trees *)
Fixpoint interp (c : com) : St -> atree St :=
  match c with
  | CSkip => ret
  | CSeq c1 c2 => atree_kcomp (interp c1) (interp c2)
  | CAssign x e => fun st => ret (upd x (e st) st)
  | CIte e c1 c2 => fun st => interp (if (e st) then c1 else c2) st
  | CChoice p c1 c2 => fun st => AChoice _ p (interp c1 st) (interp c2 st)
  | CObserve e => fun st => if e st then ret st else AFail _
  end.


(** Bit-by-bit KY trees *)
Inductive tree A : Type :=
| Leaf : A -> tree A
| Split : tree A -> tree A -> tree A
| Fail : tree A.

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

Fixpoint unit_bool_tree_eqb (t1 : tree (unit + bool)) (t2 : tree (unit + bool)) : bool :=
  match (t1, t2) with
  | (Leaf _ b1, Leaf _ b2) => unit_bool_eqb b1 b2
  | ((Split _ t1 t2), (Split _ t1' t2')) =>
    andb (unit_bool_tree_eqb t1 t1') (unit_bool_tree_eqb t2 t2')
  | (Fail _, Fail _) => true
  | _ => false
  end.

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

Fixpoint tree_depth {A : Type} (t : tree A) : nat :=
  match t with
  | Split _ t1 t2 => 1 + tree_depth t1 + tree_depth t2
  | _ => 0
  end.

Fixpoint new_bool_tree (n : nat) : tree (unit + bool) :=
  match n with
  | O => Leaf _ (inl tt)
  | S n' => Split _ (new_bool_tree n') (new_bool_tree n')
  end.

Fixpoint list_tree_aux (l : list bool) (t : tree (unit + bool)) : tree (unit + bool) :=
  match l with
  | [] => t
  | b :: bs =>
    let t' := add_to_tree b t in
    let t'' := if unit_bool_tree_eqb t t'
               then Split _ t (add_to_tree b (new_bool_tree (tree_depth t)))
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

Definition interp_prog (p : prog) : St -> atree bool :=
  fun st => atree_fmap (prog_query p) (interp (prog_com p) st).


(** Inference on abstract trees *)
Fixpoint adensity {A : Type} (f : A -> Q) (t : atree A) : Q :=
  match t with
  | ALeaf _ x => f x
  | AChoice _ p t1 t2 => p * adensity f t1 + (1-p) * adensity f t2
  | AFail _ => 0
  end.

Definition ainfer_ {A : Type} (f g : A -> Q) (t : atree A) : Q * Q :=
  (adensity f t, adensity g t).

Definition ainfer {A : Type} (f : A -> bool) (t : atree A) : Q :=
  let (n, d) := ainfer_ (fun x => if f x then 1 else 0) (fun _ => 1) t in
  n / d.


(** Inference on KY trees *)
Fixpoint density {A : Type} (f : A -> Q) (t : tree A) : Q :=
  match t with
  | Leaf _ x => f x
  | Split _ t1 t2 => (1#2) * density f t1 + (1#2) * density f t2
  | Fail _ => 0
  end.


(** Compiling abstract trees to KY trees *)
Fixpoint compile_atree {A : Type} (t : atree A) : tree A :=
  match t with
  | ALeaf _ x => Leaf _ x
  | AFail _ => Fail _
  | AChoice _ (Qmake n d) t1 t2 =>
    bind (bernoulli_tree (Z.to_nat n) (Pos.to_nat d))
         (fun b => if b:bool then compile_atree t1 else compile_atree t2)
  end.


Lemma bernoulli_tree_spec (n d : nat) :
  density (fun b => if b:bool then 1 else 0) (bernoulli_tree n d) =
  Z.of_nat n # Pos.of_nat d.
Proof.
Admitted.

(** Compilation correctness theorem *)
Theorem density_equiv {A : Type} (f : A -> Q) (t : atree A) :
  adensity f t = density f (compile_atree t).
Proof.
  revert f. induction t; intro f; auto.
  simpl. destruct q as [n d].
  rewrite IHt1, IHt2.
  admit. (* the hard part *)
Admitted.
