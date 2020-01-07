(*** Compile to finite trees first. *)
(*** NO LOOPS *)

(*To install ITree, do:
    opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.

Require Import Coq.Program.Basics.
Require Import List.
Require Import Coq.Init.Nat.
Require Import PeanoNat.
Require Import Omega.
Local Open Scope program_scope.

Import ListNotations.

Section Zar.

  Inductive val : Type -> Type :=
  | VBool : bool -> val bool.

  Definition bool_of_val (v : val bool) : bool :=
    match v with
    | VBool b => b
    end.

  Definition St : Type := nat -> val bool.
  Definition empty : St := fun _ => VBool false.
  Definition upd (x : nat) (v : val bool) (st : St) : St :=
    fun y => if Nat.eqb y x then v else st y.

  Inductive exp : Type -> Type :=
  | EVal : val bool -> exp bool
  | EVar : nat -> exp bool
  | ENot : exp bool -> exp bool
  | EAnd : exp bool -> exp bool -> exp bool
  | EOr : exp bool -> exp bool -> exp bool
  | EEq : forall {A}, exp A -> exp A -> exp bool.

  Fixpoint eval {A : Type} (e : exp A) (st : St) : val A :=
    match e with
      | EVal b => b
      | EVar x => st x
      | ENot e' =>
        match eval e' st with
        | VBool b => VBool (negb b)
        end
      | EAnd e1 e2 =>
        match (eval e1 st, eval e2 st) with
        | (VBool b1, VBool b2) => VBool (andb b1 b2)
        end
      | EOr e1 e2 =>
        match (eval e1 st, eval e2 st) with
        | (VBool b1, VBool b2) => VBool (orb b1 b2)
        end
      | EEq e1 e2 =>
        match (eval e1 st, eval e2 st) with
        | (VBool b1, VBool b2) => VBool (Bool.eqb b1 b2)
        end
    end.

  Inductive com : Type :=
  | CSkip : com
  | CAssign : forall {A}, nat -> exp A -> com
  | CSeq : com -> com -> com
  | CIte : exp bool -> com -> com -> com
  | CChoice : nat -> nat -> com -> com -> com
  | CObserve : exp bool -> com.
  (* | CWhile : Exp bool -> Com -> Com. *)

  Record prog :=
    { prog_com : com
    ; prog_query : exp bool
    }.

  Variant bitE : Type -> Type :=
  | Get : bitE bool.

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

  (* (** Using option to handle failure. *) *)
  (* Fixpoint add_to_tree_aux {A : Type} (x : A) (t : tree (unit + A)) : option (tree (unit + A)) := *)
  (*   match t with *)
  (*   | Leaf _ (inl _) => Some (Leaf _ (inr x)) *)
  (*   | Leaf _ (inr _) => None *)
  (*   | Split _ t1 t2 => *)
  (*     match add_to_tree_aux x t1 with *)
  (*     | Some t1' => Some (Split _ t1' t2) *)
  (*     | None => match add_to_tree_aux x t2 with *)
  (*              | Some t2' => Some (Split _ t1 t2') *)
  (*              | None => None *)
  (*              end *)
  (*     end *)
  (*   | Fail _ => None *)
  (*   end. *)

  Definition unit_bool_eqb (x y : unit + bool) : bool :=
    match (x, y) with
    | (inl _, inl _) => true
    | (inr b1, inr b2) => Bool.eqb b1 b2 (* XNOR *)
    | _ => false
    end.

  Lemma unit_bool_eqb_spec (x y : unit + bool) : Bool.reflect (x = y) (unit_bool_eqb x y).
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
    | 0 => Leaf _ (inl tt)
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

  Fixpoint interp (c : com) : St -> tree St :=
    match c with
    | CSkip => ret
    | CSeq c1 c2 => tree_kcomp (interp c1) (interp c2)
    | CAssign x e => fun st => match eval e st with
                           | VBool b => ret (upd x (VBool b) st)
                           end
    | CIte e c1 c2 => fun st => match eval e st with
                            | VBool true => interp c1 st
                            | VBool false => interp c2 st
                            end
    | CChoice n d c1 c2 => fun st =>
                          bind (bernoulli_tree n d)
                               (fun b => if b:bool then interp c1 st else interp c2 st)
    | CObserve e => fun st => match eval e st with
                          | VBool true => ret st
                          | VBool false => Fail _
                          end
    end.

  Definition interp_prog (p : prog) : St -> tree bool :=
    fun st => tree_fmap (fun st' => bool_of_val (eval (prog_query p) st'))
                     (interp (prog_com p) st).

End Zar.

CoFixpoint itree_of_tree_aux {A : Type} (root : tree A) (t : tree A) : itree bitE A :=
  match t with
  | Leaf _ x => ret x
  | Split _ t1 t2 =>
    b <- trigger Get ;;
      if b:bool then Tau (itree_of_tree_aux root t1) else Tau (itree_of_tree_aux root t2)
  | Fail _ => Tau (itree_of_tree_aux root root)
  end.

Definition itree_of_tree {A : Type} (t : tree A) : itree bitE A :=
  itree_of_tree_aux t t.

Definition flip (c1 c2 : com) : com := CChoice 1 2 c1 c2.

Definition choice_bool (n d x : nat) : com :=
  CChoice n d (CAssign x (EVal (VBool true))) (CAssign x (EVal (VBool false))).

Definition flip_bool (x : nat) : com :=
  choice_bool 1 2 x.

(* Goldfish-piranha program *)
Definition pir : prog :=
  {| prog_com := 
       CSeq (flip_bool 0)
            (CSeq (CAssign 1 (EVal (VBool true)))
                  (CSeq (flip (CAssign 2 (EVar 0))
                              (CAssign 2 (EVar 1)))
                        (CObserve (EEq (EVar 2) (EVal (VBool true))))))
   ; prog_query := EVar 0 |}.

Definition test1 : prog :=
  {| prog_com :=
       CSeq (flip_bool 0)
            (CSeq (flip_bool 1)
                  (CObserve (EEq (EVar 0) (EVar 1))))
   ; prog_query := EVar 0
  |}.

Definition fair_coin : prog :=
  {| prog_com := CSeq (choice_bool 1 3 0)
                      (CSeq (choice_bool 1 3 1)
                            (CObserve (ENot (EEq (EVar 0) (EVar 1)))))     
   ; prog_query := EVar 0
  |}.

(* Definition it : itree bitE bool := itree_of_tree (interp_prog pir empty). *)

Definition t : tree bool := interp_prog fair_coin empty.
Definition it : itree bitE bool := itree_of_tree t.

Extraction "extract/itree" it.
