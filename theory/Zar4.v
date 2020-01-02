(*** Experimenting with itrees *)
(** Mapping directly from a deep embedding of program syntax to
    interaction trees, probably not in the most sane way possible. *)

(*To install ITree, do:
    opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.

Section Zar.

  Inductive Val : Type -> Type :=
  | VBool : bool -> Val bool.

  Definition St : Type := nat -> Val bool.
  Definition empty : St := fun _ => VBool false.

  Definition upd (x : nat) (v : Val bool) (st : St) : St :=
    fun y => if Nat.eqb y x then v else st y.
    
  Inductive Exp : Type -> Type :=
  | EVal : Val bool -> Exp bool
  | EVar : nat -> Exp bool
  | ENot : Exp bool -> Exp bool
  | EAnd : Exp bool -> Exp bool -> Exp bool
  | EOr : Exp bool -> Exp bool -> Exp bool
  | EEq : forall {A}, Exp A -> Exp A -> Exp bool.

  Fixpoint eval {A : Type} (e : Exp A) (st : St) : Val A :=
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

  (* TODO: maybe get rid of the type indices, make all commands
     interpreted as ktree bitE St St, and say a program is a command
     together with a query expression of type St -> bool. *)
  Inductive Com : Type -> Type :=
  | CSkip : Com St
  | CAssign : forall {A}, nat -> Exp A -> Com St
  | CSeq : forall {A}, Com St -> Com A -> Com A
  | CIte : forall {A}, Exp bool -> Com A -> Com A -> Com A
  | CFlip : forall {A}, Com A -> Com A -> Com A
  | CObserve : Exp bool -> Com St
  | CWhile : Exp bool -> Com St -> Com St
  | CReturn : Exp bool -> Com bool.
  (* | CAbort : Com void. *)

  Variant bitE : Type -> Type :=
  | Get : bitE bool.

  (* Axiom nil : forall {A}, ktree bitE St A. *)

  (* Variant treeE : Type -> Type := *)
  (* | Tree : treeE (itree (treeE +' bitE) St). *)

  (* This was causing the OCaml compiler to stack overflow. *)
  (* Definition diverge : itree bitE void := *)
  (*   Basics.iter (fun _ : unit => ret (inl tt)) tt. *)

  (* Composition of ktrees that may fail (if the first fails, ignore
     the second ktree and propagate the failure). *)
  Definition cat_reject {A B C D : Type} {E : Type -> Type} (k1 : ktree E A (D + B))
             (k2 : ktree E B (D + C)) : ktree E A (D + C) :=
    fun a => bind (k1 a) (fun x => match x with
                             | inl d => ret (inl d)
                             | inr b => k2 b
                             end).

  (* Interpret commands as ktrees that may fail due to observation
     failure. *)
  Fixpoint interp_reject {A : Type} (c : Com A) : ktree bitE St (St + A) :=
    match c with
    | CSkip => fun st => ret (inr st)
    | CSeq c1 c2 => cat_reject (interp_reject c1) (interp_reject c2)
    | CAssign x e => fun st => match eval e st with
                           | VBool b => ret (inr (upd x (VBool b) st))
                           end
    | CIte e c1 c2 => fun st => match eval e st with
                            | VBool true => interp_reject c1 st
                            | VBool false => interp_reject c2 st
                            end
    | CFlip c1 c2 => fun st => b <- trigger Get ;;
                             interp_reject (if negb b:bool then c1 else c2) st
    | CObserve e => fun st => match eval e st with
                          | VBool true => ret (inr st)
                          | VBool false => ret (inl empty)
                          end
    | CWhile e body =>
      Basics.iter (fun st => ITree.map (fun x => match x with
                                           | inl st' => inr (inl st')
                                           | inr st' =>
                                             match eval e st' with
                                             | VBool true => inr (inr st')
                                             | VBool false => inl st
                                             end
                                           end) (interp_reject body st))
    | CReturn e => fun st => match eval e st with
                         | VBool b => ret (inr b)
                         end
    end.

  (* Iterate until a sample is successfully produced. *)
  Definition interp {A : Type} (c : Com A) : ktree bitE St A :=
    iter (interp_reject c).

End Zar.

(* Goldfish-piranha program *)
Definition pir : Com bool :=
  CSeq (CFlip (CAssign 0 (EVal (VBool false)))
              (CAssign 0 (EVal (VBool true))))
       (CSeq (CAssign 1 (EVal (VBool true)))
             (CSeq (CFlip (CAssign 2 (EVar 0))
                          (CAssign 2 (EVar 1)))
                   (CSeq (CObserve (EEq (EVar 2) (EVal (VBool true))))
                         (CReturn (EVar 0))))).

Definition pir_ktree : ktree bitE St bool := interp pir.

Extraction "extract/ktree" pir_ktree.
