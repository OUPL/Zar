(*** BACK TO TREE TRANSFORMERS *)

(*** Experimenting with itrees *)
(** Mapping directly from a deep embedding of program syntax to
    interaction trees, probably not in the most sane way possible. *)

(*To install ITree, do:
    opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.

Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Section Zar.

  Inductive Val : Type -> Type :=
  | VBool : bool -> Val bool.

  Definition bool_of_Val (v : Val bool) : bool :=
    match v with
    | VBool b => b
    end.

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

  Inductive Com : Type :=
  | CSkip : Com
  | CAssign : forall {A}, nat -> Exp A -> Com
  | CSeq : Com -> Com -> Com
  | CIte : Exp bool -> Com -> Com -> Com
  | CFlip : Com -> Com -> Com
  | CObserve : Exp bool -> Com
  | CWhile : Exp bool -> Com -> Com.

  Record Prog :=
    { prog_com : Com
    ; prog_query : Exp bool
    }.

  Variant bitE : Type -> Type :=
  | Get : bitE bool.

  (* Axiom nil : forall {A B E}, ktree E A B. *)

  (* Kleisli lifting into the itree monad. *)
  Definition klift {A B : Type} {E : Type -> Type}
    : (A -> itree E B) -> itree E A -> itree E B := ITree.bind'.

  Fixpoint interp (c : Com) : itree bitE St -> itree bitE St :=
    match c with
    | CSkip => id
    | CSeq c1 c2 => interp c2 ∘ interp c1
    | CAssign x e => klift (fun st => match eval e st with
                                  | VBool b => ret (upd x (VBool b) st)
                                  end)
    | CIte e c1 c2 => klift (fun st => match eval e st with
                                   | VBool true => interp c1 (ret st)
                                   | VBool false => interp c2 (ret st)
                                   end)
    | CFlip c1 c2 => fun st => b <- trigger Get ;;
                             interp (if b:bool then c1 else c2) st
    | CWhile e body =>
      klift (Basics.iter (fun st =>
                            ITree.map (fun st' =>
                                         match eval e st' with
                                         | VBool true => inr st'
                                         | VBool false => inl st
                                         end) (interp body (ret st))))
    | CObserve e => fun t => bind t (fun st => match eval e st with
                                        | VBool true => ret st
                                        | VBool false => t
                                        end)
    end.

  Definition interp_prog (p : Prog) : itree bitE bool :=
    ITree.map (bool_of_Val ∘ eval (prog_query p)) (interp (prog_com p) (ret empty)).

End Zar.

(* Goldfish-piranha program *)
Definition pir : Prog :=
  {| prog_com := 
       CSeq (CFlip (CAssign 0 (EVal (VBool false)))
                   (CAssign 0 (EVal (VBool true))))
            (CSeq (CAssign 1 (EVal (VBool true)))
                  (CSeq (CFlip (CAssign 2 (EVar 0))
                               (CAssign 2 (EVar 1)))
                        (CObserve (EEq (EVar 2) (EVal (VBool true))))))
   ; prog_query := EVar 0 |}.

Definition pir_itree : itree bitE bool := interp_prog pir.

Extraction "extract/itree" pir_itree.
