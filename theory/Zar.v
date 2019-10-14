(*To install ITree, do:
    opam install coq-itree *)
From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.

Section Zar.

Variable A: Type.
  
Variant zarE: Type -> Type :=
| Input : zarE bool
| Output: A -> zarE unit.

Definition Tree := itree zarE.

(*This is the "while" combinator of the ITrees paper.*)
Definition star (t : Tree bool)
  : Tree unit :=
  loop (fun l: unit + unit =>
          match l with
          | inr _ => Ret (inl tt)
          | inl _ =>
            continue <- t ;;
            if continue: bool then Ret (inl tt)         
            else Ret (inr tt)                     
          end) tt.

(*The tree that does [a] with prob. 2/3, [b] with prob. 1/3*)
Definition two_thirds (a b: A)
  : Tree unit
  := star (b1 <- trigger Input ;;
           if b1: bool then (trigger (Output a) ;; Ret false)
           else b2 <- trigger Input ;;
                if b2: bool then (trigger (Output b) ;; Ret false)
                else Ret true).

Definition abort: Tree unit := star (Ret true).

Definition flip {R} (t1 t2: Tree R)
  : Tree R
  := b <- trigger Input ;;
     if b: bool then t1 else t2.  

Definition seq {R} (t1: Tree unit) (t2: Tree R)
  : Tree R
  := t1 ;; t2.

(*TODO: Need an expression language in ite and while (t1 shouldn't be a tree)
Definition ite {R} (t1: Tree bool) (t2 t3: Tree R)
  : Tree R
  := b <- t1 ;;
     if b: bool then t2 else t3.
*)

End Zar.
