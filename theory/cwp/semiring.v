(* Set Implicit Arguments. *)
Require Import Coq.Program.Basics.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

Require Import order.

(* Class CommutativeMonoid (A : Type) `{Monoid A} : Type := *)
(*   { monoid_comm : forall x y, monoid_plus x y = *)
(*   }. *)

(* Our infinite sequences are almost a kleene algebra except for
   idempotence of union. We don't have [a + a === a] because our
   equivalence relation is duplicate-sensitive. We could possibly
   refactor to be duplicate-insensitive but it's not necessary for any
   of our purposes. We can still possibly use an analogue of the order
   relation and kleene star axioms? *)

Class Semiring (A : Type) `{Equivalence A} : Type :=
  { sr_plus : A -> A -> A
  ; sr_zero : A
  ; sr_mult : A -> A -> A
  ; sr_one : A
  (** sr_plus is a commutative monoid with identity element sr_zero. *)
  ; sr_plus_assoc : forall a b c, sr_plus (sr_plus a b) c === sr_plus a (sr_plus b c)
  ; sr_plus_zero_l : forall a, sr_plus sr_zero a === a
  ; sr_plus_zero_r : forall a, sr_plus a sr_zero === a
  ; sr_plus_comm : forall a b, sr_plus a b === sr_plus b a
  (** sr_mult is a monoid with identity element sr_one. *)
  ; sr_mult_assoc : forall a b c, sr_mult (sr_mult a b) c === sr_mult a (sr_mult b c)
  ; sr_mult_one_l : forall a, sr_mult sr_one a === a
  ; sr_mult_one_r : forall a, sr_mult a sr_one === a
  (** Multiplication distributes over addition. *)
  ; sr_distr_l : forall a b c, sr_mult a (sr_plus b c) === sr_plus (sr_mult a b) (sr_mult a c)
  ; sr_distr_r : forall a b c, sr_mult (sr_plus a b) c === sr_plus (sr_mult a c) (sr_mult b c)
  (** Multiplication by zero annihilates A. *)
  ; sr_anni_l : forall a, sr_mult sr_zero a === sr_zero
  ; sr_anni_r : forall a, sr_mult a sr_zero === sr_zero
  ; sr_plus_proper : Proper (equiv ==> equiv ==> equiv) sr_plus
  ; sr_mult_proper : Proper (equiv ==> equiv ==> equiv) sr_mult
  }.

Section derived_ops.
  Context {A : Type} `{Semiring A}.

  Definition nth_prod (x y : A) (n : nat) : A :=
    Nat.iter n (fun x' => sr_mult x' y) x.

  Definition nth_rep (x : A) (n : nat) : A :=
    nth_prod sr_one x n.

  Fixpoint nth_sum (f : nat -> A) (n : nat) :=
    match n with
    | O => f O
    | S n' => sr_plus (nth_sum f n') (f n)
  end.

  Definition big_sum `{OType A} (sup : A) (f : nat -> A) : Prop :=
    supremum sup (nth_sum f).
End derived_ops.

(* Section semiring_lemmas. *)
(*   Context {A : Type} `{Semiring A}. *)
  
(*   (* Lemma nth_rep_zero (n : nat) : *) *)
(*   (*   nth_rep sr_zero n === sr_one. *) *)
(*   (* Proof. *) *)
(*   (*   induction n. *) *)
(*   (*   - reflexivity. *) *)
(*   (*   - simpl. destruct H0. rewrite IHn. *) *)
(*   (*     rewrite sr_mult_one_l0 *) *)
      
    
(* End semiring_lemmas. *)
