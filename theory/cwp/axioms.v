Require Import misc.

(** Limited principle of omniscience. *)
Axiom LPO : forall P : nat -> Prop, (forall n, P n \/ ~ P n) -> (exists n, P n) \/ (~ exists n, P n).

(** Strong limited principle of omniscience. *)
Axiom strong_LPO : forall {P : nat -> Prop},
    (forall n, {P n} + {~ P n}) ->
    {exists n, P n} + {~ exists n, P n}.

Ltac destruct_LPO :=
  match goal with
  | [ H: context[if strong_LPO ?y then _ else _] |- _] =>
    destruct (strong_LPO y)
  | [ |- context[if strong_LPO ?y then _ else _] ] =>
    destruct (strong_LPO y)
  end.

(** There exists a bijective pair of mappings between nat and nat*nat. *)
Axiom nat_f : nat -> nat * nat.
Axiom nat_g : nat * nat -> nat.
Axiom nat_g_f : forall n, nat_g (nat_f n) = n.
Axiom nat_f_g : forall p, nat_f (nat_g p) = p.

Lemma nat_f_inj (n m : nat) :
  nat_f n = nat_f m ->
  n = m.
Proof.
  apply (inj_spec nat_f nat_g nat_g_f).
Qed.

Lemma nat_g_inj (i j k l : nat) :
  nat_g (i, j) = nat_g (k, l) ->
  (i, j) = (k, l).
Proof.
  apply (inj_spec nat_g nat_f nat_f_g).
Qed.
