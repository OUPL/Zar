(* Set Implicit Arguments. *)

(* Require Import Coq.Program.Basics. *)
(* Require Import Coq.QArith.QArith. *)

(* Require Import order. *)
(* Require Import set. *)
(* Open Scope program_scope. *)
(* Open Scope set_scope. *)

(* Class MeasurableSpace (A : Type) (sigma : pow A) : Prop := *)
(*   { sigma_A : @full A ∈ sigma *)
(*   ; sigma_complement : forall U, U ∈ sigma -> ! U ∈ sigma *)
(*   ; sigma_union : forall seq : sequence (set A), *)
(*       (forall i, seq i ∈ sigma) -> *)
(*       countable_union seq ∈ sigma *)
(*   }. *)

(* Lemma sigma_empty (A : Type) `{meas : MeasurableSpace A} : *)
(*   ∅ A ∈ sigma. *)
(* Proof. *)
(*   destruct meas as [sigma_A sigma_comp ?]. *)
(*   rewrite <- complement_full_empty; firstorder. *)
(* Qed. *)

(* Lemma sigma_intersection (A : Type) *)
(*       `{meas : MeasurableSpace A} (seq : sequence (set A)) : *)
(*   (forall i, seq i ∈ sigma) -> *)
(*   countable_intersection seq ∈ sigma. *)
(* Admitted. *)

(* Class MeasureSpace (A : Type) `{MeasurableSpace A} (mu : set A -> Q) : Prop := *)
(*   { mu_empty : mu (∅ A) == 0 *)
(*     ; mu_add : forall seq : sequence (set A), *)
(*         (forall i j, i <> j -> disjoint (seq i) (seq j)) -> *)
(*         supremum (mu (countable_union seq)) (mu ∘ seq) *)
(*   }. *)

(* Definition is_measurable {A : Type} `{MeasurableSpace A} (U : set A) := U ∈ sigma. *)

(* Definition is_measurable_fun {A B : Type} *)
(*            `{MeasurableSpace A} `{MeasurableSpace B} (f : A -> B) := *)
(*   forall V, is_measurable V -> is_measurable (preimage f V). *)

(* (** Lifting a sigma-algebra to the option type. *) *)
(* Definition option_sigma {A : Type} (sigma : pow A) (U : option A -> Prop) : Prop := *)
(*   (fun x => Some x ∈ U) ∈ sigma. *)

(* Program Instance OptionMeasurableSpace {A : Type} `{MeasurableSpace A} *)
(*   : MeasurableSpace (option_sigma sigma). *)
(* Solve Obligations with firstorder. *)
(* Next Obligation. destruct H as [? ? Hunion]; apply Hunion, H0. Qed. *)

(* Definition discrete_sigma {A : Type} : pow A := const True. *)

(* Program Instance DiscreteMeasurableSpace {A : Type} *)
(*   : MeasurableSpace (@discrete_sigma A). *)
(* Solve Obligations with firstorder. *)

(* Definition partial_fun (A B : Type) : Type := A -> option B. *)
