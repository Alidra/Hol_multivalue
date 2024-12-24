Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7069399 : forall {A : Type'}, forall s : A -> Prop, (@sum A s (fun n : A => real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
